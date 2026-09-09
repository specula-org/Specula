"""Continue one incremental conversation across explicitly requested compactions."""

from __future__ import annotations

import json
import os
import secrets
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from specula.adapters.utils.usage import UsageTotals, accumulate_usage
from specula.context_control import MCP_ENV, PYTHON_ENV, REQUEST_ENV, TOKEN_ENV, YIELD_PREFIX, mcp_config, write_json
from specula.resource_summary import UsageRecord, _claude_usage, _normalized_usage, _parse_usage_file
from specula.resumelib import inherited_run_lock_fds

ROOT = Path(__file__).resolve().parents[2]


def tool_environment(directory: Path, work: Path, python: Path, agent: str = "") -> dict[str, str]:
    env = os.environ.copy()
    env.update(
        {
            REQUEST_ENV: str(directory / "request.json"),
            TOKEN_ENV: secrets.token_hex(16),
            PYTHON_ENV: str(python),
            "SPECULA_WORK_DIR": str(work),
            "SPECULA_CONTEXT_AGENT": agent,
        }
    )
    # Native MCP servers may be launched with a restricted inherited environment.
    config = mcp_config(python, ROOT / "tools/context_control/mcp_server.py", env)
    if env.get("SPECULA_TLC_TOOL_CONFIG"):
        tlc_config = (
            json.loads(env["SPECULA_TLC_TOOL_JSON"])
            if agent == "copilot-cli"
            else json.loads(Path(env["SPECULA_TLC_TOOL_CONFIG"]).read_text())
        )
        config["mcpServers"].update(tlc_config["mcpServers"])
    write_json(directory / "mcp.json", config)
    env[MCP_ENV] = str(directory / "mcp.json")
    env["SPECULA_CONTEXT_MCP_JSON"] = json.dumps(config)
    entry = config["mcpServers"]["specula_context"]
    values = ", ".join(json.dumps(k) + "=" + json.dumps(v) for k, v in entry["env"].items())
    env["SPECULA_CONTEXT_CODEX_CONFIG"] = (
        "{command=" + json.dumps(entry["command"]) + ",args=" + json.dumps(entry["args"]) + ",env={" + values + "}}"
    )
    return env


def compaction_usage(agent: str, receipt: dict[str, Any]) -> UsageRecord | None:
    if agent == "claude-code" and isinstance(receipt.get("usage_payload"), dict):
        payload = receipt["usage_payload"]
        return _claude_usage({**payload, "model_usage": payload.get("modelUsage", {})})
    totals = UsageTotals()
    if agent == "pi" and isinstance(receipt.get("pi_usage"), dict):
        accumulate_usage(
            "pi", {"type": "message_end", "message": {"role": "assistant", "usage": receipt["pi_usage"]}}, totals
        )
    elif agent == "opencode" and isinstance(receipt.get("opencode_usage"), list):
        for info in receipt["opencode_usage"]:
            accumulate_usage("opencode", {"type": "step_finish", "part": info}, totals)
    else:
        return None
    return _normalized_usage(totals.as_payload(agent), dict(totals.as_usage()))


def publish_usage(path: Path, agent: str, session_id: str | None, records: list[UsageRecord | None]) -> None:
    observed = [record for record in records if record is not None]
    if not observed:
        return
    complete = all(record is not None and record.complete for record in records)
    cost_known = all(record is not None and record.cost_usd is not None for record in records)
    tokens_known = all(record is not None and record.total_tokens is not None for record in records)
    write_json(
        path,
        {
            "agent": agent,
            "session_id": session_id,
            "total_cost_usd": sum(r.cost_usd or 0 for r in observed) if cost_known else None,
            "usage": {
                "total_tokens": sum(r.total_tokens or 0 for r in observed) if tokens_known else None,
                "cached_input_tokens": sum(r.cached_input_tokens or 0 for r in observed) if tokens_known else None,
            },
            "usage_complete": complete,
            "observed_cost_usd": sum(r.cost_usd or 0 for r in observed)
            if any(r.cost_usd is not None for r in observed)
            else None,
            "observed_usage": {
                "total_tokens": sum(r.total_tokens or 0 for r in observed),
                "cached_input_tokens": sum(r.cached_input_tokens or 0 for r in observed),
            },
            "usage_scope": "CI invocation including context compaction"
            if complete
            else "partial; inspect context compaction receipts",
        },
    )


def run(adapter: Path, arguments: list[str]) -> int:
    options = dict(arg[2:].split("=", 1) for arg in arguments if arg.startswith("--") and "=" in arg)
    if os.environ.get("SPECULA_PHASE") != "incremental":
        return subprocess.call([str(adapter), *arguments], pass_fds=inherited_run_lock_fds())
    python = ROOT / "tools/context_control/.venv/bin/python"
    if not python.is_file():
        print("WARNING: context tool is not installed; run specula setup to enable CI compaction.", flush=True)
        return subprocess.call([str(adapter), *arguments], pass_fds=inherited_run_lock_fds())
    work = Path(os.environ["SPECULA_WORK_DIR"]).resolve()
    log = Path(options["log"])
    resume = Path(options["resume-state"])
    usage = log.with_suffix(".usage.json")
    control = work / ".context-control"
    try:
        control.mkdir(exist_ok=True)
        directory = Path(tempfile.mkdtemp(prefix="invocation-", dir=control))
        env = tool_environment(directory, work, python, adapter.stem)
    except OSError as exc:
        print(f"WARNING: context tool unavailable ({exc}); continuing without compaction.", flush=True)
        return subprocess.call([str(adapter), *arguments], pass_fds=inherited_run_lock_fds())
    records: list[UsageRecord | None] = []
    call_arguments = list(arguments)
    round_number = 0
    session_id: str | None = None
    compacted = False
    codex_compaction_unpriced = False
    try:
        while True:
            request = Path(env[REQUEST_ENV])
            request.unlink(missing_ok=True)
            rc = subprocess.call([str(adapter), *call_arguments], env=env, pass_fds=inherited_run_lock_fds())
            if usage.is_file():
                shutil.copy2(usage, directory / f"turn-{round_number + 1}.usage.json")
            record = _parse_usage_file(work, usage)
            # Codex's collector reads the whole native session, including prior
            # turns. Other CLI adapters report the current invocation's usage.
            if adapter.stem == "codex":
                records = [record]
            else:
                records.append(record)
            if rc != 0 or not request.is_file():
                return rc
            response = log.with_suffix(".last-message.txt") if adapter.stem == "codex" else log
            expected = f"{YIELD_PREFIX} {env[TOKEN_ENV]}"
            if response.read_text(errors="replace").strip().splitlines()[-1:] != [expected]:
                return rc  # Never reinterpret an ordinary final response as a yield.
            pending = json.loads(request.read_text())
            if pending.get("token") != env[TOKEN_ENV]:
                return 1
            state = json.loads(resume.read_text())
            if state.get("adapter") != adapter.stem or not state.get("session_id"):
                raise ValueError("Compaction requires the exact persisted native session")
            if session_id is not None and session_id != state["session_id"]:
                raise ValueError("Native conversation changed during compaction")
            session_id = state["session_id"]
            round_number += 1
            archive = directory / str(round_number)
            archive.mkdir()
            for suffix in (".log", ".last-message.txt", ".activity.jsonl", ".raw.json", ".usage.json"):
                source = log.with_suffix(suffix)
                if source.is_file():
                    shutil.copy2(source, archive / source.name)
            shutil.copy2(request, archive / "request.json")
            receipt_path = archive / "compaction.json"
            print(f"Context compaction: {adapter.stem}, same session {session_id}", flush=True)
            helper_env = {**env, "SPECULA_PHASE": "context_compaction"}
            helper_env.pop(REQUEST_ENV, None)
            try:
                with (archive / "control.log").open("w") as output:
                    subprocess.call(
                        [
                            str(python),
                            str(ROOT / "tools/context_control/compact.py"),
                            str(resume),
                            str(receipt_path),
                            options.get("claude-alias", ""),
                        ],
                        env=helper_env,
                        stdout=output,
                        stderr=subprocess.STDOUT,
                        pass_fds=inherited_run_lock_fds(),
                    )
            except OSError as exc:
                write_json(receipt_path, {"status": "failed", "error": str(exc)})
            try:
                receipt = json.loads(receipt_path.read_text())
            except (OSError, ValueError):
                receipt = {"status": "failed", "error": "Native compactor returned no receipt"}
            if adapter.stem != "codex":
                records.append(compaction_usage(adapter.stem, receipt))
            else:
                codex_compaction_unpriced = True
            compacted = True
            status = receipt.get("status", "failed")
            print(f"Context compaction {status}; continuing the same CI conversation.", flush=True)
            if status == "failed" and receipt.get("error"):
                print("Compaction note: " + str(receipt["error"]).replace("\n", " ")[:240], flush=True)
            prompt = directory / "continue.md"
            prompt.write_text(
                f"Continue the same incremental CI task. Context compaction {status}. "
                f"First read the saved handoff at {pending['handoff_path']}; then open only evidence needed for the next work. "
                "Keep unresolved counterexamples, invalidated results and pending checks pending. "
                "This was an internal pause, not finalization or a new run. "
                "If compaction failed, continue without repeatedly retrying it. Finish the existing workflow.\n"
            )
            call_arguments = [arg for arg in arguments if not arg.startswith(("--prompt=", "--prompt-file="))]
            call_arguments.append(f"--prompt-file={prompt}")
    finally:
        if compacted:
            publish_usage(usage, adapter.stem, session_id, records + ([None] if codex_compaction_unpriced else []))


def main() -> int:
    try:
        return run(Path(sys.argv[1]), sys.argv[2:])
    except (OSError, ValueError, KeyError) as exc:
        print(f"ERROR: CI context continuation: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
