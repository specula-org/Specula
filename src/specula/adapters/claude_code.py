"""Adapter: claude-code (Python port of claude-code.sh).

Unified interface for invoking the Claude Code CLI. The command-construction
contract (argv assembly, config-dir from the alias, exit codes incl. the
rate-limit 75, the num_turns session fixup) is pinned by
tests/unit/test_adapters.py.

Options:
  --prompt=...          Task prompt (mutually exclusive with --prompt-file)
  --prompt-file=FILE    Read prompt from file (mutually exclusive with --prompt)
  --max-turns=N         (DEPRECATED, ignored — use --max-budget)
  --max-budget=N        Max dollar budget for API calls (optional)
  --claude-alias=NAME   Claude CLI alias/profile (default: claude). Selects
                        CLAUDE_CONFIG_DIR=$HOME/.<NAME>. Also via CLAUDE_ALIAS env.
  --effort=LEVEL        low|medium|high|xhigh|max (default: max; via CLAUDE_EFFORT)
  --model=NAME          Model alias/name (default: profile default; via CLAUDE_MODEL)
  --log=FILE            Log file path (required)
  --background          Run in background (accepted; caller handles backgrounding)
  --help                Show this help
"""

import contextlib
import json
import os
import shlex
import subprocess
import sys
import tempfile
from typing import Any

HELP = __doc__

# Nested-session markers stripped before spawning claude, so the child CLI does
# not believe it is running inside another Claude Code session.
SESSION_ENV_VARS = ("CLAUDECODE", "CLAUDE_CODE_SSE_PORT", "CLAUDE_CODE_ENTRYPOINT")


def _derived_path(log_file: str, suffix: str) -> str:
    """Mirror bash `${LOG_FILE%.log}<suffix>`."""
    stem = log_file[:-4] if log_file.endswith(".log") else log_file
    return stem + suffix


def _maybe_wrap_sandbox(cmd: list[str], work_dir: str) -> list[str]:
    """Optionally wrap the agent command in the outer srt sandbox (M1.3).

    Opt-in via ``SPECULA_SANDBOX=on``; additive — when off/unset the command is
    returned byte-for-byte (legacy). One outer srt layer wraps claude and every
    descendant it spawns (TLC / MCP / build); the inner
    ``--dangerously-skip-permissions`` stays, so the agent runs YOLO with no
    nested second sandbox. Backend path is repo-relative but overridable via
    ``SPECULA_SANDBOX_BACKEND`` (e.g. an installed layout).
    """
    if os.environ.get("SPECULA_SANDBOX", "").lower() != "on":
        return cmd
    backend = os.environ.get("SPECULA_SANDBOX_BACKEND") or os.path.normpath(
        os.path.join(
            os.path.dirname(os.path.abspath(__file__)),
            "..",
            "..",
            "..",
            "scripts",
            "launch",
            "sandbox",
            "backend.mjs",
        )
    )
    workspace = work_dir or os.getcwd()
    return ["node", backend, "--workspace", workspace, "--", *cmd]


def _parse_result(raw_text: str) -> dict[str, Any] | None:
    """Find the Claude result in single-result JSON or a stream-json capture."""
    try:
        d = json.loads(raw_text)
    except Exception:
        d = None
    if isinstance(d, dict):
        return d
    for line in reversed(raw_text.splitlines()):
        try:
            candidate = json.loads(line)
        except Exception:
            continue
        if isinstance(candidate, dict) and (candidate.get("type") == "result" or "result" in candidate):
            return candidate
    return None


def _extract_log(d: dict[str, Any] | None, raw_text: str, log_file: str) -> None:
    """Result text -> .log; on JSON-parse failure, fall back to the raw output."""
    with open(log_file, "w") as fh:
        if d is not None:
            print(d.get("result", ""), file=fh)
        else:
            print(raw_text, file=fh)


def _extract_usage(d: dict[str, Any] | None, usage_path: str) -> None:
    """Usage stats -> .usage.json, fixing num_turns from the session JSONL when a
    session_id is present. Any failure -> {"error": "parse_failed"} (mirrors the
    bash `|| parse_failed` fallback)."""
    try:
        if d is None:
            raise ValueError("result JSON unparseable")
        usage = {
            "total_cost_usd": d.get("total_cost_usd", 0),
            "num_turns": d.get("num_turns", 0),
            "duration_ms": d.get("duration_ms", 0),
            "stop_reason": d.get("stop_reason", ""),
            "usage": d.get("usage", {}),
            "model_usage": d.get("modelUsage", {}),
        }
        session_id = d.get("session_id", "")
        if session_id:
            cwd = os.getcwd()
            proj_key = cwd.replace("/", "-").lstrip("-")
            config_dir = os.environ.get("CLAUDE_CONFIG_DIR") or os.path.expanduser("~/.claude")
            proj_dir = os.path.join(config_dir, "projects", f"-{proj_key}")
            jsonl_path = os.path.join(proj_dir, f"{session_id}.jsonl")
            if os.path.exists(jsonl_path):
                assistant_count = 0
                tool_count = 0
                with open(jsonl_path) as f:
                    for line in f:
                        # Session transcripts are dominated by huge tool-result
                        # lines; skip the full JSON parse for anything that can't
                        # be an assistant turn (cheap superset substring test).
                        if '"assistant"' not in line:
                            continue
                        try:
                            msg = json.loads(line)
                            if msg.get("type") == "assistant":
                                assistant_count += 1
                                content = msg.get("message", {}).get("content", [])
                                if isinstance(content, list):
                                    tool_count += sum(
                                        1 for c in content if isinstance(c, dict) and c.get("type") == "tool_use"
                                    )
                        except Exception:
                            pass
                usage["num_turns_reported"] = usage["num_turns"]
                usage["num_turns"] = assistant_count
                usage["num_tool_uses"] = tool_count
        with open(usage_path, "w") as uf:
            json.dump(usage, uf, indent=2)
            uf.write("\n")
    except Exception:
        with open(usage_path, "w") as uf:
            json.dump({"error": "parse_failed"}, uf)
            uf.write("\n")


def _die(msg: str) -> int:
    print(msg, file=sys.stderr)
    return 1


def main(argv: list[str]) -> int:
    prompt = ""
    prompt_file = ""
    max_budget = ""
    log_file = ""
    _background = False  # accepted; caller does the backgrounding, as in bash
    # `or`: bash ${VAR:-default} treats an exported-but-empty var as unset — an
    # empty CLAUDE_EFFORT must still mean "max", not "skip the --effort flag".
    claude_alias = os.environ.get("CLAUDE_ALIAS") or "claude"
    effort = os.environ.get("CLAUDE_EFFORT") or "max"
    model = os.environ.get("CLAUDE_MODEL", "")

    for arg in argv:
        if arg.startswith("--prompt="):
            prompt = arg[len("--prompt=") :]
        elif arg.startswith("--prompt-file="):
            prompt_file = arg[len("--prompt-file=") :]
        elif arg.startswith("--max-turns="):
            pass  # deprecated, ignored
        elif arg.startswith("--max-budget="):
            max_budget = arg[len("--max-budget=") :]
        elif arg.startswith("--claude-alias="):
            claude_alias = arg[len("--claude-alias=") :]
        elif arg.startswith("--effort="):
            effort = arg[len("--effort=") :]
        elif arg.startswith("--model="):
            model = arg[len("--model=") :]
        elif arg.startswith("--log="):
            log_file = arg[len("--log=") :]
        elif arg == "--background":
            _background = True
        elif arg in ("--help", "-h"):
            print(HELP)
            return 0
        else:
            return _die(f"claude-code adapter: unknown option: {arg}")

    # ── Validate arguments ──
    if prompt and prompt_file:
        return _die("claude-code adapter: --prompt and --prompt-file are mutually exclusive")
    if not prompt and not prompt_file:
        return _die("claude-code adapter: one of --prompt or --prompt-file is required")
    if not log_file:
        return _die("claude-code adapter: --log is required")

    # ── Resolve prompt ──
    # Feed prompt via stdin (not -p) to keep the process cmdline clean, so
    # `pkill -f` can't collateral-kill on strings like "tlc2.TLC".
    tmp_prompt = None
    if prompt_file:
        if not os.path.isfile(prompt_file):
            return _die(f"claude-code adapter: prompt file not found: {prompt_file}")
        prompt_input = prompt_file
    else:
        fd, tmp_prompt = tempfile.mkstemp()
        with os.fdopen(fd, "w") as f:
            f.write(prompt + "\n")
        prompt_input = tmp_prompt

    try:
        # ── Environment setup ──
        for var in SESSION_ENV_VARS:
            os.environ.pop(var, None)
        # Alias determines the config dir authoritatively (do NOT inherit an
        # ambient CLAUDE_CONFIG_DIR, which would redirect quota-sensitive runs).
        os.environ["CLAUDE_CONFIG_DIR"] = os.environ.get("HOME", "") + "/." + (claude_alias or "claude")

        # ── Stop gate (execution layer) ──
        # Generic gate interface: the phase launcher exports SPECULA_PHASE +
        # SPECULA_WORK_DIR (see src/specula/stop_gate.py). When both are present,
        # register a Stop hook so the agent cannot end its turn while background
        # jobs it started run unobserved, or without the phase deliverable.
        # Without them (interactive use, tests, other callers) nothing is
        # injected and the claude argv is unchanged.
        settings_args: list[str] = []
        work_dir = os.environ.get("SPECULA_WORK_DIR", "")
        if (
            work_dir
            and os.environ.get("SPECULA_PHASE")
            and os.environ.get("SPECULA_STOP_GATE", "").lower() != "off"
            and os.path.isdir(work_dir)
        ):
            try:
                gate = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "stop_gate.py"))
                state_dir = os.path.join(work_dir, ".stop-gate")
                os.makedirs(state_dir, exist_ok=True)
                # Fresh fuse per agent run — via the gate's own CLI (like
                # codex.sh) so the state-file list has exactly one owner.
                subprocess.run([sys.executable, gate, "reset", work_dir], check=False)
                hook = {"type": "command", "command": f"python3 {shlex.quote(gate)} claude", "timeout": 60}
                settings_path = os.path.join(state_dir, "claude-settings.json")
                with open(settings_path, "w") as sf:
                    json.dump({"hooks": {"Stop": [{"hooks": [hook]}]}}, sf, indent=2)
                    sf.write("\n")
                settings_args = ["--settings", settings_path]
            except OSError as e:  # fail-open: a broken gate must never wedge the run
                settings_args = []
                print(
                    f"claude-code adapter: stop-gate setup failed ({e}); continuing without the gate", file=sys.stderr
                )

        # ── Build command ──
        activity_log = os.environ.get("SPECULA_ACTIVITY_LOG", "")
        output_format = "stream-json" if activity_log else "json"
        cmd = ["claude", "--print", "--dangerously-skip-permissions", "--output-format", output_format]
        if activity_log:
            cmd += ["--verbose"]
        if effort and effort != "default":
            cmd += ["--effort", effort]
        if max_budget and max_budget != "0":
            cmd += ["--max-budget-usd", max_budget]
        if model:
            cmd += ["--model", model]
        cmd += settings_args
        cmd = _maybe_wrap_sandbox(cmd, work_dir)

        # ── Run ──
        raw_json = _derived_path(log_file, ".raw.json")
        capture_path = activity_log or raw_json
        cli_rc = 127
        try:
            with open(prompt_input) as pin, open(capture_path, "w") as out:
                cli_rc = subprocess.run(cmd, stdin=pin, stdout=out, stderr=subprocess.STDOUT).returncode
        except OSError as e:
            # Keep producing the normal diagnostics, then report a conventional
            # command-not-found status to the phase runner.
            with open(capture_path, "w") as out:
                out.write(f"claude-code adapter: failed to run claude: {e}\n")

        # errors="replace" is a deliberate deviation from the bash, which died on
        # non-UTF-8 claude output (UnicodeDecodeError under set -e: non-zero exit,
        # empty .log, no .usage.json — and a rate-limit hit lost its exit-75 retry
        # signal). Degrade to U+FFFD + parse_failed on the normal exit-code path
        # instead (test_adapters.py::test_nonutf8_output_degrades_gracefully).
        raw_text = open(capture_path, errors="replace").read()

        # ── Detect rate limit → exit 75 (EX_TEMPFAIL) so callers can wait/retry ──
        rate_limited = "hit your limit" in raw_text
        if rate_limited:
            print("claude-code adapter: rate limit hit", file=sys.stderr)

        result = _parse_result(raw_text)
        if activity_log:
            with open(raw_json, "w") as out:
                if result is not None:
                    json.dump(result, out)
                    out.write("\n")
                else:
                    out.write(raw_text)
        _extract_log(result, raw_text, log_file)
        _extract_usage(result, _derived_path(log_file, ".usage.json"))

        return 75 if rate_limited else cli_rc
    finally:
        if tmp_prompt is not None:
            with contextlib.suppress(OSError):
                os.remove(tmp_prompt)


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
