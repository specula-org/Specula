"""CI-scoped requests for compaction and one-shot bug confirmation."""

from __future__ import annotations

import json
import os
import secrets
from pathlib import Path
from typing import Any

REQUEST_ENV = "SPECULA_CONTEXT_REQUEST"
TOKEN_ENV = "SPECULA_CONTEXT_TOKEN"
PYTHON_ENV = "SPECULA_CONTEXT_PYTHON"
MCP_ENV = "SPECULA_CONTEXT_MCP_CONFIG"
YIELD_PREFIX = "SPECULA_CONTEXT_YIELD"
TOOL_NAME = "request_context_compaction"
CONFIRMATION_REQUEST = ".context-control/confirmation.json"
# Phase keys whose launcher runs one native conversation through context_runner
# (agent-requested compaction and the confirmation yield). ``incremental`` is the
# CI update workflow; ``main`` is the main session of single-session orchestration.
CONTEXT_CONTROL_PHASES = frozenset({"incremental", "main"})
REPAIR_SNAPSHOT = "spec/.repair-phase3-snapshot.json"
CONFIRMATION_YIELD_RC = 73
CONFIRMATION_TOOL = "request_bug_confirmation"
CONFIRMATION_DESCRIPTION = (
    "Submit the current MC findings and code-review Scenarios to Specula's parallel confirmation workflow. "
    "First save the current modeling brief and spec/bug-report.md (and spec/findings.json when present), "
    "and reuse applicable persistent findings. Follow the returned yield instructions; this is not CI completion."
)
TOOL_DESCRIPTION = (
    "Request native context compaction after saving and reviewing a Markdown handoff. "
    "Use between completed work batches, after collecting outstanding tool results. "
    "The request is not CI completion. Follow the returned continuation instructions."
)


def write_json(path: Path, value: Any) -> None:
    temporary = path.with_name(f".{path.name}.{secrets.token_hex(8)}.tmp")
    try:
        with temporary.open("x", encoding="utf-8") as stream:
            json.dump(value, stream, ensure_ascii=False, indent=2)
            stream.write("\n")
        temporary.replace(path)
    finally:
        temporary.unlink(missing_ok=True)


def _unconsumed_repairs(root: Path) -> list[str]:
    """Repair requests a single-session main session was resumed to handle but has not consumed."""
    try:
        snapshot = json.loads((root / REPAIR_SNAPSHOT).read_text())
    except FileNotFoundError:
        return []
    except (OSError, ValueError):
        return ["the repair snapshot is unreadable"]
    requests = snapshot.get("requests") if isinstance(snapshot, dict) else None
    if not isinstance(requests, dict):
        return ["the repair snapshot is invalid"]
    pending: list[str] = []
    for filename in sorted(requests):
        status = ""
        try:
            lines = (root / "spec/repair-requests" / filename).read_text(errors="replace").splitlines()
        except OSError:
            lines = []
        for line in lines[:25]:
            if line.startswith("status:"):
                status = "".join(line[len("status:") :].split())
                break
        if status != "CONSUMED":
            pending.append(f"{Path(filename).stem}={status or '<missing>'}")
    return pending


def _output_problems(root: Path) -> str | None:
    """The main session's required-output problems, checked before it yields.

    The controller repeats the check authoritatively at the handoff. This
    precheck only saves a yield-and-resume cycle, so it never blocks on its own
    limitations: SANY that cannot run here, or any unexpected error, skips it.
    """
    try:
        from specula import output_contract

        strict = output_contract.strict()
        problems = output_contract.handoff_problems(root, strict=strict, sany_optional=True)
    except Exception:  # noqa: BLE001 - the controller decides instead
        return None
    return output_contract.rejection(problems, strict=strict) if problems else None


def _request(action: str, handoff_path: str | None = None) -> dict[str, str]:
    raw = os.environ.get(REQUEST_ENV)
    token = os.environ.get(TOKEN_ENV)
    work = os.environ.get("SPECULA_WORK_DIR")
    phase = os.environ.get("SPECULA_PHASE")
    if phase not in CONTEXT_CONTROL_PHASES or not raw or not token or not work:
        raise ValueError(
            "Workflow requests are available only inside an incremental CI run or a single-session Specula main session."
        )
    root = Path(work).resolve()
    document: dict[str, str] = {"token": token}
    if handoff_path is not None:
        path = Path(handoff_path)
        path = (path if path.is_absolute() else root / path).resolve()
        if not path.is_relative_to(root) or not path.is_file() or path.stat().st_size == 0:
            raise ValueError("Save a nonempty handoff file inside the CI working directory first.")
        document["handoff_path"] = str(path)
    if action == "confirm":
        for relative in ("modeling-brief.md", "spec/bug-report.md"):
            if not (root / relative).is_file():
                raise ValueError(f"Save {relative} before requesting confirmation.")
        if phase == "main":
            unconsumed = _unconsumed_repairs(root)
            if unconsumed:
                raise ValueError(
                    "Finish the repair round before requesting confirmation: mark each repaired request "
                    f"CONSUMED after its full revalidation ({', '.join(unconsumed)})."
                )
            problems = _output_problems(root)
            if problems is not None:
                raise ValueError(
                    f"Confirmation was not requested. {problems}\n\n"
                    "Fix these in this turn, then request confirmation again."
                )
        document["action"] = action
    request = Path(raw)
    if not request.parent.is_dir():
        raise ValueError("The CI context controller is no longer available.")
    write_json(request, document)
    yield_instruction = f"end this turn with exactly: {YIELD_PREFIX} {token}"
    if os.environ.get("SPECULA_CONTEXT_AGENT") == "copilot-cli":
        yield_instruction = (
            f"call the native task_complete tool with summary exactly '{YIELD_PREFIX} {token}'. "
            "This completes only this internal invocation so autopilot stops; the controller will resume the CI task."
        )
    if action != "confirm":
        lead = "The controller will compact this same conversation after you yield. "
    elif phase == "main":
        lead = (
            "The controller will confirm the findings in separate clean contexts and resumes this same "
            "conversation only if repair work is needed. "
        )
    else:
        lead = "The controller will run confirmation, then resume this same conversation. "
    final = "confirmation or final reports" if phase == "main" else "final CI reports"
    return {
        "status": "requested",
        "instruction": (
            lead + f"Do not write {final} or claim completion. Once outstanding tool results "
            f"are collected, {yield_instruction}"
        ),
    }


def request_compaction(handoff_path: str) -> dict[str, str]:
    """Bind a compaction request to this invocation."""
    return _request("compact", handoff_path)


def request_confirmation() -> dict[str, str]:
    """Yield to the existing one-shot confirmation dispatcher."""
    return _request("confirm")


def mcp_config(python: Path, server: Path, env: dict[str, str]) -> dict[str, Any]:
    return {
        "mcpServers": {
            "specula_context": {
                "command": str(python),
                "args": [str(server)],
                "env": {
                    key: env[key]
                    for key in (
                        REQUEST_ENV,
                        TOKEN_ENV,
                        "SPECULA_WORK_DIR",
                        "SPECULA_PHASE",
                        "SPECULA_CONTEXT_AGENT",
                        # The main session's precheck applies the run's output contract.
                        *(("SPECULA_STRICT_OUTPUTS",) if env.get("SPECULA_PHASE") == "main" else ()),
                    )
                    if key in env
                },
            }
        }
    }
