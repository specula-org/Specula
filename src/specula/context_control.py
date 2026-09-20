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


def _request(action: str, handoff_path: str | None = None) -> dict[str, str]:
    raw = os.environ.get(REQUEST_ENV)
    token = os.environ.get(TOKEN_ENV)
    work = os.environ.get("SPECULA_WORK_DIR")
    if os.environ.get("SPECULA_PHASE") != "incremental" or not raw or not token or not work:
        raise ValueError("Workflow requests are available only inside an incremental CI run.")
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
    return {
        "status": "requested",
        "instruction": (
            (
                "The controller will run confirmation, then resume this same conversation. "
                if action == "confirm"
                else "The controller will compact this same conversation after you yield. "
            )
            + "Do not write final CI reports or claim completion. Once outstanding tool results "
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
                    for key in (REQUEST_ENV, TOKEN_ENV, "SPECULA_WORK_DIR", "SPECULA_PHASE", "SPECULA_CONTEXT_AGENT")
                    if key in env
                },
            }
        }
    }
