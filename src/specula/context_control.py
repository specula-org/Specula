"""A CI-scoped request to compact an existing native Agent conversation."""

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


def request_compaction(handoff_path: str) -> dict[str, str]:
    """Bind a request to this invocation; do not judge the handoff's semantics."""
    raw = os.environ.get(REQUEST_ENV)
    token = os.environ.get(TOKEN_ENV)
    work = os.environ.get("SPECULA_WORK_DIR")
    if os.environ.get("SPECULA_PHASE") != "incremental" or not raw or not token or not work:
        raise ValueError("Context compaction is available only inside an incremental CI run.")
    root = Path(work).resolve()
    path = Path(handoff_path)
    path = (path if path.is_absolute() else root / path).resolve()
    if not path.is_relative_to(root) or not path.is_file() or path.stat().st_size == 0:
        raise ValueError("Save a nonempty handoff file inside the CI working directory first.")
    request = Path(raw)
    if not request.parent.is_dir():
        raise ValueError("The CI context controller is no longer available.")
    write_json(request, {"token": token, "handoff_path": str(path)})
    yield_instruction = f"end this turn with exactly: {YIELD_PREFIX} {token}"
    if os.environ.get("SPECULA_CONTEXT_AGENT") == "copilot-cli":
        yield_instruction = (
            f"call the native task_complete tool with summary exactly '{YIELD_PREFIX} {token}'. "
            "This completes only this internal invocation so autopilot stops; the controller will resume the CI task."
        )
    return {
        "status": "requested",
        "instruction": (
            "The controller will compact this same conversation after you yield. "
            "Do not write final CI reports or claim completion. Once outstanding tool results "
            f"are collected, {yield_instruction}"
        ),
    }


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
