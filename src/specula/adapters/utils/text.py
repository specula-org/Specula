"""Terminal-safe rendering helpers shared by adapter runtimes."""

from __future__ import annotations

import re

_ESCAPE_RE = re.compile(r"\x1b(?:\][^\x07]*(?:\x07|\x1b\\)|\[[0-?]*[ -/]*[@-~])")
_CONTROL_RE = re.compile(r"[\x00-\x1f\x7f-\x9f]")
_CONTROL_KEEP_NL_RE = re.compile(r"[\x00-\x09\x0b-\x1f\x7f-\x9f]")
SUMMARY_LIMIT = 180


def _strip_escapes(text: str) -> str:
    return _ESCAPE_RE.sub("", text)


def summary(text: str, limit: int | None = SUMMARY_LIMIT) -> str:
    """Flatten agent-controlled text to one terminal-safe line."""
    text = _CONTROL_RE.sub(" ", _strip_escapes(text))
    result = " ".join(text.split())
    if limit is not None and len(result) > limit:
        return result[: limit - 3].rstrip() + "..."
    return result


def readable(text: str) -> str:
    """Preserve line structure while removing terminal control sequences."""
    text = _CONTROL_KEEP_NL_RE.sub(" ", _strip_escapes(text))
    return "\n".join(line.rstrip() for line in text.split("\n")).strip("\n")


def readable_fragment(text: str) -> str:
    """Sanitize streamed text without changing its spacing or line breaks."""
    return _CONTROL_KEEP_NL_RE.sub(" ", _strip_escapes(text))


def _string_arg(arguments: object, *keys: str) -> str:
    if not isinstance(arguments, dict):
        return ""
    for key in keys:
        value = arguments.get(key)
        if isinstance(value, str) and value.strip():
            return value
    return ""


def tool_summary(name: str, arguments: object) -> str:
    """Render one safe, concise description of an agent tool invocation."""
    name = summary(name, 60) or "tool"
    lowered = name.casefold()
    command = _string_arg(arguments, "command", "cmd")
    path = _string_arg(arguments, "file_path", "path")
    pattern = _string_arg(arguments, "pattern", "query")
    description = _string_arg(arguments, "description", "intent", "prompt")
    if lowered in {"bash", "shell", "powershell", "command_execution"} and command:
        command = command.removeprefix("/bin/bash -lc ").removeprefix("/bin/sh -lc ")
        if len(command) >= 2 and command[0] == command[-1] and command[0] in {'"', "'"}:
            command = command[1:-1]
        return f"running {summary(command, 160)}"
    if lowered in {"read", "view", "read_file"} and path:
        return f"reading {summary(path)}"
    if lowered in {"edit", "write", "write_file", "notebookedit"} and path:
        return f"editing {summary(path)}"
    if lowered in {"grep", "glob", "search", "websearch", "web_search"} and pattern:
        return f"searching for {summary(pattern)}"
    if lowered in {"task", "spawnagent", "spawn_agent"}:
        detail = f": {summary(description)}" if description else ""
        return f"spawning subagent{detail}"
    if lowered in {"taskoutput", "wait"}:
        return "waiting for subagents"
    detail = f": {summary(description)}" if description else ""
    return f"using {name}{detail}"
