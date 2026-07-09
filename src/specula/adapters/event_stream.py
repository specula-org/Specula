"""Tee adapter JSONL into raw and incrementally readable activity logs."""

from __future__ import annotations

import json
import re
import sys
from collections.abc import Iterable
from pathlib import Path

_ESCAPE_RE = re.compile(r"\x1b(?:\][^\x07]*(?:\x07|\x1b\\)|\[[0-?]*[ -/]*[@-~])")
_CONTROL_RE = re.compile(r"[\x00-\x1f\x7f-\x9f]")
_SUMMARY_LIMIT = 180


def summary(text: str, limit: int | None = _SUMMARY_LIMIT) -> str:
    """Flatten agent-controlled text and remove terminal control sequences."""
    text = _ESCAPE_RE.sub("", text)
    text = _CONTROL_RE.sub(" ", text)
    result = " ".join(text.split())
    if limit is not None and len(result) > limit:
        return result[: limit - 3].rstrip() + "..."
    return result


def _string_arg(arguments: object, *keys: str) -> str:
    if not isinstance(arguments, dict):
        return ""
    for key in keys:
        value = arguments.get(key)
        if isinstance(value, str) and value.strip():
            return value
    return ""


def tool_summary(name: str, arguments: object) -> str:
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


def _text_event(text: str, concise: bool) -> str:
    return summary(text, _SUMMARY_LIMIT if concise else None)


def _claude_events(record: object, concise: bool) -> list[str]:
    if not isinstance(record, dict):
        return []
    if record.get("type") == "result":
        result = record.get("result")
        return [_text_event(result, concise)] if isinstance(result, str) else []
    if record.get("type") != "assistant":
        return []
    message = record.get("message")
    content = message.get("content") if isinstance(message, dict) else None
    if not isinstance(content, list):
        return []
    events: list[str] = []
    for block in content:
        if not isinstance(block, dict):
            continue
        text = block.get("text")
        name = block.get("name")
        if block.get("type") == "text" and isinstance(text, str):
            events.append(_text_event(text, concise))
        elif block.get("type") == "tool_use" and isinstance(name, str):
            events.append(tool_summary(name, block.get("input")))
    return events


def _copilot_events(record: object, concise: bool) -> list[str]:
    if not isinstance(record, dict):
        return []
    data = record.get("data")
    if not isinstance(data, dict):
        return []
    content = data.get("content")
    tool_name = data.get("toolName")
    if record.get("type") == "assistant.message" and isinstance(content, str):
        return [_text_event(content, concise)]
    if record.get("type") == "tool.execution_start" and isinstance(tool_name, str):
        if tool_name == "report_intent":
            return []
        return [tool_summary(tool_name, data.get("arguments"))]
    return []


def _codex_events(record: object, concise: bool) -> list[str]:
    if not isinstance(record, dict) or record.get("type") not in {"item.started", "item.completed"}:
        return []
    item = record.get("item")
    if not isinstance(item, dict):
        return []
    item_type = item.get("type")
    if record.get("type") == "item.completed" and item_type == "agent_message":
        text = item.get("text")
        return [_text_event(text, concise)] if isinstance(text, str) else []
    if record.get("type") != "item.started" or not isinstance(item_type, str):
        return []
    if item_type == "command_execution":
        return [tool_summary(item_type, {"command": item.get("command")})]
    if item_type in {"mcp_tool_call", "web_search"}:
        name = item.get("tool") or item_type
        return [tool_summary(str(name), item.get("arguments"))]
    return []


def parse_events(adapter_name: str, lines: list[str], *, concise: bool = True) -> list[str]:
    """Convert raw JSONL records into readable activity without raising on malformed input."""
    parsers = {
        "claude-code": _claude_events,
        "codex": _codex_events,
        "copilot-cli": _copilot_events,
    }
    parser = parsers.get(adapter_name)
    if parser is None:
        return []
    events: list[str] = []
    for line in lines:
        try:
            record = json.loads(line)
        except (TypeError, ValueError):
            text = summary(line, _SUMMARY_LIMIT if concise else None)
            is_error = any(term in text.casefold() for term in ("error", "failed", "require", "invalid", "unknown"))
            if text and (is_error or not concise):
                events.append(f"adapter error: {text}" if is_error else text)
            continue
        events.extend(parser(record, concise))
    return events

_ADAPTER_NAMES = {
    "claude": "claude-code",
    "claude-code": "claude-code",
    "codex": "codex",
    "copilot": "copilot-cli",
    "copilot-cli": "copilot-cli",
}


def stream_events(
    adapter: str,
    activity_path: Path,
    log_path: Path,
    source: Iterable[bytes] | None = None,
) -> None:
    """Persist raw JSONL and flush readable activity after every event."""
    source = source if source is not None else sys.stdin.buffer
    adapter_name = _ADAPTER_NAMES[adapter]
    last_event = ""
    with activity_path.open("wb") as raw_log, log_path.open("w") as log:
        for raw_line in source:
            raw_log.write(raw_line)
            raw_log.flush()
            line = raw_line.decode(errors="replace")
            for event in parse_events(adapter_name, [line], concise=False):
                if not event or event == last_event:
                    continue
                log.write(event.rstrip("\n") + "\n")
                log.flush()
                last_event = event


def main(argv: list[str]) -> int:
    if len(argv) != 3 or argv[0] not in _ADAPTER_NAMES:
        print("usage: event_stream.py {claude|codex|copilot} ACTIVITY_JSONL LOG_FILE", file=sys.stderr)
        return 2
    try:
        stream_events(argv[0], Path(argv[1]), Path(argv[2]))
    except OSError as exc:
        print(f"adapter event stream failed: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
