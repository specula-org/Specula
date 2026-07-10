"""Tee adapter JSONL into raw and incrementally readable activity logs.

The `.activity.jsonl` sidecar holds the adapter's event stream as emitted, minus
the tool-result echo records (see `_is_tool_echo`), plus any non-JSON diagnostic
the CLI wrote to stderr — both adapters merge stderr into the stream so an
"unknown flag" line still reaches the reader.
"""

from __future__ import annotations

import json
import re
import sys
from collections.abc import Callable, Iterable
from pathlib import Path

_ESCAPE_RE = re.compile(r"\x1b(?:\][^\x07]*(?:\x07|\x1b\\)|\[[0-?]*[ -/]*[@-~])")
_CONTROL_RE = re.compile(r"[\x00-\x1f\x7f-\x9f]")
_CONTROL_KEEP_NL_RE = re.compile(r"[\x00-\x09\x0b-\x1f\x7f-\x9f]")  # every control char but \n
_SUMMARY_LIMIT = 180


def _strip_escapes(text: str) -> str:
    return _ESCAPE_RE.sub("", text)


def summary(text: str, limit: int | None = _SUMMARY_LIMIT) -> str:
    """Flatten agent-controlled text to one terminal-safe line."""
    text = _CONTROL_RE.sub(" ", _strip_escapes(text))
    result = " ".join(text.split())
    if limit is not None and len(result) > limit:
        return result[: limit - 3].rstrip() + "..."
    return result


def readable(text: str) -> str:
    """Terminal-safe like `summary`, but line structure survives.

    The agent's final answer is markdown; `summary` would collapse a whole
    report into one line, which is fine for a CLI ticker and useless in
    agent.log. Escapes and every other control character still go."""
    text = _CONTROL_KEEP_NL_RE.sub(" ", _strip_escapes(text))
    return "\n".join(line.rstrip() for line in text.split("\n")).strip("\n")


def _string_arg(arguments: object, *keys: str) -> str:
    if not isinstance(arguments, dict):
        return ""
    for key in keys:
        value = arguments.get(key)
        if isinstance(value, str) and value.strip():
            return value
    return ""


def tool_summary(name: str, arguments: object) -> str:
    # `name` is as agent-controlled as the arguments are — an MCP server picks its
    # own tool names, and this string goes straight to the user's terminal.
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


def _text_event(text: str, concise: bool) -> str:
    return summary(text) if concise else readable(text)


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


_PARSERS: dict[str, Callable[[object, bool], list[str]]] = {
    "claude-code": _claude_events,
    "codex": _codex_events,
    "copilot-cli": _copilot_events,
}


def _is_tool_echo(adapter_name: str, record: object) -> bool:
    """True for records that only replay a tool's output back to the model.

    Nothing downstream reads them — not the parsers above, not the adapter's
    result lookup — yet they carry the full text of every file the agent opened,
    which is the bulk of a long phase's stream. Claude keeps its own complete
    session JSONL under `CLAUDE_CONFIG_DIR/projects/`, so dropping them from our
    sidecar costs no information that cannot be recovered."""
    if not isinstance(record, dict):
        return False
    if adapter_name == "claude-code":
        return record.get("type") == "user"
    if adapter_name == "codex":
        item = record.get("item")
        return (
            record.get("type") == "item.completed"
            and isinstance(item, dict)
            and item.get("type") == "command_execution"
        )
    return False  # copilot-cli: no pinned event for command output, keep it whole


def _read_line(adapter_name: str, line: str, concise: bool) -> tuple[bool, list[str]]:
    """One line of adapter output -> (persist the raw line?, readable events).

    Never raises on malformed input: a line that is not JSON is the CLI's own
    diagnostic, and losing it is worse than showing it."""
    try:
        record = json.loads(line)
    except (TypeError, ValueError):
        text = summary(line, _SUMMARY_LIMIT if concise else None)
        is_error = any(term in text.casefold() for term in ("error", "failed", "require", "invalid", "unknown"))
        if text and (is_error or not concise):
            return True, [f"adapter error: {text}" if is_error else text]
        return True, []
    if _is_tool_echo(adapter_name, record):
        return False, []
    return True, _PARSERS[adapter_name](record, concise)


def parse_events(adapter_name: str, lines: list[str], *, concise: bool = True) -> list[str]:
    """Convert raw JSONL records into readable activity without raising on malformed input."""
    if adapter_name not in _PARSERS:
        return []
    events: list[str] = []
    for line in lines:
        events.extend(_read_line(adapter_name, line, concise)[1])
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
    # encoding/errors explicitly: the agent writes whatever it likes, and the
    # ambient locale must not be able to kill a run with a UnicodeEncodeError.
    with activity_path.open("wb") as raw_log, log_path.open("w", encoding="utf-8", errors="replace") as log:
        for raw_line in source:
            keep, events = _read_line(adapter_name, raw_line.decode(errors="replace"), concise=False)
            if keep:
                raw_log.write(raw_line)
                raw_log.flush()
            for event in events:
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
