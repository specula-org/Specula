"""Tee adapter JSONL into raw and incrementally readable activity logs.

The `.activity.jsonl` sidecar holds the adapter's event stream as emitted, minus
the tool-result echo records (see `_is_tool_echo`), plus any non-JSON diagnostic
the CLI wrote to stderr — both adapters merge stderr into the stream so an
"unknown flag" line still reaches the reader.
"""

from __future__ import annotations

import contextlib
import json
import math
import re
import sys
from collections.abc import Callable, Iterable
from dataclasses import dataclass
from pathlib import Path
from typing import BinaryIO, TextIO, cast

_ESCAPE_RE = re.compile(r"\x1b(?:\][^\x07]*(?:\x07|\x1b\\)|\[[0-?]*[ -/]*[@-~])")
_CONTROL_RE = re.compile(r"[\x00-\x1f\x7f-\x9f]")
_CONTROL_KEEP_NL_RE = re.compile(r"[\x00-\x09\x0b-\x1f\x7f-\x9f]")  # every control char but \n
_SUMMARY_LIMIT = 180


@dataclass(frozen=True)
class StreamStatus:
    activity_ok: bool
    log_ok: bool
    terminal_record: object | None
    plain_diagnostics: tuple[str, ...]
    usage: dict[str, object]


@dataclass
class UsageTotals:
    session_id: str | None = None
    total_cost_usd: float | None = None
    input_tokens: int = 0
    cached_input_tokens: int = 0
    cache_write_input_tokens: int = 0
    output_tokens: int = 0
    reasoning_output_tokens: int = 0

    def add_cost(self, value: object) -> None:
        if isinstance(value, (int, float)) and not isinstance(value, bool):
            try:
                cost = float(value)
            except OverflowError:
                return
            if cost >= 0 and math.isfinite(cost):
                self.total_cost_usd = (self.total_cost_usd or 0.0) + cost

    def as_payload(self, agent: str) -> dict[str, object]:
        total = (
            self.input_tokens
            + self.cached_input_tokens
            + self.cache_write_input_tokens
            + self.output_tokens
            + self.reasoning_output_tokens
        )
        return {
            "agent": agent,
            "session_id": self.session_id,
            "session_file": None,
            "total_cost_usd": self.total_cost_usd,
            "usage": {
                "input_tokens": self.input_tokens,
                "cached_input_tokens": self.cached_input_tokens,
                "cache_write_input_tokens": self.cache_write_input_tokens,
                "output_tokens": self.output_tokens,
                "reasoning_output_tokens": self.reasoning_output_tokens,
                "total_tokens": total,
            },
        }


_INVALID_RECORD = object()


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


def _diagnostic_message(value: object) -> str:
    """Extract the human-readable part of a structured adapter error."""
    if isinstance(value, str):
        return value
    if isinstance(value, dict):
        message = value.get("message")
        if isinstance(message, str):
            return message
    return ""


def _diagnostic_event(kind: str, message: str, concise: bool) -> list[str]:
    text = _text_event(message, concise)
    return [f"adapter {kind}: {text}"] if text else []


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
    if record.get("type") == "session.error":
        if not isinstance(data, dict):
            return _diagnostic_event("error", _diagnostic_message(record), concise)
        message = _diagnostic_message(data)
        error_type = data.get("errorType")
        status_code = data.get("statusCode")
        details: list[str] = []
        if isinstance(error_type, str) and error_type:
            details.append(summary(error_type, 60))
        if isinstance(status_code, int):
            details.append(f"HTTP {status_code}")
        if details:
            message = f"{' / '.join(details)}: {message}" if message else " / ".join(details)
        return _diagnostic_event("error", message, concise)
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
    if not isinstance(record, dict):
        return []
    record_type = record.get("type")
    if record_type == "error":
        return _diagnostic_event("error", _diagnostic_message(record), concise)
    if record_type == "turn.failed":
        return _diagnostic_event("error", _diagnostic_message(record.get("error")), concise)
    if record_type not in {"item.started", "item.updated", "item.completed"}:
        return []
    item = record.get("item")
    if not isinstance(item, dict):
        return []
    item_type = item.get("type")
    if item_type == "error":
        # Codex explicitly defines error items as non-fatal notifications. They
        # still belong in agent.log, but only a terminal turn.failed event should
        # turn an otherwise successful CLI invocation into a failure.
        return _diagnostic_event("warning", _diagnostic_message(item), concise)
    if record_type == "item.completed" and item_type == "agent_message":
        text = item.get("text")
        return [_text_event(text, concise)] if isinstance(text, str) else []
    if record_type != "item.started" or not isinstance(item_type, str):
        return []
    if item_type == "command_execution":
        return [tool_summary(item_type, {"command": item.get("command")})]
    if item_type in {"mcp_tool_call", "web_search"}:
        name = item.get("tool") or item_type
        return [tool_summary(str(name), item.get("arguments"))]
    return []


def _opencode_events(record: object, concise: bool) -> list[str]:
    if not isinstance(record, dict):
        return []
    if record.get("type") == "error":
        return _diagnostic_event("error", _diagnostic_message(record.get("error")), concise)
    part = record.get("part")
    if not isinstance(part, dict):
        return []
    if part.get("type") == "text":
        text = part.get("text")
        return [_text_event(text, concise)] if isinstance(text, str) else []
    if part.get("type") != "tool":
        return []
    name = part.get("tool")
    state = part.get("state")
    arguments = state.get("input") if isinstance(state, dict) else None
    return [tool_summary(name, arguments)] if isinstance(name, str) else []


def _pi_events(record: object, concise: bool) -> list[str]:
    if not isinstance(record, dict):
        return []
    record_type = record.get("type")
    if record_type == "error" or record_type == "warning":
        nested = record.get(record_type)
        message = _diagnostic_message(nested) or _diagnostic_message(record)
        return _diagnostic_event(record_type, message, concise)
    if record_type == "message_update":
        update = record.get("assistantMessageEvent")
        if isinstance(update, dict) and update.get("type") == "text_delta":
            delta = update.get("delta")
            return [_text_event(delta, concise)] if isinstance(delta, str) else []
        return []
    if record_type == "tool_execution_start":
        name = record.get("toolName")
        return [tool_summary(name, record.get("args"))] if isinstance(name, str) else []
    return []


_PARSERS: dict[str, Callable[[object, bool], list[str]]] = {
    "claude-code": _claude_events,
    "codex": _codex_events,
    "copilot-cli": _copilot_events,
    "opencode": _opencode_events,
    "pi": _pi_events,
}


def _token_count(value: object) -> int:
    if isinstance(value, bool):
        return 0
    if isinstance(value, int):
        return value if value >= 0 else 0
    if not isinstance(value, float):
        return 0
    if value < 0 or not math.isfinite(value) or not value.is_integer():
        return 0
    return int(value)


def _accumulate_usage(adapter_name: str, record: object, totals: UsageTotals) -> None:
    if not isinstance(record, dict):
        return
    if adapter_name == "opencode":
        session_id = record.get("sessionID")
        if totals.session_id is None and isinstance(session_id, str):
            totals.session_id = session_id
        if record.get("type") != "step_finish":
            return
        part = record.get("part")
        if not isinstance(part, dict):
            return
        totals.add_cost(part.get("cost"))
        tokens = part.get("tokens")
        if not isinstance(tokens, dict):
            return
        cache = tokens.get("cache")
        totals.input_tokens += _token_count(tokens.get("input"))
        totals.output_tokens += _token_count(tokens.get("output"))
        totals.reasoning_output_tokens += _token_count(tokens.get("reasoning"))
        if isinstance(cache, dict):
            totals.cached_input_tokens += _token_count(cache.get("read"))
            totals.cache_write_input_tokens += _token_count(cache.get("write"))
        return
    if adapter_name != "pi":
        return
    if record.get("type") == "session":
        session_id = record.get("id")
        if totals.session_id is None and isinstance(session_id, str):
            totals.session_id = session_id
        return
    if record.get("type") != "message_end":
        return
    message = record.get("message")
    if not isinstance(message, dict) or message.get("role") != "assistant":
        return
    usage = message.get("usage")
    if not isinstance(usage, dict):
        return
    totals.input_tokens += _token_count(usage.get("input"))
    totals.output_tokens += _token_count(usage.get("output"))
    totals.cached_input_tokens += _token_count(usage.get("cacheRead"))
    totals.cache_write_input_tokens += _token_count(usage.get("cacheWrite"))
    cost = usage.get("cost")
    if isinstance(cost, dict):
        totals.add_cost(cost.get("total"))


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


def _read_line(adapter_name: str, line: str, concise: bool) -> tuple[bool, list[str], object]:
    """One line -> (persist raw?, readable events, parsed record or sentinel).

    Never raises on malformed input: a line that is not JSON is the CLI's own
    diagnostic, and losing it is worse than showing it."""
    try:
        record = json.loads(line)
    except (TypeError, ValueError):
        text = summary(line, _SUMMARY_LIMIT if concise else None)
        if adapter_name == "copilot-cli":
            # Pre-JSON Copilot output is the agent's response, not a diagnostic
            # channel. Preserve wording such as "tests failed before the fix"
            # and literal "API Error:" markers without guessing their meaning.
            return True, [text] if text else [], _INVALID_RECORD
        is_error = any(term in text.casefold() for term in ("error", "failed", "require", "invalid", "unknown"))
        if text and (is_error or not concise):
            return True, [f"adapter error: {text}" if is_error else text], _INVALID_RECORD
        return True, [], _INVALID_RECORD
    if _is_tool_echo(adapter_name, record):
        return False, [], record
    return True, _PARSERS[adapter_name](record, concise), record


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
    "opencode": "opencode",
    "pi": "pi",
}


def stream_events(
    adapter: str,
    activity_path: Path,
    log_path: Path,
    source: Iterable[bytes] | None = None,
) -> StreamStatus:
    """Persist both views independently and report sink health.

    A sink can fail after hours of work (disk full, revoked mount, broken pipe).
    Keep consuming the source and writing the other sink, then report all sink
    failures at EOF so the underlying CLI never receives SIGPIPE from us. The
    activity sidecar is progress telemetry; agent.log is the scheduler-facing
    durable result and therefore the only sink that affects helper status.
    """
    source = source if source is not None else sys.stdin.buffer
    adapter_name = _ADAPTER_NAMES[adapter]
    usage_totals = UsageTotals()
    last_event = ""
    terminal_record: object | None = None
    plain_diagnostics: list[str] = []
    raw_failures: list[str] = []
    readable_failures: list[str] = []
    raw_log: BinaryIO | None = None
    log: TextIO | None = None

    # encoding/errors explicitly: the agent writes whatever it likes, and the
    # ambient locale must not be able to kill a run with a UnicodeEncodeError.
    try:
        raw_log = activity_path.open("wb")
    except OSError as exc:
        raw_failures.append(f"activity log {activity_path}: {exc}")
    try:
        log = log_path.open("w", encoding="utf-8", errors="replace")
    except OSError as exc:
        readable_failures.append(f"readable log {log_path}: {exc}")

    def write_raw(data: bytes) -> None:
        nonlocal raw_log
        if not data or raw_log is None:
            return
        try:
            raw_log.write(data)
            raw_log.flush()
        except OSError as exc:
            raw_failures.append(f"activity log {activity_path}: {exc}")
            with contextlib.suppress(OSError):
                raw_log.close()
            raw_log = None

    def handle_line(raw_line: bytes, *, raw_already_written: bool) -> None:
        nonlocal last_event, log, terminal_record
        decoded = raw_line.decode(errors="replace")
        keep, events, record = _read_line(adapter_name, decoded, concise=False)
        _accumulate_usage(adapter_name, record, usage_totals)
        if adapter_name == "claude-code":
            if isinstance(record, dict) and record.get("type") == "result":
                terminal_record = record
            elif record is _INVALID_RECORD and decoded.strip():
                # Claude's stream-json mode uses non-JSON only for CLI
                # diagnostics. Retain those few lines so quota banners survive
                # an activity-sidecar failure without buffering the full stream.
                plain_diagnostics.append(decoded)
        if keep and not raw_already_written:
            write_raw(raw_line)
        for event in events:
            if not event or event == last_event:
                continue
            last_event = event
            if log is not None:
                try:
                    log.write(event.rstrip("\n") + "\n")
                    log.flush()
                except OSError as exc:
                    readable_failures.append(f"readable log {log_path}: {exc}")
                    with contextlib.suppress(OSError):
                        log.close()
                    log = None

    try:
        read1 = getattr(source, "read1", None)
        if callable(read1):
            read_chunk = cast(Callable[[int], bytes], read1)
            pending = bytearray()
            while chunk := read_chunk(1 << 16):
                raw_already_written = adapter_name == "copilot-cli"
                if raw_already_written:
                    # Copilot has no filtered tool-echo records. Writing each
                    # chunk immediately preserves liveness for pre-JSON CLIs,
                    # whose text mode emits token-by-token without newlines.
                    write_raw(chunk)
                parts = chunk.split(b"\n")
                pending.extend(parts[0])
                for part in parts[1:]:
                    handle_line(bytes(pending) + b"\n", raw_already_written=raw_already_written)
                    pending = bytearray(part)
            if pending:
                handle_line(bytes(pending), raw_already_written=adapter_name == "copilot-cli")
        else:
            # Tests and library callers historically pass an iterable of complete
            # lines. Preserve that contract while real pipe readers use chunks.
            for raw_line in source:
                raw_already_written = adapter_name == "copilot-cli"
                if raw_already_written:
                    write_raw(raw_line)
                handle_line(raw_line, raw_already_written=raw_already_written)
    finally:
        for sink_name, path, sink in (
            ("activity log", activity_path, raw_log),
            ("readable log", log_path, log),
        ):
            if sink is None:
                continue
            try:
                sink.close()
            except OSError as exc:
                target = raw_failures if sink_name == "activity log" else readable_failures
                target.append(f"{sink_name} {path}: {exc}")

    for failure in raw_failures:
        print(f"adapter event stream warning: {failure}", file=sys.stderr)
    for failure in readable_failures:
        print(f"adapter event stream failed: {failure}", file=sys.stderr)
    return StreamStatus(
        activity_ok=not raw_failures,
        log_ok=not readable_failures,
        terminal_record=terminal_record,
        plain_diagnostics=tuple(plain_diagnostics),
        usage=usage_totals.as_payload(adapter_name),
    )


def main(argv: list[str]) -> int:
    if len(argv) != 3 or argv[0] not in _ADAPTER_NAMES:
        print(
            "usage: event_stream.py {claude|codex|copilot|opencode|pi} ACTIVITY_JSONL LOG_FILE",
            file=sys.stderr,
        )
        return 2
    try:
        status = stream_events(argv[0], Path(argv[1]), Path(argv[2]))
    except OSError as exc:
        print(f"adapter event stream failed: {exc}", file=sys.stderr)
        return 1
    return 0 if status.log_ok else 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
