"""Tee adapter JSONL into activity, readable, and usage logs.

The `.activity.jsonl` sidecar holds the useful adapter event stream, minus
tool-result echo records (see `_is_tool_echo`). Pi's cumulative
`message_update` snapshots are reduced to their incremental event before they
are persisted. Non-JSON diagnostics still reach the sidecar and readable log.
"""

from __future__ import annotations

import contextlib
import json
import math
import re
import stat
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
    structured_error: str | None
    plain_diagnostics: tuple[str, ...]
    session_files: tuple[str, ...]
    usage: dict[str, object]


@dataclass(frozen=True)
class _LogEvent:
    text: str = ""
    fragment: bool = False
    message_end: bool = False


@dataclass
class UsageTotals:
    session_id: str | None = None
    total_cost_usd: float | None = None
    input_tokens: int = 0
    cached_input_tokens: int = 0
    cache_write_input_tokens: int = 0
    output_tokens: int = 0
    reasoning_output_tokens: int = 0

    def add(self, other: UsageTotals) -> None:
        self.input_tokens += other.input_tokens
        self.cached_input_tokens += other.cached_input_tokens
        self.cache_write_input_tokens += other.cache_write_input_tokens
        self.output_tokens += other.output_tokens
        self.reasoning_output_tokens += other.reasoning_output_tokens
        if other.total_cost_usd is not None:
            self.total_cost_usd = (self.total_cost_usd or 0.0) + other.total_cost_usd

    def add_cost(self, value: object) -> None:
        if isinstance(value, (int, float)) and not isinstance(value, bool):
            try:
                cost = float(value)
            except OverflowError:
                return
            if cost >= 0 and math.isfinite(cost):
                self.total_cost_usd = (self.total_cost_usd or 0.0) + cost

    def as_payload(self, agent: str) -> dict[str, object]:
        return {
            "agent": agent,
            "session_id": self.session_id,
            "session_file": None,
            "total_cost_usd": self.total_cost_usd,
            "usage": self.as_usage(),
        }

    def as_usage(self) -> dict[str, int]:
        total = (
            self.input_tokens
            + self.cached_input_tokens
            + self.cache_write_input_tokens
            + self.output_tokens
            + self.reasoning_output_tokens
        )
        return {
            "input_tokens": self.input_tokens,
            "cached_input_tokens": self.cached_input_tokens,
            "cache_write_input_tokens": self.cache_write_input_tokens,
            "output_tokens": self.output_tokens,
            "reasoning_output_tokens": self.reasoning_output_tokens,
            "total_tokens": total,
        }

    @classmethod
    def from_payload(cls, payload: dict[str, object]) -> UsageTotals:
        totals = cls(session_id=payload.get("session_id") if isinstance(payload.get("session_id"), str) else None)
        totals.add_cost(payload.get("total_cost_usd"))
        usage = payload.get("usage")
        if isinstance(usage, dict):
            totals.input_tokens = _token_count(usage.get("input_tokens"))
            totals.cached_input_tokens = _token_count(usage.get("cached_input_tokens"))
            totals.cache_write_input_tokens = _token_count(usage.get("cache_write_input_tokens"))
            totals.output_tokens = _token_count(usage.get("output_tokens"))
            totals.reasoning_output_tokens = _token_count(usage.get("reasoning_output_tokens"))
        return totals


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


def _readable_fragment(text: str) -> str:
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


def _line_event(text: str) -> _LogEvent:
    return _LogEvent(text=text)


def _text_event(text: str, concise: bool) -> _LogEvent:
    return _line_event(summary(text) if concise else readable(text))


def _diagnostic_message(value: object) -> str:
    """Extract the human-readable part of a structured adapter error."""
    if isinstance(value, str):
        return value
    if isinstance(value, dict):
        message = value.get("message")
        if isinstance(message, str):
            return message
    return ""


def _diagnostic_event(kind: str, message: str, concise: bool) -> list[_LogEvent]:
    text = _text_event(message, concise).text
    return [_line_event(f"adapter {kind}: {text}")] if text else []


def _claude_events(record: object, concise: bool) -> list[_LogEvent]:
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
    events: list[_LogEvent] = []
    for block in content:
        if not isinstance(block, dict):
            continue
        text = block.get("text")
        name = block.get("name")
        if block.get("type") == "text" and isinstance(text, str):
            events.append(_text_event(text, concise))
        elif block.get("type") == "tool_use" and isinstance(name, str):
            events.append(_line_event(tool_summary(name, block.get("input"))))
    return events


def _copilot_events(record: object, concise: bool) -> list[_LogEvent]:
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
        return [_line_event(tool_summary(tool_name, data.get("arguments")))]
    return []


def _codex_events(record: object, concise: bool) -> list[_LogEvent]:
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
        return [_line_event(tool_summary(item_type, {"command": item.get("command")}))]
    if item_type in {"mcp_tool_call", "web_search"}:
        name = item.get("tool") or item_type
        return [_line_event(tool_summary(str(name), item.get("arguments")))]
    return []


def _opencode_events(record: object, concise: bool) -> list[_LogEvent]:
    if not isinstance(record, dict):
        return []
    if record.get("type") == "error":
        error = record.get("error")
        message = _diagnostic_message(error)
        if isinstance(error, dict):
            message = _diagnostic_message(error.get("data")) or message
            name = error.get("name")
            if not message and isinstance(name, str):
                message = name
        return _diagnostic_event("error", message, concise)
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
    return [_line_event(tool_summary(name, arguments))] if isinstance(name, str) else []


def _pi_message_text(message: object) -> str:
    if not isinstance(message, dict) or message.get("role") != "assistant":
        return ""
    content = message.get("content")
    if isinstance(content, str):
        return content
    if not isinstance(content, list):
        return ""
    return "".join(
        text
        for block in content
        if isinstance(block, dict) and block.get("type") == "text" and isinstance((text := block.get("text")), str)
    )


def _pi_terminal_error(record: object) -> str | None:
    if not isinstance(record, dict) or record.get("type") != "message_end":
        return None
    message = record.get("message")
    if not isinstance(message, dict) or message.get("role") != "assistant":
        return None
    reason = message.get("stopReason")
    if not isinstance(reason, str) or reason.casefold() not in {"error", "aborted"}:
        return None
    detail = message.get("errorMessage")
    if not isinstance(detail, str) or not detail.strip():
        detail = f"assistant stopped with stopReason {reason}"
    return summary(detail, None)


def _pi_events(record: object, concise: bool) -> list[_LogEvent]:
    if not isinstance(record, dict):
        return []
    record_type = record.get("type")
    if record_type == "error" or record_type == "warning":
        nested = record.get(record_type)
        diagnostic = _diagnostic_message(nested) or _diagnostic_message(record)
        return _diagnostic_event(record_type, diagnostic, concise)
    if record_type == "message_update":
        update = record.get("assistantMessageEvent")
        if isinstance(update, dict) and update.get("type") == "text_delta":
            delta = update.get("delta")
            if not isinstance(delta, str) or concise:
                return []
            return [_LogEvent(text=_readable_fragment(delta), fragment=True)]
        return []
    if record_type == "message_end":
        message = record.get("message")
        if not isinstance(message, dict) or message.get("role") != "assistant":
            return []
        terminal_error = _pi_terminal_error(record)
        if terminal_error:
            events = _diagnostic_event("error", terminal_error, concise)
            if not concise:
                events.append(_LogEvent(message_end=True))
            return events
        if not concise:
            return [_LogEvent(message_end=True)]
        text = _pi_message_text(message)
        return [_text_event(text, concise=True)] if text else []
    if record_type == "tool_execution_start":
        name = record.get("toolName")
        return [_line_event(tool_summary(name, record.get("args")))] if isinstance(name, str) else []
    return []


_PARSERS: dict[str, Callable[[object, bool], list[_LogEvent]]] = {
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


def _read_pi_session_usage(path: Path) -> tuple[UsageTotals, list[str]] | None:
    """Read one persisted Pi child session without retaining its messages."""
    try:
        metadata = path.lstat()
        if not stat.S_ISREG(metadata.st_mode) or path.is_symlink():
            return None
        stream = path.open(encoding="utf-8", errors="replace")
    except OSError as exc:
        print(f"adapter usage warning: {summary(str(exc), None)}", file=sys.stderr)
        return None

    totals = UsageTotals()
    nested_paths: list[str] = []
    header_seen = False
    try:
        with stream:
            for line in stream:
                try:
                    record = json.loads(line)
                except (TypeError, ValueError):
                    continue
                if not header_seen:
                    if not isinstance(record, dict) or record.get("type") != "session":
                        return None
                    header_seen = True
                    session_id = record.get("id")
                    if isinstance(session_id, str):
                        totals.session_id = session_id
                    continue
                if not isinstance(record, dict) or record.get("type") != "message":
                    continue
                message = record.get("message")
                if not isinstance(message, dict):
                    continue
                if message.get("role") == "assistant":
                    _accumulate_usage("pi", {"type": "message_end", "message": message}, totals)
                elif message.get("role") == "toolResult" and message.get("toolName") == "subagent":
                    nested_paths.extend(_find_session_paths(message.get("details")))
    except OSError as exc:
        print(f"adapter usage warning: {summary(str(exc), None)}", file=sys.stderr)
        return None
    return (totals, nested_paths) if header_seen else None


def augment_pi_usage(
    parent_payload: dict[str, object],
    session_files: Iterable[str | Path],
    session_root: Path | None = None,
) -> dict[str, object]:
    """Add per-child and combined Pi usage while preserving top-level readers."""
    pending = [Path(path) for path in session_files]
    if session_root is not None:
        with contextlib.suppress(OSError):
            pending.extend(session_root.rglob("session.jsonl"))

    seen: set[Path] = set()
    sessions: list[dict[str, object]] = []
    subagent_totals = UsageTotals()
    while pending:
        candidate = pending.pop()
        try:
            resolved = candidate.expanduser().resolve()
        except OSError:
            continue
        if resolved in seen:
            continue
        seen.add(resolved)
        result = _read_pi_session_usage(resolved)
        if result is None:
            continue
        totals, nested_paths = result
        pending.extend(Path(path) for path in nested_paths)
        subagent_totals.add(totals)
        session_payload = totals.as_payload("pi")
        session_payload.pop("agent", None)
        session_payload.pop("session_file", None)
        sessions.append(session_payload)

    sessions.sort(key=lambda item: str(item.get("session_id") or ""))
    parent_totals = UsageTotals.from_payload(parent_payload)
    combined_totals = UsageTotals(session_id=parent_totals.session_id)
    combined_totals.add(parent_totals)
    combined_totals.add(subagent_totals)
    combined_payload = combined_totals.as_payload("pi")
    combined_payload.update(
        {
            "usage_scope": "combined",
            "parent": {
                "session_id": parent_totals.session_id,
                "total_cost_usd": parent_totals.total_cost_usd,
                "usage": parent_totals.as_usage(),
            },
            "subagents": {
                "session_count": len(sessions),
                "total_cost_usd": subagent_totals.total_cost_usd,
                "usage": subagent_totals.as_usage(),
                "sessions": sessions,
            },
            "combined": {
                "total_cost_usd": combined_totals.total_cost_usd,
                "usage": combined_totals.as_usage(),
            },
        }
    )
    return combined_payload


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


def _compact_activity_line(adapter_name: str, record: object, raw_line: bytes) -> bytes:
    """Drop Pi's repeated cumulative message while retaining live deltas."""
    if not isinstance(record, dict) or adapter_name != "pi" or record.get("type") != "message_update":
        return raw_line
    compact: dict[str, object] = {"type": "message_update"}
    update = record.get("assistantMessageEvent")
    if isinstance(update, dict):
        compact_update = {
            key: value
            for key in ("type", "contentIndex", "delta")
            if (value := update.get(key)) is not None and isinstance(value, (str, int, float, bool))
        }
        if compact_update:
            compact["assistantMessageEvent"] = compact_update
    newline = b"\n" if raw_line.endswith(b"\n") else b""
    return json.dumps(compact, ensure_ascii=False, separators=(",", ":")).encode() + newline


def _find_session_paths(value: object) -> list[str]:
    found: list[str] = []

    def visit(node: object) -> None:
        if isinstance(node, dict):
            for key, nested in node.items():
                if key in {"sessionFile", "sessionPath"} and isinstance(nested, str) and nested:
                    found.append(nested)
                else:
                    visit(nested)
        elif isinstance(node, list):
            for nested in node:
                visit(nested)

    visit(value)
    return found


def _session_files_from_subagent_result(record: object) -> list[str]:
    """Extract only Pi subagent-owned session paths from a tool result."""
    if (
        not isinstance(record, dict)
        or record.get("type") != "tool_execution_end"
        or record.get("toolName") != "subagent"
    ):
        return []
    result = record.get("result")
    details = result.get("details") if isinstance(result, dict) else None
    return _find_session_paths(details)


def _read_line(adapter_name: str, line: str, concise: bool) -> tuple[bool, list[_LogEvent], object]:
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
            return True, [_line_event(text)] if text else [], _INVALID_RECORD
        is_error = any(term in text.casefold() for term in ("error", "failed", "require", "invalid", "unknown"))
        if text and (is_error or not concise):
            return True, [_line_event(f"adapter error: {text}" if is_error else text)], _INVALID_RECORD
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
        events.extend(event.text for event in _read_line(adapter_name, line, concise)[1] if event.text)
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
    fragment_active = False
    line_open = False
    terminal_record: object | None = None
    structured_error: str | None = None
    plain_diagnostics: list[str] = []
    session_files: list[str] = []
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

    def write_readable(data: str) -> None:
        nonlocal log
        if not data or log is None:
            return
        try:
            log.write(data)
            log.flush()
        except OSError as exc:
            readable_failures.append(f"readable log {log_path}: {exc}")
            with contextlib.suppress(OSError):
                log.close()
            log = None

    def handle_line(raw_line: bytes, *, raw_already_written: bool) -> None:
        nonlocal fragment_active, last_event, line_open, structured_error, terminal_record
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
        elif adapter_name == "pi":
            if (
                isinstance(record, dict)
                and record.get("type") == "message_end"
                and isinstance(record.get("message"), dict)
                and record["message"].get("role") == "assistant"
            ):
                terminal_record = record
                structured_error = _pi_terminal_error(record)
            session_files.extend(_session_files_from_subagent_result(record))
        if keep and not raw_already_written:
            write_raw(_compact_activity_line(adapter_name, record, raw_line))
        for event in events:
            if event.message_end:
                if fragment_active and line_open:
                    write_readable("\n")
                fragment_active = False
                line_open = False
                continue
            if event.fragment:
                if not event.text:
                    continue
                last_event = ""
                fragment_active = True
                write_readable(event.text)
                line_open = not event.text.endswith("\n")
                continue
            if not event.text or event.text == last_event:
                continue
            if fragment_active and line_open:
                write_readable("\n")
            fragment_active = False
            line_open = False
            last_event = event.text
            write_readable(event.text.rstrip("\n") + "\n")

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
        structured_error=structured_error,
        plain_diagnostics=tuple(plain_diagnostics),
        session_files=tuple(dict.fromkeys(session_files)),
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
