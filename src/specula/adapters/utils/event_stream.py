"""Tee adapter JSONL into activity, readable, and usage logs.

The `.activity.jsonl` sidecar holds the useful adapter event stream, minus
tool-result echo records (see `_is_tool_echo`). Pi's cumulative
`message_update` snapshots are reduced to their incremental event before they
are persisted. Non-JSON diagnostics still reach the sidecar and readable log.
"""

from __future__ import annotations

import contextlib
import json
import re
import sys
from collections.abc import Callable, Iterable
from dataclasses import dataclass
from pathlib import Path
from typing import BinaryIO, TextIO, cast

from .text import SUMMARY_LIMIT, readable, readable_fragment, summary, tool_summary
from .usage import PiSubagentResult, UsageTotals, accumulate_usage, pi_subagent_results


@dataclass(frozen=True)
class StreamStatus:
    activity_ok: bool
    log_ok: bool
    terminal_record: object | None
    structured_error: str | None
    rate_limit_error: str | None
    terminal_error: str | None
    plain_diagnostics: tuple[str, ...]
    subagent_results: tuple[PiSubagentResult, ...]
    usage: dict[str, object]


@dataclass(frozen=True)
class _LogEvent:
    text: str = ""
    fragment: bool = False
    message_end: bool = False


_INVALID_RECORD = object()


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
    events = [_line_event(tool_summary(name, arguments))] if isinstance(name, str) else []
    if isinstance(state, dict) and state.get("status") == "error":
        error = _diagnostic_message(state.get("error"))
        if error:
            tool_name = summary(name, 60) if isinstance(name, str) else "tool"
            events.extend(_diagnostic_event("tool error", f"{tool_name}: {error}", concise))
    return events


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


_RATE_LIMIT_RE = re.compile(
    r"(?:\b429\b|rate[\s_-]*limit|too many requests|quota|resource[\s_-]*exhausted|"
    r"insufficient[\s_-]*quota)",
    re.IGNORECASE,
)


def _looks_rate_limited(value: object, depth: int = 0) -> bool:
    """Inspect only fields inside a structured provider error."""
    if depth > 3:
        return False
    if isinstance(value, str):
        return bool(_RATE_LIMIT_RE.search(value))
    if not isinstance(value, dict):
        return False
    for key in ("statusCode", "status_code", "status"):
        status_code = value.get(key)
        if status_code == 429 or status_code == "429":
            return True
    for key in ("name", "type", "code", "message", "errorMessage", "responseBody"):
        if _looks_rate_limited(value.get(key), depth + 1):
            return True
    return any(_looks_rate_limited(value.get(key), depth + 1) for key in ("data", "error"))


def _structured_rate_limit_error(adapter_name: str, record: object) -> str | None:
    """Return a diagnostic only for an explicit provider-error record."""
    if not isinstance(record, dict):
        return None
    if adapter_name == "opencode" and record.get("type") == "error":
        error = record.get("error")
        if not _looks_rate_limited(error):
            return None
        message = _diagnostic_message(error)
        if isinstance(error, dict):
            message = _diagnostic_message(error.get("data")) or message
            name = error.get("name")
            if not message and isinstance(name, str):
                message = name
        return summary(message or "provider rate limit", None)
    if adapter_name != "pi":
        return None
    terminal_error = _pi_terminal_error(record)
    if terminal_error is not None and _looks_rate_limited(terminal_error):
        return terminal_error
    if record.get("type") == "error":
        error = record.get("error")
        if _looks_rate_limited(record):
            diagnostic = _diagnostic_message(error) or _diagnostic_message(record)
            return summary(diagnostic or "provider rate limit", None)
    return None


def _terminal_error(adapter_name: str, record: object | None) -> str | None:
    """Reject streams that end between agent turns instead of completing."""
    if adapter_name == "opencode":
        if not isinstance(record, dict):
            return "stream ended without an OpenCode step_finish event"
        part = record.get("part")
        reason = part.get("reason") if isinstance(part, dict) else None
        if not isinstance(reason, str) or reason.casefold() != "stop":
            detail = summary(str(reason), 60) if reason is not None else "missing"
            return f"final OpenCode step_finish reason was {detail}; expected stop"
    elif adapter_name == "pi":
        if not isinstance(record, dict):
            return "stream ended without a Pi assistant message_end event"
        message = record.get("message")
        reason = message.get("stopReason") if isinstance(message, dict) else None
        if not isinstance(reason, str) or reason.casefold() != "stop":
            detail = summary(str(reason), 60) if reason is not None else "missing"
            return f"final Pi assistant stopReason was {detail}; expected stop"
    return None


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
            return [_LogEvent(text=readable_fragment(delta), fragment=True)]
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
            # Pi usually streams text_delta records first, but some providers
            # populate only the terminal message. The stream handler uses this
            # full text strictly as a fallback when it saw no deltas.
            text = _pi_message_text(message)
            return [_LogEvent(text=readable(text) if text else "", message_end=True)]
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


def _read_line(adapter_name: str, line: str, concise: bool) -> tuple[bool, list[_LogEvent], object]:
    """One line -> (persist raw?, readable events, parsed record or sentinel).

    Never raises on malformed input: a line that is not JSON is the CLI's own
    diagnostic, and losing it is worse than showing it."""
    try:
        record = json.loads(line)
    except (TypeError, ValueError):
        text = summary(line, SUMMARY_LIMIT if concise else None)
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
    pi_message_had_fragments = False
    line_open = False
    terminal_record: object | None = None
    structured_error: str | None = None
    rate_limit_error: str | None = None
    plain_diagnostics: list[str] = []
    subagent_results: list[PiSubagentResult] = []
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
        nonlocal fragment_active, last_event, line_open, pi_message_had_fragments
        nonlocal rate_limit_error, structured_error, terminal_record
        decoded = raw_line.decode(errors="replace")
        keep, events, record = _read_line(adapter_name, decoded, concise=False)
        accumulate_usage(adapter_name, record, usage_totals)
        if adapter_name == "claude-code":
            if isinstance(record, dict) and record.get("type") == "result":
                terminal_record = record
            elif record is _INVALID_RECORD and decoded.strip():
                # Claude's stream-json mode uses non-JSON only for CLI
                # diagnostics. Retain those few lines so quota banners survive
                # an activity-sidecar failure without buffering the full stream.
                plain_diagnostics.append(decoded)
        elif adapter_name == "opencode":
            detected_rate_limit = _structured_rate_limit_error(adapter_name, record)
            if detected_rate_limit is not None:
                rate_limit_error = detected_rate_limit
            if isinstance(record, dict) and record.get("type") == "step_finish":
                terminal_record = record
        elif adapter_name == "pi":
            if (
                isinstance(record, dict)
                and record.get("type") == "message_end"
                and isinstance(record.get("message"), dict)
                and record["message"].get("role") == "assistant"
            ):
                terminal_record = record
                structured_error = _pi_terminal_error(record)
                rate_limit_error = _structured_rate_limit_error(adapter_name, record)
            elif isinstance(record, dict) and record.get("type") == "error":
                detected_rate_limit = _structured_rate_limit_error(adapter_name, record)
                if detected_rate_limit is not None:
                    rate_limit_error = detected_rate_limit
            child_results = pi_subagent_results(record)
            subagent_results.extend(child_results)
        if keep and not raw_already_written:
            write_raw(_compact_activity_line(adapter_name, record, raw_line))
        for event in events:
            if event.message_end:
                if fragment_active:
                    if line_open:
                        write_readable("\n")
                if not pi_message_had_fragments and event.text:
                    last_event = event.text
                    write_readable(event.text.rstrip("\n") + "\n")
                fragment_active = False
                pi_message_had_fragments = False
                line_open = False
                continue
            if event.fragment:
                if not event.text:
                    continue
                last_event = ""
                fragment_active = True
                if adapter_name == "pi":
                    pi_message_had_fragments = True
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
        rate_limit_error=rate_limit_error,
        terminal_error=_terminal_error(adapter_name, terminal_record),
        plain_diagnostics=tuple(plain_diagnostics),
        subagent_results=tuple(subagent_results),
        usage=usage_totals.as_payload(adapter_name),
    )


def main(argv: list[str]) -> int:
    if len(argv) != 3 or argv[0] not in _ADAPTER_NAMES:
        print(
            "usage: specula _adapter event-stream {claude|codex|copilot|opencode|pi} ACTIVITY_JSONL LOG_FILE",
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
