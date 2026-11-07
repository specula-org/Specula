"""Provider-policy error classification shared by every agent adapter."""

from __future__ import annotations

import json
import re
from collections.abc import Mapping
from pathlib import Path

from .transient import looks_transient

# Dedicated adapter outcome consumed by the common phase runner. Keep it
# distinct from quota's EX_TEMPFAIL (75): a policy block needs a changed
# request immediately, not backoff followed by a replay.
POLICY_BLOCKED_RC = 76
# Internal event-stream outcome: a final out-of-band diagnostic looks like a
# policy block, but the wrapper must still confirm that the CLI itself failed.
# Adapters normalize this to POLICY_BLOCKED_RC; the phase runner never sees it.
PLAIN_POLICY_DIAGNOSTIC_RC = 77
_FAILED_LOG_SCAN_BYTES = 256 * 1024

_POLICY_CODES = {
    "content_filter",
    "content_filtering",
    "content_policy",
    "content_policy_violation",
    "content_policy_violation_error",
    "cyber_policy",
}
_POLICY_TEXT_RE = re.compile(
    r"(?:cyber[_\s-]*policy|content[_\s-]*policy|content filtering policy|"
    r"output blocked by content filtering|blocked by (?:the )?(?:model(?:'s)? )?content filter|"
    r"flagged for possible cybersecurity risk)",
    re.IGNORECASE,
)
# Claude Code's real-time safeguard diagnostic: "API Error: <model>'s
# safeguards flagged this message. ..." followed by a "Details: `[cyber]`"
# category line. Applied only on Claude Code paths.
_CLAUDE_SAFEGUARD_TEXT_RE = re.compile(r"safeguards flagged this message|details:\s*`?\[cyber\]`?", re.IGNORECASE)
# Correlation identifiers that Claude Code appends after that diagnostic
# ("Request ID: req_...", "Message ID: msg_..."). They carry no failure class,
# so the Claude Code fallback looks past them; any other trailing line still
# ends the backward scan.
_DIAGNOSTIC_ID_TRAILER_RE = re.compile(r"(?:request|message)[ _-]?id\s*[:=]\s*\S+", re.IGNORECASE)


def _normalized_code(value: str) -> str:
    return re.sub(r"[^a-z0-9]+", "_", value.casefold()).strip("_")


def looks_policy_blocked(value: object, depth: int = 0) -> bool:
    """Recognize a policy block inside an already identified error payload.

    Callers must first establish that ``value`` came from a provider/terminal
    error envelope. This intentionally does not decide whether arbitrary agent
    output is an error: an agent may quote an old policy message while fixing
    exactly this failure.
    """
    if depth > 4:
        return False
    if isinstance(value, str):
        return _normalized_code(value) in _POLICY_CODES or bool(_POLICY_TEXT_RE.search(value))
    if not isinstance(value, dict):
        return False

    for key in ("code", "errorCode", "error_code", "errorType", "error_type", "name", "type"):
        code = value.get(key)
        if isinstance(code, str) and _normalized_code(code) in _POLICY_CODES:
            return True
    for key in ("message", "errorMessage", "error_message", "responseBody", "response_body"):
        if looks_policy_blocked(value.get(key), depth + 1):
            return True
    return any(
        looks_policy_blocked(value.get(key), depth + 1) for key in ("data", "error", "cause", "body", "response")
    )


def looks_claude_safeguard_block(value: object) -> bool:
    """Recognize Claude Code's safeguard diagnostic in an identified error.

    Like ``looks_policy_blocked``, callers must first establish that ``value``
    is a failed Claude Code result or its failed CLI's final diagnostic.
    """
    return isinstance(value, str) and bool(_CLAUDE_SAFEGUARD_TEXT_RE.search(value))


def refusal_policy_block(record: Mapping[str, object]) -> bool:
    """Whether a failed Claude result is a provider safety refusal.

    Claude Code reports real-time safeguard blocks as a terminal ``result``
    whose ``stop_reason`` is ``"refusal"`` and which carries no API status; the
    accompanying text varies by model and CLI release. A refusal stop next to
    an API status (429, 5xx) or a transient transport diagnostic belongs to
    that failure instead, so rate-limit waits and transient backoff keep
    precedence and do not spend the policy budget. Callers must first establish
    that the result envelope itself failed: a successful turn is never
    reclassified.
    """
    stop_reason = record.get("stop_reason")
    if not isinstance(stop_reason, str) or stop_reason.casefold() != "refusal":
        return False
    if record.get("api_error_status") not in (None, "", 0, "0"):
        return False
    return not (looks_transient(record) or looks_transient(record.get("result")))


def _final_diagnostic_line(text: str, *, skip_id_trailers: bool) -> str:
    """The final non-empty line of ``text``, optionally past correlation IDs."""
    for line in reversed(text.splitlines()):
        line = line.strip()
        if line and not (skip_id_trailers and _DIAGNOSTIC_ID_TRAILER_RE.fullmatch(line)):
            return line
    return ""


def final_diagnostic_has_policy_block(text: str, *, claude: bool = False) -> bool:
    """Classify only a failed CLI's final non-empty diagnostic line.

    ``claude=True`` is for Claude Code's own out-of-band output: it also
    recognizes the safeguard diagnostic and looks past the Request ID /
    Message ID lines that follow it. Other fallbacks may scan an agent's
    transcript (Copilot text mode), where an ID line is not a CLI trailer.
    """
    diagnostic = _final_diagnostic_line(text, skip_id_trailers=claude)
    if not diagnostic:
        return False
    try:
        json.loads(diagnostic)
    except (TypeError, ValueError):
        pass
    else:
        # A valid JSON line belongs to an agent/event channel. Structured error
        # envelopes are classified by the adapter parser, not this fallback.
        return False
    return looks_policy_blocked(diagnostic) or (claude and looks_claude_safeguard_block(diagnostic))


def failed_log_has_policy_block(path: Path) -> bool:
    """Narrow fallback for a failed CLI run that could not emit JSON events."""
    try:
        with path.open("rb") as stream:
            stream.seek(0, 2)
            stream.seek(max(0, stream.tell() - _FAILED_LOG_SCAN_BYTES))
            text = stream.read(_FAILED_LOG_SCAN_BYTES).decode("utf-8", errors="replace")
    except OSError:
        return False
    return final_diagnostic_has_policy_block(text)
