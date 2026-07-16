"""Provider-policy error classification shared by every agent adapter."""

from __future__ import annotations

import json
import re
from pathlib import Path

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


def final_diagnostic_has_policy_block(text: str) -> bool:
    """Classify only a failed CLI's final non-empty diagnostic line."""
    diagnostic = next((line.strip() for line in reversed(text.splitlines()) if line.strip()), "")
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
    return looks_policy_blocked(diagnostic)


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
