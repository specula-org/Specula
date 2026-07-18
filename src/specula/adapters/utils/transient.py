"""Narrow classification for retryable provider and transport failures.

Adapters use a dedicated result code so the phase runner can resume the exact
native session instead of replaying an entire phase.  Arbitrary agent text is
never classified here: callers must first establish that the value came from a
provider error envelope, or that it is the final diagnostic of a failed CLI.
"""

from __future__ import annotations

import json
import re
from pathlib import Path

TRANSIENT_FAILURE_RC = 74
# Like policy's plain-diagnostic code, this is private to an adapter wrapper.
# The wrapper may normalize it only after confirming that the native CLI failed.
PLAIN_TRANSIENT_DIAGNOSTIC_RC = 78
_FAILED_LOG_SCAN_BYTES = 256 * 1024

_TRANSIENT_CODES = {
    "api_connection_error",
    "api_timeout_error",
    "connection_error",
    "eai_again",
    "econnaborted",
    "econnrefused",
    "econnreset",
    "ehostunreach",
    "enetdown",
    "enetreset",
    "enetunreach",
    "epipe",
    "etimedout",
    "engine_overloaded",
    "fetch_failed",
    "internal_server_error",
    "model_at_capacity",
    "network_error",
    "overloaded",
    "overloaded_error",
    "request_timeout",
    "server_error",
    "service_unavailable",
    "socket_hang_up",
    "temporarily_unavailable",
    "timeout",
    "transport_error",
    "und_err_connect_timeout",
    "und_err_socket",
}
_TRANSIENT_TEXT_RE = re.compile(
    r"(?:\bhttp(?:\s+status)?\s*[:=]?\s*(?:500|502|503|504|529)\b|"
    r"\bstatus(?:\s+code)?\s*[:=]?\s*(?:500|502|503|504|529)\b|"
    r"\bapi\s+error\s*[:=-]?\s*(?:500|502|503|504|529)\b|"
    r"selected model is at capacity|model (?:is )?at capacity|"
    r"(?:server|service|provider|model) (?:is )?(?:temporarily )?unavailable|"
    r"internal server error|overloaded[_\s-]*error|(?:server|model) overloaded|"
    r"upstream (?:request )?(?:timed out|timeout|connect error)|"
    r"request (?:timed out|timeout)|gateway (?:timed out|timeout)|"
    r"connection (?:reset|closed|refused|terminated)|"
    r"transport (?:error|closed)|network error|socket hang up|fetch failed|"
    r"\b(?:eai_again|econnaborted|econnrefused|econnreset|ehostunreach|"
    r"enetdown|enetreset|enetunreach|epipe|etimedout|und_err_connect_timeout|und_err_socket)\b)",
    re.IGNORECASE,
)

# Plain output lacks the trusted provider-error envelope available to
# ``looks_transient``. Require the final CLI diagnostic to start like an
# operational error, so agent prose such as "the test expects HTTP 503" cannot
# turn an unrelated native failure into repeated resume attempts.
_PLAIN_TRANSIENT_DIAGNOSTIC_RE = re.compile(
    r"^\s*(?:(?:error|fatal)(?:\[[^\]]+\])?\s*[:=-]\s*)?(?:"
    r"(?:http(?:\s+status)?|status(?:\s+code)?|api\s+error)\s*[:=]?\s*(?:500|502|503|504|529)\b|"
    r"selected model is at capacity\b|model (?:is )?at capacity\b|"
    r"(?:server|service|provider|model) (?:is )?(?:temporarily )?unavailable\b|"
    r"internal server error\b|overloaded[_\s-]*error\b|(?:server|model) overloaded\b|"
    r"upstream (?:request )?(?:timed out|timeout|connect error)\b|"
    r"request (?:timed out|timeout)\b|gateway (?:timed out|timeout)\b|"
    r"connection (?:reset|closed|refused|terminated)\b|"
    r"transport (?:error|closed)\b|network error\b|socket hang up\b|fetch failed\b|"
    r"(?:(?:read|write|connect|getaddrinfo)\s+)?(?:eai_again|econnaborted|econnrefused|econnreset|ehostunreach|"
    r"enetdown|enetreset|enetunreach|epipe|etimedout|und_err_connect_timeout|und_err_socket)\b"
    r")",
    re.IGNORECASE,
)


def _normalized_code(value: str) -> str:
    value = re.sub(r"([A-Z]+)([A-Z][a-z])", r"\1_\2", value)
    value = re.sub(r"([a-z0-9])([A-Z])", r"\1_\2", value)
    return re.sub(r"[^a-z0-9]+", "_", value.casefold()).strip("_")


def _is_transient_code(value: str) -> bool:
    normalized = _normalized_code(value)
    return normalized in _TRANSIENT_CODES or normalized.removesuffix("_error") in _TRANSIENT_CODES


def looks_transient(value: object, depth: int = 0) -> bool:
    """Recognize a transient failure inside an identified error payload."""
    if depth > 4:
        return False
    if isinstance(value, str):
        return _is_transient_code(value) or bool(_TRANSIENT_TEXT_RE.search(value))
    if not isinstance(value, dict):
        return False

    for key in ("statusCode", "status_code", "status"):
        status = value.get(key)
        if status in {500, 502, 503, 504, 529, "500", "502", "503", "504", "529"}:
            return True
    for key in ("code", "errorCode", "error_code", "errorType", "error_type", "name", "type"):
        code = value.get(key)
        if isinstance(code, str) and _is_transient_code(code):
            return True
    for key in ("message", "errorMessage", "error_message", "responseBody", "response_body"):
        if looks_transient(value.get(key), depth + 1):
            return True
    return any(looks_transient(value.get(key), depth + 1) for key in ("data", "error", "cause", "body", "response"))


def final_diagnostic_has_transient_failure(text: str) -> bool:
    """Classify only a failed CLI's final non-empty, non-JSON diagnostic."""
    diagnostic = next((line.strip() for line in reversed(text.splitlines()) if line.strip()), "")
    if not diagnostic:
        return False
    try:
        json.loads(diagnostic)
    except (TypeError, ValueError):
        return bool(_PLAIN_TRANSIENT_DIAGNOSTIC_RE.search(diagnostic))
    return False


def failed_log_has_transient_failure(path: Path) -> bool:
    """Narrow fallback for a failed CLI run that could not emit JSON events."""
    try:
        with path.open("rb") as stream:
            stream.seek(0, 2)
            stream.seek(max(0, stream.tell() - _FAILED_LOG_SCAN_BYTES))
            text = stream.read(_FAILED_LOG_SCAN_BYTES).decode("utf-8", errors="replace")
    except OSError:
        return False
    return final_diagnostic_has_transient_failure(text)
