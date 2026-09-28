"""Read cumulative Copilot CLI token usage without exporting session content."""

from __future__ import annotations

import contextlib
import json
import os
import sqlite3
import sys
import tempfile
from collections.abc import Mapping
from pathlib import Path

from .text import summary

_REQUIRED_COLUMNS = frozenset(
    {
        "session_id",
        "model",
        "copilot_usage_model",
        "input_tokens",
        "output_tokens",
        "cache_read_tokens",
        "cache_write_tokens",
        "reasoning_tokens",
        "total_nano_aiu",
        "duration_ms",
    }
)
_NANO_AIU_PER_AI_CREDIT = 1_000_000_000
_NANO_AIU_PER_USD = 100_000_000_000


def database_path(environment: Mapping[str, str]) -> Path | None:
    root = environment.get("COPILOT_HOME")
    if not root:
        home = environment.get("HOME")
        if not home:
            return None
        root = str(Path(home) / ".copilot")
    return Path(root) / "session-store.db"


def _empty_payload(session_id: str | None, warning: str) -> dict[str, object]:
    return {
        "agent": "copilot-cli",
        "session_id": session_id,
        "total_cost_usd": None,
        "usage": {},
        "usage_complete": False,
        "usage_scope": "unavailable",
        "usage_warning": warning,
    }


def _nonnegative(value: object) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value < 0:
        raise ValueError("Copilot usage database contains an invalid token count")
    return value


def _open_read_only(path: Path) -> sqlite3.Connection:
    resolved = path.resolve(strict=True)
    connection = sqlite3.connect(f"{resolved.as_uri()}?mode=ro", uri=True)
    connection.execute("PRAGMA query_only = ON")
    connection.execute("PRAGMA busy_timeout = 5000")
    return connection


def collect_usage(session_id: str | None, path: Path | None) -> dict[str, object]:
    if not session_id:
        return _empty_payload(None, "Copilot session ID unavailable; token usage was not collected")
    if path is None:
        return _empty_payload(session_id, "Copilot home directory unavailable; token usage was not collected")
    try:
        with _open_read_only(path) as connection:
            columns = {str(row[1]) for row in connection.execute("PRAGMA table_info(assistant_usage_events)")}
            if not _REQUIRED_COLUMNS.issubset(columns):
                return _empty_payload(session_id, "Copilot usage database schema is unsupported")
            rows = list(
                connection.execute(
                    """
                    SELECT
                        COALESCE(copilot_usage_model, model) AS usage_model,
                        COUNT(*) AS request_count,
                        SUM(input_tokens) AS input_tokens,
                        SUM(output_tokens) AS output_tokens,
                        SUM(cache_read_tokens) AS cache_read_tokens,
                        SUM(cache_write_tokens) AS cache_write_tokens,
                        SUM(COALESCE(reasoning_tokens, 0)) AS reasoning_tokens,
                        SUM(COALESCE(total_nano_aiu, 0)) AS total_nano_aiu,
                        SUM(COALESCE(duration_ms, 0)) AS duration_ms,
                        SUM(
                            CASE
                                WHEN input_tokens IS NULL
                                  OR output_tokens IS NULL
                                  OR cache_read_tokens IS NULL
                                  OR cache_write_tokens IS NULL
                                  OR total_nano_aiu IS NULL
                                  OR input_tokens < 0
                                  OR output_tokens < 0
                                  OR cache_read_tokens < 0
                                  OR cache_write_tokens < 0
                                  OR COALESCE(reasoning_tokens, 0) < 0
                                  OR total_nano_aiu < 0
                                  OR input_tokens < cache_read_tokens + cache_write_tokens
                                THEN 1 ELSE 0
                            END
                        ) AS invalid_rows,
                        SUM(CASE WHEN reasoning_tokens IS NULL THEN 1 ELSE 0 END) AS missing_reasoning_rows
                    FROM assistant_usage_events
                    WHERE session_id = ?
                    GROUP BY COALESCE(copilot_usage_model, model)
                    ORDER BY usage_model
                    """,
                    (session_id,),
                )
            )
    except (OSError, sqlite3.Error) as exc:
        return _empty_payload(session_id, f"Copilot usage database unavailable: {summary(str(exc), None)}")

    if not rows:
        return _empty_payload(session_id, "Copilot usage database has no events for this session")

    input_tokens = 0
    cached_input_tokens = 0
    cache_write_input_tokens = 0
    output_tokens = 0
    reasoning_output_tokens = 0
    total_nano_aiu = 0
    duration_ms = 0
    request_count = 0
    missing_reasoning_rows = 0
    model_usage: dict[str, object] = {}
    for row in rows:
        model = row[0]
        if not isinstance(model, str) or not model:
            return _empty_payload(session_id, "Copilot usage database contains an invalid model identifier")
        try:
            (
                model_requests,
                model_input,
                model_output,
                model_cached,
                model_cache_write,
                model_reasoning,
                model_nano_aiu,
                model_duration,
                invalid_rows,
                model_missing_reasoning,
            ) = (_nonnegative(value) for value in row[1:])
        except ValueError as exc:
            return _empty_payload(session_id, str(exc))
        if invalid_rows:
            return _empty_payload(session_id, "Copilot usage database contains incomplete or inconsistent billing data")
        model_uncached = model_input - model_cached - model_cache_write
        model_ai_credits = model_nano_aiu / _NANO_AIU_PER_AI_CREDIT
        request_count += model_requests
        input_tokens += model_uncached
        cached_input_tokens += model_cached
        cache_write_input_tokens += model_cache_write
        output_tokens += model_output
        reasoning_output_tokens += model_reasoning
        total_nano_aiu += model_nano_aiu
        duration_ms += model_duration
        missing_reasoning_rows += model_missing_reasoning
        model_usage[model] = {
            "request_count": model_requests,
            "input_tokens": model_uncached,
            "cached_input_tokens": model_cached,
            "cache_write_input_tokens": model_cache_write,
            "output_tokens": model_output,
            "reasoning_output_tokens": model_reasoning,
            "total_tokens": model_input + model_output,
            "total_nano_aiu": model_nano_aiu,
            "ai_credits": model_ai_credits,
            "total_cost_usd": model_nano_aiu / _NANO_AIU_PER_USD,
            "duration_ms": model_duration,
        }

    ai_credits = total_nano_aiu / _NANO_AIU_PER_AI_CREDIT
    payload: dict[str, object] = {
        "agent": "copilot-cli",
        "session_id": session_id,
        "total_cost_usd": total_nano_aiu / _NANO_AIU_PER_USD,
        "usage": {
            "input_tokens": input_tokens,
            "cached_input_tokens": cached_input_tokens,
            "cache_write_input_tokens": cache_write_input_tokens,
            "output_tokens": output_tokens,
            "reasoning_output_tokens": reasoning_output_tokens,
            "total_tokens": input_tokens + cached_input_tokens + cache_write_input_tokens + output_tokens,
        },
        "usage_complete": True,
        "usage_scope": "session_cumulative",
        "request_count": request_count,
        "total_nano_aiu": total_nano_aiu,
        "ai_credits": ai_credits,
        "duration_ms": duration_ms,
        "model_usage": model_usage,
    }
    if missing_reasoning_rows:
        payload["reasoning_usage_complete"] = False
        payload["usage_warning"] = (
            f"{missing_reasoning_rows} Copilot usage event(s) omitted reasoning-token telemetry; "
            "total tokens remain complete because Copilot output tokens include reasoning"
        )
    else:
        payload["reasoning_usage_complete"] = True
    return payload


def write_usage(path: Path, payload: dict[str, object]) -> None:
    temporary: Path | None = None
    try:
        path.parent.mkdir(parents=True, exist_ok=True)
        fd, raw_path = tempfile.mkstemp(prefix=f".{path.name}.", suffix=".tmp", dir=path.parent)
        temporary = Path(raw_path)
        with os.fdopen(fd, "w", encoding="utf-8") as stream:
            json.dump(payload, stream, indent=2, sort_keys=True)
            stream.write("\n")
        os.replace(temporary, path)
        temporary = None
    finally:
        if temporary is not None:
            with contextlib.suppress(OSError):
                temporary.unlink()


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print("usage: python -m specula.adapters.utils.copilot_usage SESSION_ID LOG_FILE", file=sys.stderr)
        return 2
    session_id = argv[0] or None
    usage_path = Path(argv[1]).with_suffix(".usage.json")
    payload = collect_usage(session_id, database_path(os.environ))
    try:
        write_usage(usage_path, payload)
    except OSError as exc:
        print(f"copilot-cli adapter: usage write failed: {summary(str(exc), None)}", file=sys.stderr)
        return 1
    warning = payload.get("usage_warning")
    if isinstance(warning, str):
        print(f"copilot-cli adapter: usage warning: {warning}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
