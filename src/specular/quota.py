"""Shared quota gating and reactive rate-limit backoff."""

from __future__ import annotations

import json
import os
import re
import subprocess
import time
from collections.abc import Callable
from datetime import datetime
from pathlib import Path

RATE_LIMIT_RC = 75
RATE_LIMIT_RETRIES = 2
QUOTA_POLL_FALLBACK_SECONDS = 600.0
RATE_LIMIT_FALLBACK_SECONDS = 3600.0


def quota_check(usage_json: str, q5: str, q7: str) -> str | None:
    """Return ``ok``, the first over-limit window, or None on bad input."""
    try:
        payload = json.loads(usage_json)
        windows = (
            ("5h", "five_hour", q5),
            ("7d", "seven_day", q7),
            ("7d_opus", "seven_day_opus", q7),
            ("7d_sonnet", "seven_day_sonnet", q7),
        )
        for label, key, threshold in windows:
            window = payload.get(key) or {}
            utilization = window.get("utilization", 0) or 0
            if utilization > float(threshold):
                return f"{label}={utilization}% (limit {threshold}%) resets_at={window.get('resets_at', '')}"
        return "ok"
    except Exception:
        return None


def _epoch(timestamp: str) -> int:
    try:
        return int(datetime.fromisoformat(timestamp.replace("Z", "+00:00")).timestamp())
    except ValueError:
        return 0


def _sleep_fallback(
    *,
    reason: str,
    fallback_seconds: float,
    sleep_fn: Callable[[float], object],
    log_fn: Callable[[str], object],
) -> None:
    seconds = max(0.0, fallback_seconds)
    log_fn(f"{reason}; sleeping {seconds:g}s after rate limit")
    sleep_fn(seconds)


def wait_for_quota(
    *,
    usage_script: str | Path,
    q5: str,
    q7: str,
    max_waits: str,
    claude_alias: str,
    sleep_fn: Callable[[float], object] = time.sleep,
    log_fn: Callable[[str], object] = print,
    reactive: bool = False,
    fallback_seconds: float | None = None,
) -> int:
    """Wait for quota availability.

    Preflight calls are fail-open when usage cannot be inspected. Reactive
    calls follow an adapter's exit 75 and therefore always sleep at least once,
    even when the usage endpoint is unavailable or has not caught up yet.
    """
    script = Path(usage_script)
    waits = 0
    if fallback_seconds is None:
        fallback_seconds = RATE_LIMIT_FALLBACK_SECONDS if reactive else QUOTA_POLL_FALLBACK_SECONDS

    if not script.is_file():
        if reactive:
            _sleep_fallback(
                reason="WARN: usage fetch failed",
                fallback_seconds=fallback_seconds,
                sleep_fn=sleep_fn,
                log_fn=log_fn,
            )
        return 0

    while True:
        env = dict(os.environ)
        env["CLAUDE_ALIAS"] = claude_alias
        try:
            result = subprocess.run(["bash", str(script)], env=env, capture_output=True)
        except OSError:
            result = None

        if result is None or result.returncode != 0:
            if reactive and waits == 0:
                _sleep_fallback(
                    reason="WARN: usage fetch failed",
                    fallback_seconds=fallback_seconds,
                    sleep_fn=sleep_fn,
                    log_fn=log_fn,
                )
            else:
                log_fn("WARN: usage fetch failed, proceeding")
            return 0

        try:
            check = quota_check(result.stdout.decode(), q5, q7)
        except UnicodeDecodeError:
            check = None
        if check is None:
            if reactive and waits == 0:
                _sleep_fallback(
                    reason="WARN: usage parse failed",
                    fallback_seconds=fallback_seconds,
                    sleep_fn=sleep_fn,
                    log_fn=log_fn,
                )
            else:
                log_fn("WARN: usage parse failed, proceeding")
            return 0

        if check == "ok":
            if reactive and waits == 0:
                _sleep_fallback(
                    reason="Quota API is below the configured thresholds",
                    fallback_seconds=fallback_seconds,
                    sleep_fn=sleep_fn,
                    log_fn=log_fn,
                )
            return 0

        waits += 1
        wait_limit = int(max_waits)
        # A reactive call must honor the adapter's rate-limit signal with at
        # least one wait, even if QUOTA_MAX_WAITS was configured as zero.
        effective_limit = max(wait_limit, 1) if reactive else wait_limit
        if waits > effective_limit:
            log_fn(f"ERROR: quota still over limit after {max_waits} waits, aborting")
            raise SystemExit(1)

        match = re.search(r"resets_at=(\S+)", check)
        reset_at = match.group(1) if match else ""
        sleep_seconds: float
        if reset_at:
            sleep_seconds = _epoch(reset_at) - int(time.time()) + 120
            if sleep_seconds < 60:
                sleep_seconds = 60
        else:
            sleep_seconds = fallback_seconds
        log_fn(f"Quota: {check} - sleeping {sleep_seconds:g}s (wait {waits}/{max_waits})")
        sleep_fn(sleep_seconds)


# Backward-compatible private name used by pipelinelib and its tests.
_quota_check = quota_check
