"""Credential resolution in scripts/exp/usage.sh.

On macOS the credentials live in the login Keychain, not in a file, and a
failed quota fetch makes quota.wait_for_quota fall back to a blind sleep
instead of waiting until the reported resets_at.

Claude Code names its Keychain item "Claude Code-credentials", suffixed with
the first 8 hex digits of sha256(config dir) whenever CLAUDE_CONFIG_DIR is set
(even to ~/.claude) and left bare otherwise.

uname, security and curl are stubbed on PATH so these run on any platform.
"""

from __future__ import annotations

import hashlib
import json
import os
import stat
import subprocess
import time
from collections.abc import Mapping
from datetime import datetime, timedelta, timezone
from pathlib import Path

import pytest

from specula import quota

REPO_ROOT = Path(__file__).resolve().parents[2]
USAGE_SH = REPO_ROOT / "scripts" / "exp" / "usage.sh"

BASE_SERVICE = "Claude Code-credentials"

USAGE_JSON = {
    "five_hour": {"utilization": 13.0, "resets_at": "2026-11-05T04:09:59+00:00"},
    "seven_day": {"utilization": 89.0, "resets_at": "2026-11-05T17:00:00+00:00"},
}


def _write_exec(path: Path, body: str) -> None:
    path.write_text(f"#!/usr/bin/env bash\n{body}\n", encoding="utf-8")
    path.chmod(path.stat().st_mode | stat.S_IEXEC | stat.S_IXGRP | stat.S_IXOTH)


def _credentials_blob(token: str, *, wrapped: bool = True) -> str:
    payload = {"claudeAiOauth": {"accessToken": token}} if wrapped else {"accessToken": token}
    return json.dumps(payload)


def _suffixed(config_dir: str | Path) -> str:
    digest = hashlib.sha256(str(config_dir).encode()).hexdigest()[:8]
    return f"{BASE_SERVICE}-{digest}"


class Harness:
    """A stubbed environment for one usage.sh invocation."""

    def __init__(
        self,
        tmp_path: Path,
        *,
        system: str = "Darwin",
        keychain: dict[str, str] | None = None,
        curl_exit: int = 0,
    ) -> None:
        self.home = tmp_path / "home"
        self.home.mkdir(parents=True, exist_ok=True)
        self.bin = tmp_path / "bin"
        self.bin.mkdir(parents=True, exist_ok=True)
        self.curl_log = tmp_path / "curl.log"
        self.curl_exit = curl_exit

        _write_exec(self.bin / "uname", f"echo {system}")

        # Serve only the listed services, like the real item lookup; anything
        # else mirrors security's missing-item behavior (empty stdout, nonzero).
        arms = "\n".join(
            f"  {json.dumps(service)}) cat <<'JSON'\n{payload}\nJSON\n  ;;"
            for service, payload in (keychain or {}).items()
        )
        _write_exec(
            self.bin / "security",
            "\n".join(
                [
                    'service=""',
                    "while [[ $# -gt 0 ]]; do",
                    '  if [[ "$1" == "-s" ]]; then service="$2"; shift 2; else shift; fi',
                    "done",
                    'case "$service" in',
                    arms,
                    '  *) echo "security: SecKeychainSearchCopyNext: not found" >&2; exit 44 ;;',
                    "esac",
                ]
            ),
        )

        self.set_usage(USAGE_JSON)

    def set_usage(self, usage: Mapping[str, object]) -> None:
        log = f'for a in "$@"; do [[ "$a" == Authorization:* ]] && echo "$a" >> {json.dumps(str(self.curl_log))}; done'
        if self.curl_exit == 0:
            _write_exec(self.bin / "curl", f"{log}\ncat <<'JSON'\n{json.dumps(usage)}\nJSON")
        else:
            _write_exec(self.bin / "curl", f"{log}\nexit {self.curl_exit}")

    def default_credentials_path(self) -> Path:
        return self.home / ".claude" / ".credentials.json"

    def write_default_file(self, token: str) -> None:
        path = self.default_credentials_path()
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(_credentials_blob(token), encoding="utf-8")

    def tokens_sent(self) -> list[str]:
        """Bearer tokens usage.sh presented to the usage endpoint."""
        if not self.curl_log.exists():
            return []
        return [line.removeprefix("Authorization: Bearer ") for line in self.curl_log.read_text().splitlines()]

    def base_env(self) -> dict[str, str]:
        # Stubs ahead of the real tools; python3 stays real.
        return {"HOME": str(self.home), "PATH": f"{self.bin}:{os.environ.get('PATH', '')}"}

    def run(self, *args: str, env_extra: dict[str, str] | None = None) -> subprocess.CompletedProcess[str]:
        env = self.base_env()
        env.update(env_extra or {})
        return subprocess.run(
            ["bash", str(USAGE_SH), *args],
            capture_output=True,
            text=True,
            env=env,
            timeout=60,
        )


# ──────────────────────────────────────────────────────────────────────────────
# The regression: macOS with no credentials file
# ──────────────────────────────────────────────────────────────────────────────


def test_macos_default_profile_reads_the_keychain(tmp_path: Path) -> None:
    """No credentials file exists and the token is in the bare Keychain item."""
    harness = Harness(tmp_path, keychain={BASE_SERVICE: _credentials_blob("bare-token")})
    assert not harness.default_credentials_path().exists()

    result = harness.run(env_extra={"CLAUDE_ALIAS": "claude"})

    assert result.returncode == 0, result.stderr
    assert json.loads(result.stdout)["seven_day"]["utilization"] == 89.0
    assert harness.tokens_sent() == ["bare-token"]


def test_config_dir_set_to_the_default_path_reads_the_suffixed_item(tmp_path: Path) -> None:
    """The adapter exports CLAUDE_CONFIG_DIR=$HOME/.claude; Claude Code then suffixes the item."""
    config_dir = tmp_path / "home" / ".claude"
    harness = Harness(tmp_path, keychain={_suffixed(config_dir): _credentials_blob("suffixed-token")})

    result = harness.run(env_extra={"CLAUDE_CONFIG_DIR": str(config_dir)})

    assert result.returncode == 0, result.stderr
    assert harness.tokens_sent() == ["suffixed-token"]


def test_config_dir_set_to_the_default_path_ignores_the_bare_item(tmp_path: Path) -> None:
    """Claude Code would not read the bare item here; it may be another account."""
    harness = Harness(tmp_path, keychain={BASE_SERVICE: _credentials_blob("bare-token")})

    result = harness.run(env_extra={"CLAUDE_CONFIG_DIR": str(harness.home / ".claude")})

    assert result.returncode == 2
    assert harness.tokens_sent() == []


def test_suffixed_item_wins_over_the_bare_item(tmp_path: Path) -> None:
    """With both present, the account the adapter-launched claude uses is the one measured."""
    config_dir = tmp_path / "home" / ".claude"
    harness = Harness(
        tmp_path,
        keychain={
            BASE_SERVICE: _credentials_blob("bare-token"),
            _suffixed(config_dir): _credentials_blob("suffixed-token"),
        },
    )

    for env_extra in ({"CLAUDE_CONFIG_DIR": str(config_dir)}, {"CLAUDE_ALIAS": "claude"}):
        harness.curl_log.unlink(missing_ok=True)
        result = harness.run(env_extra=env_extra)
        assert result.returncode == 0, result.stderr
        assert harness.tokens_sent() == ["suffixed-token"]


def test_service_suffix_matches_claude_codes_naming(tmp_path: Path) -> None:
    """Pin the suffix to a literal so the helper cannot drift with the script."""
    assert _suffixed("/Users/alice/.claude") == f"{BASE_SERVICE}-5ac5e874"
    harness = Harness(tmp_path, keychain={f"{BASE_SERVICE}-5ac5e874": _credentials_blob("alice-token")})

    result = harness.run(env_extra={"CLAUDE_CONFIG_DIR": "/Users/alice/.claude"})

    assert result.returncode == 0, result.stderr
    assert harness.tokens_sent() == ["alice-token"]


def test_non_default_alias_reads_only_its_own_suffixed_item(tmp_path: Path) -> None:
    """The adapter runs alias "work" with CLAUDE_CONFIG_DIR=$HOME/.work."""
    work_dir = tmp_path / "home" / ".work"
    harness = Harness(
        tmp_path,
        keychain={
            BASE_SERVICE: _credentials_blob("bare-token"),
            _suffixed(work_dir): _credentials_blob("work-token"),
        },
    )

    result = harness.run(env_extra={"CLAUDE_ALIAS": "work"})

    assert result.returncode == 0, result.stderr
    assert harness.tokens_sent() == ["work-token"]


def test_non_default_alias_never_falls_back_to_the_bare_item(tmp_path: Path) -> None:
    """Another profile must not receive the default account's quota."""
    harness = Harness(tmp_path, keychain={BASE_SERVICE: _credentials_blob("bare-token")})

    result = harness.run(env_extra={"CLAUDE_ALIAS": "work"})

    assert result.returncode == 2
    assert ".work/.credentials.json" in result.stderr
    assert harness.tokens_sent() == []


def test_non_default_config_dir_never_falls_back_to_the_bare_item(tmp_path: Path) -> None:
    harness = Harness(tmp_path, keychain={BASE_SERVICE: _credentials_blob("bare-token")})

    result = harness.run(env_extra={"CLAUDE_CONFIG_DIR": str(tmp_path / "other-config")})

    assert result.returncode == 2
    assert harness.tokens_sent() == []


def test_unwrapped_keychain_payload_is_accepted(tmp_path: Path) -> None:
    """The top-level object is used when claudeAiOauth is absent."""
    harness = Harness(tmp_path, keychain={BASE_SERVICE: _credentials_blob("bare-token", wrapped=False)})

    result = harness.run()

    assert result.returncode == 0, result.stderr


# ──────────────────────────────────────────────────────────────────────────────
# Existing behavior must not change
# ──────────────────────────────────────────────────────────────────────────────


def test_existing_credentials_file_wins_over_the_keychain(tmp_path: Path) -> None:
    """The Keychain is consulted only when the file is absent."""
    harness = Harness(tmp_path, keychain={BASE_SERVICE: _credentials_blob("bare-token")})
    harness.write_default_file("file-token")

    result = harness.run()

    assert result.returncode == 0, result.stderr
    assert harness.tokens_sent() == ["file-token"]


def test_explicit_credentials_path_does_not_fall_back(tmp_path: Path) -> None:
    """An explicit path names a file the caller expects to be read."""
    harness = Harness(tmp_path, keychain={BASE_SERVICE: _credentials_blob("bare-token")})
    missing = tmp_path / "nowhere" / "creds.json"

    result = harness.run(env_extra={"CLAUDE_CREDENTIALS": str(missing)})

    assert result.returncode == 2
    assert str(missing) in result.stderr
    assert "Keychain" not in result.stderr
    assert harness.tokens_sent() == []


def test_non_darwin_does_not_consult_the_keychain(tmp_path: Path) -> None:
    """On Linux the file is the only store."""
    harness = Harness(tmp_path, system="Linux", keychain={BASE_SERVICE: _credentials_blob("bare-token")})

    result = harness.run()

    assert result.returncode == 2
    assert "credentials not found at" in result.stderr
    assert "Keychain" not in result.stderr
    assert harness.tokens_sent() == []


# ──────────────────────────────────────────────────────────────────────────────
# Failure reporting
# ──────────────────────────────────────────────────────────────────────────────


def test_missing_keychain_item_reports_both_stores(tmp_path: Path) -> None:
    harness = Harness(tmp_path)

    result = harness.run()

    assert result.returncode == 2
    assert "credentials not found at" in result.stderr
    assert f"{_suffixed(harness.home / '.claude')} or {BASE_SERVICE} (run: claude /login)" in result.stderr


def test_empty_keychain_output_is_a_failure_not_a_token(tmp_path: Path) -> None:
    """An item yielding nothing must not be parsed as credentials."""
    harness = Harness(tmp_path, keychain={BASE_SERVICE: ""})

    result = harness.run()

    assert result.returncode == 2
    assert "Keychain" in result.stderr


def test_malformed_keychain_payload_reports_a_token_failure(tmp_path: Path) -> None:
    harness = Harness(tmp_path, keychain={BASE_SERVICE: "{not json"})

    result = harness.run()

    assert result.returncode == 2
    assert "failed to read access token" in result.stderr


def test_keychain_payload_without_a_token_fails(tmp_path: Path) -> None:
    harness = Harness(tmp_path, keychain={BASE_SERVICE: json.dumps({"claudeAiOauth": {"accessToken": ""}})})

    result = harness.run()

    assert result.returncode == 2
    assert "failed to read access token" in result.stderr


def test_api_failure_still_reports_a_fetch_error(tmp_path: Path) -> None:
    harness = Harness(tmp_path, keychain={BASE_SERVICE: _credentials_blob("bare-token")}, curl_exit=22)

    result = harness.run()

    assert result.returncode == 2
    assert "API request failed" in result.stderr


# ──────────────────────────────────────────────────────────────────────────────
# --check mode
# ──────────────────────────────────────────────────────────────────────────────


def test_check_mode_over_threshold_reports_the_window_and_reset(tmp_path: Path) -> None:
    harness = Harness(tmp_path, keychain={BASE_SERVICE: _credentials_blob("bare-token")})

    result = harness.run("--check", "80")

    assert result.returncode == 1, result.stderr
    assert "7d=89.0%" in result.stdout
    assert "resets_at=2026-11-05T17:00:00+00:00" in result.stdout


def test_check_mode_under_threshold_reports_ok(tmp_path: Path) -> None:
    harness = Harness(tmp_path, keychain={BASE_SERVICE: _credentials_blob("bare-token")})

    result = harness.run("--check", "95")

    assert result.returncode == 0, result.stderr
    assert result.stdout.strip() == "ok"


# ──────────────────────────────────────────────────────────────────────────────
# The consumer: quota.wait_for_quota runs usage.sh with no arguments
# ──────────────────────────────────────────────────────────────────────────────


def test_wait_for_quota_sleeps_until_resets_at_when_credentials_come_from_the_keychain(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """The failed fetch used to degrade to the blind RATE_LIMIT_FALLBACK_SECONDS sleep."""
    harness = Harness(tmp_path, keychain={BASE_SERVICE: _credentials_blob("bare-token")})
    resets_at = datetime.now(timezone.utc) + timedelta(hours=2)
    harness.set_usage({"five_hour": {"utilization": 99.0, "resets_at": resets_at.isoformat()}})
    for key, value in harness.base_env().items():
        monkeypatch.setenv(key, value)
    monkeypatch.delenv("CLAUDE_CONFIG_DIR", raising=False)
    monkeypatch.delenv("CLAUDE_CREDENTIALS", raising=False)

    sleeps: list[float] = []

    def sleep_then_reset(seconds: float) -> None:
        sleeps.append(seconds)
        harness.set_usage({"five_hour": {"utilization": 1.0, "resets_at": resets_at.isoformat()}})

    rc = quota.wait_for_quota(
        usage_script=USAGE_SH,
        q5="95",
        q7="95",
        max_waits="1",
        claude_alias="claude",
        sleep_fn=sleep_then_reset,
        log_fn=lambda _message: None,
    )

    assert rc == 0
    assert len(sleeps) == 1
    expected = resets_at.timestamp() - time.time() + 120
    assert abs(sleeps[0] - expected) < 10
    assert sleeps[0] != quota.RATE_LIMIT_FALLBACK_SECONDS
