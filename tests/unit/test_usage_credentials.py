"""Credential resolution in scripts/exp/usage.sh.

On macOS the default profile's credentials live in the login Keychain, not in
a file, and a failed quota fetch makes quota.wait_for_quota fall back to a
blind sleep instead of waiting until the reported resets_at.

uname, security and curl are stubbed on PATH so these run on any platform.
"""

from __future__ import annotations

import json
import os
import stat
import subprocess
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
USAGE_SH = REPO_ROOT / "scripts" / "exp" / "usage.sh"

KEYCHAIN_SERVICE = "Claude Code-credentials"
KEYCHAIN_TOKEN = "keychain-token"
FILE_TOKEN = "file-token"

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


class Harness:
    """A stubbed environment for one usage.sh invocation."""

    def __init__(
        self,
        tmp_path: Path,
        *,
        system: str = "Darwin",
        keychain: str | None = None,
        curl_exit: int = 0,
    ) -> None:
        self.home = tmp_path / "home"
        self.home.mkdir(parents=True, exist_ok=True)
        self.bin = tmp_path / "bin"
        self.bin.mkdir(parents=True, exist_ok=True)

        _write_exec(self.bin / "uname", f'[[ "${{1:-}}" == "-s" ]] && echo {system} || echo {system}')

        if keychain is None:
            # Mirror security's missing-item behavior: empty stdout, nonzero.
            _write_exec(self.bin / "security", 'echo "security: SecKeychainSearchCopyNext: not found" >&2\nexit 44')
        else:
            # Echo only for the expected service, so a wrong lookup fails.
            _write_exec(
                self.bin / "security",
                "\n".join(
                    [
                        'service=""',
                        "while [[ $# -gt 0 ]]; do",
                        '  if [[ "$1" == "-s" ]]; then service="$2"; shift 2; else shift; fi',
                        "done",
                        f'if [[ "$service" == {json.dumps(KEYCHAIN_SERVICE)} ]]; then',
                        f"  cat <<'JSON'\n{keychain}\nJSON",
                        "else",
                        "  exit 44",
                        "fi",
                    ]
                ),
            )

        if curl_exit == 0:
            _write_exec(self.bin / "curl", f"cat <<'JSON'\n{json.dumps(USAGE_JSON)}\nJSON")
        else:
            _write_exec(self.bin / "curl", f"exit {curl_exit}")

    def default_credentials_path(self) -> Path:
        return self.home / ".claude" / ".credentials.json"

    def write_default_file(self, token: str) -> None:
        path = self.default_credentials_path()
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(_credentials_blob(token), encoding="utf-8")

    def run(self, *args: str, env_extra: dict[str, str] | None = None) -> subprocess.CompletedProcess[str]:
        env = {
            "HOME": str(self.home),
            # Stubs ahead of the real tools; python3 stays real.
            "PATH": f"{self.bin}:{os.environ.get('PATH', '')}",
        }
        env.update(env_extra or {})
        return subprocess.run(
            ["bash", str(USAGE_SH), *args],
            capture_output=True,
            text=True,
            env=env,
            timeout=60,
        )


# ──────────────────────────────────────────────────────────────────────────────
# The regression: macOS default profile with no credentials file
# ──────────────────────────────────────────────────────────────────────────────


def test_macos_default_profile_reads_the_keychain(tmp_path: Path) -> None:
    """No credentials file exists and the token is in the Keychain."""
    harness = Harness(tmp_path, keychain=_credentials_blob(KEYCHAIN_TOKEN))
    assert not harness.default_credentials_path().exists()

    result = harness.run(env_extra={"CLAUDE_ALIAS": "claude"})

    assert result.returncode == 0, result.stderr
    assert json.loads(result.stdout)["seven_day"]["utilization"] == 89.0


def test_macos_config_dir_pointing_at_the_default_profile_reads_the_keychain(tmp_path: Path) -> None:
    """The adapter exports CLAUDE_CONFIG_DIR=$HOME/.claude, the default path."""
    harness = Harness(tmp_path, keychain=_credentials_blob(KEYCHAIN_TOKEN))

    result = harness.run(env_extra={"CLAUDE_CONFIG_DIR": str(harness.home / ".claude")})

    assert result.returncode == 0, result.stderr
    assert json.loads(result.stdout)["five_hour"]["utilization"] == 13.0


def test_unwrapped_keychain_payload_is_accepted(tmp_path: Path) -> None:
    """The top-level object is used when claudeAiOauth is absent."""
    harness = Harness(tmp_path, keychain=_credentials_blob(KEYCHAIN_TOKEN, wrapped=False))

    result = harness.run()

    assert result.returncode == 0, result.stderr


# ──────────────────────────────────────────────────────────────────────────────
# Existing behavior must not change
# ──────────────────────────────────────────────────────────────────────────────


def test_existing_credentials_file_wins_over_the_keychain(tmp_path: Path) -> None:
    """The Keychain is consulted only when the file is absent."""
    harness = Harness(tmp_path, keychain=_credentials_blob(KEYCHAIN_TOKEN))
    harness.write_default_file(FILE_TOKEN)

    result = harness.run()

    assert result.returncode == 0, result.stderr
    assert json.loads(result.stdout)["seven_day"]["utilization"] == 89.0


def test_explicit_credentials_path_does_not_fall_back(tmp_path: Path) -> None:
    """An explicit path names a file the caller expects to be read."""
    harness = Harness(tmp_path, keychain=_credentials_blob(KEYCHAIN_TOKEN))
    missing = tmp_path / "nowhere" / "creds.json"

    result = harness.run(env_extra={"CLAUDE_CREDENTIALS": str(missing)})

    assert result.returncode == 2
    assert str(missing) in result.stderr
    assert "Keychain" not in result.stderr


def test_non_default_alias_does_not_fall_back(tmp_path: Path) -> None:
    """Another profile must not receive the default account's quota."""
    harness = Harness(tmp_path, keychain=_credentials_blob(KEYCHAIN_TOKEN))

    result = harness.run(env_extra={"CLAUDE_ALIAS": "work"})

    assert result.returncode == 2
    assert ".work/.credentials.json" in result.stderr
    assert "Keychain" not in result.stderr


def test_non_default_config_dir_does_not_fall_back(tmp_path: Path) -> None:
    harness = Harness(tmp_path, keychain=_credentials_blob(KEYCHAIN_TOKEN))
    other = tmp_path / "other-config"

    result = harness.run(env_extra={"CLAUDE_CONFIG_DIR": str(other)})

    assert result.returncode == 2
    assert "Keychain" not in result.stderr


def test_non_darwin_does_not_consult_the_keychain(tmp_path: Path) -> None:
    """On Linux the file is the only store."""
    harness = Harness(tmp_path, system="Linux", keychain=_credentials_blob(KEYCHAIN_TOKEN))

    result = harness.run()

    assert result.returncode == 2
    assert "credentials not found at" in result.stderr
    assert "Keychain" not in result.stderr


# ──────────────────────────────────────────────────────────────────────────────
# Failure reporting
# ──────────────────────────────────────────────────────────────────────────────


def test_missing_keychain_item_reports_both_stores(tmp_path: Path) -> None:
    harness = Harness(tmp_path, keychain=None)

    result = harness.run()

    assert result.returncode == 2
    assert "credentials not found at" in result.stderr
    assert "Keychain" in result.stderr
    assert KEYCHAIN_SERVICE in result.stderr


def test_empty_keychain_output_is_a_failure_not_a_token(tmp_path: Path) -> None:
    """An item yielding nothing must not be parsed as credentials."""
    harness = Harness(tmp_path, keychain="")

    result = harness.run()

    assert result.returncode == 2
    assert "Keychain" in result.stderr


def test_malformed_keychain_payload_reports_a_token_failure(tmp_path: Path) -> None:
    harness = Harness(tmp_path, keychain="{not json")

    result = harness.run()

    assert result.returncode == 2
    assert "failed to read access token" in result.stderr


def test_keychain_payload_without_a_token_fails(tmp_path: Path) -> None:
    harness = Harness(tmp_path, keychain=json.dumps({"claudeAiOauth": {"accessToken": ""}}))

    result = harness.run()

    assert result.returncode == 2
    assert "failed to read access token" in result.stderr


def test_api_failure_still_reports_a_fetch_error(tmp_path: Path) -> None:
    harness = Harness(tmp_path, keychain=_credentials_blob(KEYCHAIN_TOKEN), curl_exit=22)

    result = harness.run()

    assert result.returncode == 2
    assert "API request failed" in result.stderr


# ──────────────────────────────────────────────────────────────────────────────
# The consumer contract: --check must emit resets_at for quota.wait_for_quota
# ──────────────────────────────────────────────────────────────────────────────


def test_check_mode_emits_resets_at_so_quota_can_wait_precisely(tmp_path: Path) -> None:
    """quota.wait_for_quota regexes resets_at= out of this line."""
    harness = Harness(tmp_path, keychain=_credentials_blob(KEYCHAIN_TOKEN))

    result = harness.run("--check", "80")

    assert result.returncode == 1, result.stderr
    assert "7d=89.0%" in result.stdout
    assert "resets_at=2026-11-05T17:00:00+00:00" in result.stdout


def test_check_mode_under_threshold_reports_ok(tmp_path: Path) -> None:
    harness = Harness(tmp_path, keychain=_credentials_blob(KEYCHAIN_TOKEN))

    result = harness.run("--check", "95")

    assert result.returncode == 0, result.stderr
    assert result.stdout.strip() == "ok"


def test_quota_parses_check_output_into_a_precise_sleep(tmp_path: Path) -> None:
    """The line usage.sh produces drives a resets_at-based wait."""
    import re
    import time

    from specula import quota

    harness = Harness(tmp_path, keychain=_credentials_blob(KEYCHAIN_TOKEN))
    result = harness.run("--check", "80")

    match = re.search(r"resets_at=(\S+)", result.stdout)
    assert match is not None
    sleep_seconds = quota._epoch(match.group(1)) - int(time.time()) + 120
    # A real timestamp was parsed rather than falling through to the fallback.
    assert quota._epoch(match.group(1)) > 0
    assert sleep_seconds != quota.RATE_LIMIT_FALLBACK_SECONDS
