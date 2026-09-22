"""Regression tests for the parallel TLC trace validator."""

from __future__ import annotations

import os
import subprocess
import tempfile
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
VALIDATE = REPO_ROOT / "scripts" / "tlc" / "validate.sh"


class TestValidateScript(unittest.TestCase):
    def setUp(self) -> None:
        self._temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self._temporary.cleanup)
        self.root = Path(self._temporary.name)
        self.bin = self.root / "bin"
        self.tools = self.root / "tools"
        self.bin.mkdir()
        self.tools.mkdir()
        for jar in ("tla2tools.jar", "CommunityModules-deps.jar"):
            (self.tools / jar).touch()
        java = self.bin / "java"
        java.write_text(
            "#!/bin/sh\n"
            "case $FAKE_JAVA_MODE in\n"
            "  success-no-progress) exit 0 ;;\n"
            "  fail-no-progress) exit 7 ;;\n"
            "  fail-after-100) printf '%s\\n' '<<\"Progress %:\", 100>>'; exit 7 ;;\n"
            "  progress-success)\n"
            "    printf '%s\\n' '<<\"Progress %:\", 25>>' '<<\"Progress %:\", 100>>'\n"
            "    exit 0\n"
            "    ;;\n"
            "  *) exit 99 ;;\n"
            "esac\n"
        )
        java.chmod(0o755)

    def run_validator(self, mode: str) -> subprocess.CompletedProcess[str]:
        env = os.environ.copy()
        env["FAKE_JAVA_MODE"] = mode
        env["PATH"] = f"{self.bin}{os.pathsep}{env['PATH']}"
        env["TOOLDIR"] = str(self.tools)
        return subprocess.run(
            [
                "bash",
                str(VALIDATE),
                "-p",
                "1",
                "-s",
                "Trace.tla",
                "-c",
                "Trace.cfg",
                "trace.ndjson",
            ],
            cwd=self.root,
            env=env,
            capture_output=True,
            text=True,
            timeout=10,
            check=False,
        )

    def test_tlc_exit_status_is_authoritative_without_progress_marker(self) -> None:
        success = self.run_validator("success-no-progress")
        failure = self.run_validator("fail-no-progress")

        self.assertEqual(success.returncode, 0, success.stdout + success.stderr)
        self.assertIn("1 of 1 trace(s) passed", success.stdout)
        self.assertEqual(failure.returncode, 1, failure.stdout + failure.stderr)
        self.assertIn("0 of 1 trace(s) passed", failure.stdout)

    def test_progress_100_cannot_mask_a_later_tlc_failure(self) -> None:
        result = self.run_validator("fail-after-100")

        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("0 of 1 trace(s) passed", result.stdout)

    def test_incremental_progress_still_finishes_on_successful_exit(self) -> None:
        result = self.run_validator("progress-success")

        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("1 of 1 trace(s) passed", result.stdout)


if __name__ == "__main__":
    unittest.main()
