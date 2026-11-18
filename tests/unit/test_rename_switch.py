"""Users switching from Specula get told what to change instead of silent misbehavior."""

from __future__ import annotations

import contextlib
import io
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

from specular import rename_check

SRC = Path(__file__).resolve().parents[2] / "src"


class TestOldCommand(unittest.TestCase):
    def test_pre_rename_entry_point_prints_the_switch_steps(self) -> None:
        # Installs made before the rename run `from specula.cli import main` with src/ on sys.path.
        code = f"import sys; sys.path.insert(0, {str(SRC)!r}); from specula.cli import main; main()"
        r = subprocess.run([sys.executable, "-I", "-c", code], capture_output=True, text=True)
        self.assertEqual((r.returncode, r.stdout), (1, ""))
        self.assertIn("uv tool uninstall specula && uv tool install -e .", r.stderr)
        self.assertIn("Switching from Specula", r.stderr)


class TestLegacyEnvironment(unittest.TestCase):
    def test_only_names_specula_used_are_reported(self) -> None:
        # Agent-written harness scripts define their own SPECULA_* variables; leave those alone.
        env = {"SPECULA_MODEL": "x", "SPECULAR_MODEL": "y", "SPECULA_SANDBOX": "1", "SPECULA_TRACE_DIR": "/t"}
        self.assertEqual(rename_check.legacy_variables(env), ["SPECULA_MODEL", "SPECULA_SANDBOX"])

    def test_legacy_variables_stop_the_run_with_the_new_names(self) -> None:
        err = io.StringIO()
        with contextlib.redirect_stderr(err), self.assertRaises(SystemExit) as raised:
            rename_check.exit_on_legacy_settings({"SPECULA_SANDBOX": "1"})
        self.assertEqual(raised.exception.code, 1)
        self.assertIn("SPECULA_SANDBOX -> SPECULAR_SANDBOX", err.getvalue())

    def test_clean_environment_passes(self) -> None:
        rename_check.exit_on_legacy_settings({"SPECULAR_SANDBOX": "1", "PATH": "/bin"})


class TestLegacySandboxConfig(unittest.TestCase):
    def test_unmoved_sandbox_config_is_reported_only_when_the_sandbox_is_on(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            cwd, home = Path(tmp) / "project", Path(tmp) / "home"
            legacy = home / ".specula" / "sandbox.json"
            legacy.parent.mkdir(parents=True)
            legacy.write_text("{}")
            cwd.mkdir()
            on = {"SPECULAR_SANDBOX": "on"}
            self.assertEqual(rename_check.legacy_sandbox_configs(on, cwd, home), [legacy])
            self.assertEqual(rename_check.legacy_sandbox_configs({}, cwd, home), [])
            explicit = {**on, "SPECULAR_SANDBOX_CONFIG": "/etc/policy.json"}
            self.assertEqual(rename_check.legacy_sandbox_configs(explicit, cwd, home), [])
            self.assertIn(f"mv {legacy} {home / '.specular'}/", rename_check.legacy_sandbox_message([legacy]))
            project = cwd / ".specular" / "sandbox.json"
            project.parent.mkdir()
            project.write_text("{}")
            self.assertEqual(rename_check.legacy_sandbox_configs(on, cwd, home), [])  # home is never read
            project.unlink()
            moved = home / ".specular" / "sandbox.json"
            moved.parent.mkdir()
            moved.write_text("{}")
            self.assertEqual(rename_check.legacy_sandbox_configs(on, cwd, home), [])


if __name__ == "__main__":
    unittest.main()
