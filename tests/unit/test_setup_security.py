"""Security contracts for the top-level setup entrypoint."""

from __future__ import annotations

import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
SETUP_SCRIPT = REPO_ROOT / "scripts" / "infra" / "setup.sh"
SKILL_INSTALLER = REPO_ROOT / "src" / "specula" / "skill_install.py"


class TestSetupPythonIsolation(unittest.TestCase):
    def test_setup_invokes_trusted_installers_in_isolated_mode(self) -> None:
        setup = SETUP_SCRIPT.read_text()

        self.assertIn('cd "$PROJECT_ROOT"', setup)
        self.assertIn('python3 -I "$PROJECT_ROOT/src/specula/skill_install.py"', setup)
        self.assertIn('python3 -I "$SCRIPT_DIR/setup_codex_plugin.py"', setup)
        self.assertIn('python3 -I -m venv "$venv_dir"', setup)
        self.assertIn('"$python_path" -I -m pip', setup)
        self.assertIn('--shadow-root "$CLAUDE_USER_CONFIG_DIR/skills"', setup)
        self.assertNotIn("python3 -m specula.skill_install", setup)

    def test_skill_installer_ignores_hostile_cwd_and_pythonpath(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            attacker = root / "attacker"
            source = root / "source"
            target = root / "target"
            marker = root / "hijacked"
            attacker_package = attacker / "specula"
            attacker_package.mkdir(parents=True)
            source_skill = source / "code_analysis"
            source_skill.mkdir(parents=True)
            (source_skill / "SKILL.md").write_text(
                "---\nname: code-analysis\ndescription: test\n---\n\nInstructions.\n"
            )
            (attacker / "pathlib.py").write_text(
                f"with open({str(marker)!r}, 'w') as stream:\n    stream.write('pathlib')\n"
            )
            (attacker_package / "__init__.py").write_text("")
            (attacker_package / "skill_install.py").write_text(
                f"with open({str(marker)!r}, 'w') as stream:\n    stream.write('specula')\n"
            )

            env = os.environ.copy()
            env["PYTHONPATH"] = str(attacker)
            result = subprocess.run(
                [
                    sys.executable,
                    "-I",
                    str(SKILL_INSTALLER),
                    "--source",
                    str(source),
                    "--target",
                    str(target),
                ],
                cwd=attacker,
                env=env,
                capture_output=True,
                text=True,
                check=False,
            )

            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertFalse(marker.exists())
            self.assertEqual((target / "code-analysis").resolve(), source_skill.resolve())


if __name__ == "__main__":
    unittest.main()
