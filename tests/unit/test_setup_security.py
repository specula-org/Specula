"""Security contracts for the top-level setup entrypoint."""

from __future__ import annotations

import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
SETUP_SCRIPT = REPO_ROOT / "scripts" / "infra" / "setup.sh"
SKILL_INSTALLER = REPO_ROOT / "src" / "specula" / "skill_install.py"
SETUP_HELP = """\
Usage:
  specula setup

Install Specula's TLA+ tools, Python environments, agent skills, and MCP integrations.

This interactive command may download dependencies, build local tools, and
update agent configuration.

Options:
  -h, --help  Show this help and exit
"""


class TestSetupHelp(unittest.TestCase):
    def make_checkout(self, root: Path) -> tuple[Path, Path, dict[str, str], Path]:
        for relative in (
            Path("specula"),
            Path("src/specula/cli.py"),
            Path("scripts/infra/setup.sh"),
        ):
            destination = root / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(REPO_ROOT / relative, destination)

        home = root / "home"
        home.mkdir()
        bin_dir = root / "bin"
        bin_dir.mkdir()
        sentinel = root / "setup-command-ran"
        stub = bin_dir / "stub"
        stub.write_text('#!/usr/bin/env bash\nprintf "called: %s\\n" "$0" >> "$SETUP_SENTINEL"\n')
        stub.chmod(0o755)
        for command in ("java", "pip3", "wget", "curl", "mvn", "claude", "codex"):
            (bin_dir / command).symlink_to(stub.name)

        env = os.environ.copy()
        env["HOME"] = str(home)
        env["PATH"] = f"{bin_dir}:{env['PATH']}"
        env["SETUP_SENTINEL"] = str(sentinel)
        return root / "specula", root / "scripts/infra/setup.sh", env, sentinel

    def assert_no_setup_side_effects(self, root: Path, env: dict[str, str], sentinel: Path) -> None:
        self.assertFalse(sentinel.exists())
        self.assertEqual(list(Path(env["HOME"]).iterdir()), [])
        for path in (
            root / "lib",
            root / "tools/trace_debugger/.venv",
            root / "tools/spec_analyzer/.venv",
            root / "tools/inv_checking_tool/.venv",
            root / "tools/cfa/target",
            root / ".specula-codex",
            root / ".claude",
            root / ".agents",
            root / ".github",
        ):
            self.assertFalse(path.exists(), path)

    def test_help_exits_before_any_setup_side_effect(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            launcher, setup, env, sentinel = self.make_checkout(root)

            for command in (
                ["/bin/bash", str(setup), "--help"],
                ["/bin/bash", str(setup), "-h"],
                ["/bin/bash", str(launcher), "setup", "--help"],
                ["/bin/bash", str(launcher), "setup", "-h"],
            ):
                with self.subTest(command=command):
                    result = subprocess.run(
                        command,
                        cwd=root,
                        env=env,
                        capture_output=True,
                        text=True,
                        timeout=5,
                        check=False,
                    )
                    self.assertEqual((result.returncode, result.stdout, result.stderr), (0, SETUP_HELP, ""))
                    self.assert_no_setup_side_effects(root, env, sentinel)

    def test_unknown_argument_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            launcher, setup, env, sentinel = self.make_checkout(root)

            for arguments in (["--hlep"], [""], ["--help", "extra"], ["", "--hlep"]):
                expected_error = f"specula setup: unexpected argument '{arguments[0]}'\n\n" + SETUP_HELP
                for command in (
                    ["/bin/bash", str(setup), *arguments],
                    ["/bin/bash", str(launcher), "setup", *arguments],
                ):
                    with self.subTest(command=command):
                        result = subprocess.run(
                            command,
                            cwd=root,
                            env=env,
                            capture_output=True,
                            text=True,
                            timeout=5,
                            check=False,
                        )
                        self.assertEqual((result.returncode, result.stdout, result.stderr), (2, "", expected_error))
                        self.assert_no_setup_side_effects(root, env, sentinel)


class TestSetupPythonIsolation(unittest.TestCase):
    def test_setup_invokes_trusted_installers_in_isolated_mode(self) -> None:
        setup = SETUP_SCRIPT.read_text()

        self.assertIn('cd "$PROJECT_ROOT"', setup)
        self.assertIn('python3 -I "$PROJECT_ROOT/src/specula/skill_install.py"', setup)
        self.assertIn('python3 -I "$SCRIPT_DIR/setup_codex_plugin.py"', setup)
        self.assertIn('python3 -I -m venv "$venv_dir"', setup)
        self.assertIn('"$python_path" -I -m pip', setup)
        self.assertIn('--shadow-root "$CLAUDE_USER_CONFIG_DIR/skills"', setup)
        self.assertIn('COPILOT_USER_CONFIG_DIR="${COPILOT_HOME:-$HOME/.copilot}"', setup)
        self.assertIn('--shadow-root "$COPILOT_USER_CONFIG_DIR/skills"', setup)
        self.assertIn('--legacy-root "$HOME/.github/skills"', setup)
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
