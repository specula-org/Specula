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
COPILOT_MCP_HELPER = REPO_ROOT / "scripts" / "infra" / "copilot_mcp.sh"
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
                ["bash", str(setup), "--help"],
                ["bash", str(setup), "-h"],
                ["bash", str(launcher), "setup", "--help"],
                ["bash", str(launcher), "setup", "-h"],
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

            for arguments, unexpected in (
                (["--hlep"], "--hlep"),
                ([""], ""),
                (["--help", "extra"], "extra"),
                (["-h", "extra"], "extra"),
                (["", "--hlep"], ""),
            ):
                expected_error = f"specula setup: unexpected argument '{unexpected}'\n\n" + SETUP_HELP
                for command in (
                    ["bash", str(setup), *arguments],
                    ["bash", str(launcher), "setup", *arguments],
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


class TestSetupAgentDetection(unittest.TestCase):
    AGENT_PROMPTS = {
        "claude": "Install Specula for Claude Code?",
        "codex": "Install Specula for Codex?",
        "copilot": "Install Specula for GitHub Copilot CLI?",
    }
    AGENT_MISSING_MESSAGES = {
        "claude": "Claude Code CLI not found on PATH; skipping.",
        "codex": "Codex CLI not found on PATH; skipping.",
        "copilot": "GitHub Copilot CLI not found on PATH; skipping.",
    }
    AGENT_USER_SKIP_MESSAGES = {
        "claude": "Skipped Claude Code.",
        "codex": "Skipped Codex.",
        "copilot": "Skipped Copilot CLI.",
    }

    def make_checkout(self, root: Path, agents: set[str]) -> tuple[Path, dict[str, str], Path]:
        for relative in (
            Path("scripts/infra/setup.sh"),
            Path("scripts/infra/copilot_mcp.sh"),
        ):
            destination = root / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(REPO_ROOT / relative, destination)

        for relative in (
            Path("tools/trace_debugger"),
            Path("tools/cfa"),
            Path("tools/spec_analyzer"),
            Path("tools/inv_checking_tool"),
            Path("skills"),
            Path("lib"),
        ):
            (root / relative).mkdir(parents=True)
        (root / "lib/tla2tools.jar").touch()
        (root / "lib/CommunityModules-deps.jar").touch()

        home = root / "home"
        home.mkdir()
        bin_dir = root / "bin"
        bin_dir.mkdir()
        command_log = root / "commands.log"

        for command in ("dirname", "grep", "head", "mkdir"):
            executable = shutil.which(command)
            if executable is None:
                self.fail(f"required test utility is missing: {command}")
            (bin_dir / command).symlink_to(executable)

        fake_python = bin_dir / "python3"
        fake_python.write_text(
            """#!/bin/bash
printf 'python3' >> "$FAKE_COMMAND_LOG"
printf '\\t%s' "$@" >> "$FAKE_COMMAND_LOG"
printf '\\n' >> "$FAKE_COMMAND_LOG"
if [[ "${1:-}" == "--version" ]]; then
  echo "Python 3.13.0"
elif [[ "${1:-}" == "-I" && "${2:-}" == "-m" && "${3:-}" == "venv" ]]; then
  /bin/mkdir -p "$4/bin"
  /bin/ln -s "$0" "$4/bin/python"
fi
"""
        )
        fake_python.chmod(0o755)

        fake_java = bin_dir / "java"
        fake_java.write_text(
            """#!/bin/bash
if [[ "${1:-}" == "-version" ]]; then
  echo 'openjdk version "21"' >&2
else
  echo "TLA+ fake help"
fi
"""
        )
        fake_java.chmod(0o755)

        for command in ("pip3", "mvn"):
            stub = bin_dir / command
            stub.write_text(
                """#!/bin/bash
printf '%s' "${0##*/}" >> "$FAKE_COMMAND_LOG"
printf '\\t%s' "$@" >> "$FAKE_COMMAND_LOG"
printf '\\n' >> "$FAKE_COMMAND_LOG"
"""
            )
            stub.chmod(0o755)

        for agent in agents:
            stub = bin_dir / agent
            stub.write_text(
                """#!/bin/bash
printf '%s' "${0##*/}" >> "$FAKE_COMMAND_LOG"
printf '\\t%s' "$@" >> "$FAKE_COMMAND_LOG"
printf '\\n' >> "$FAKE_COMMAND_LOG"
"""
            )
            stub.chmod(0o755)

        env = os.environ.copy()
        env.update(
            {
                "FAKE_COMMAND_LOG": str(command_log),
                "HOME": str(home),
                "PATH": str(bin_dir),
            }
        )
        return root / "scripts/infra/setup.sh", env, command_log

    def run_setup(
        self,
        root: Path,
        agents: set[str],
        user_input: str,
    ) -> tuple[subprocess.CompletedProcess[str], str]:
        setup, env, command_log = self.make_checkout(root, agents)
        result = subprocess.run(
            ["/bin/bash", str(setup)],
            cwd=root,
            env=env,
            input=user_input,
            capture_output=True,
            text=True,
            timeout=10,
            check=False,
        )
        commands = command_log.read_text() if command_log.exists() else ""
        return result, commands

    def test_missing_agents_are_reported_without_prompting(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            result, commands = self.run_setup(Path(tmp), set(), "")

        self.assertEqual(result.returncode, 0, result.stderr)
        for agent in self.AGENT_PROMPTS:
            self.assertNotIn(self.AGENT_PROMPTS[agent], result.stdout + result.stderr)
            self.assertIn(self.AGENT_MISSING_MESSAGES[agent], result.stdout)
            self.assertNotIn(self.AGENT_USER_SKIP_MESSAGES[agent], result.stdout)
        self.assertNotIn("src/specula/skill_install.py", commands)
        self.assertNotIn("setup_codex_plugin.py", commands)
        self.assertNotIn("claude\tmcp", commands)
        self.assertNotIn("codex\tmcp", commands)
        self.assertNotIn("copilot\tmcp", commands)

    def test_only_agents_on_path_are_prompted(self) -> None:
        for installed_agent in self.AGENT_PROMPTS:
            with self.subTest(installed_agent=installed_agent), tempfile.TemporaryDirectory() as tmp:
                result, _commands = self.run_setup(Path(tmp), {installed_agent}, "n\n")

                self.assertEqual(result.returncode, 0, result.stderr)
                for agent in self.AGENT_PROMPTS:
                    if agent == installed_agent:
                        self.assertNotIn(self.AGENT_MISSING_MESSAGES[agent], result.stdout)
                        self.assertIn(self.AGENT_USER_SKIP_MESSAGES[agent], result.stdout)
                    else:
                        self.assertIn(self.AGENT_MISSING_MESSAGES[agent], result.stdout)
                        self.assertNotIn(self.AGENT_USER_SKIP_MESSAGES[agent], result.stdout)

    def test_codex_y_keeps_explanation_out_of_branch_value(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            result, commands = self.run_setup(Path(tmp), {"codex"}, "y\nglobal\n")

        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("y: install skills and register MCP servers separately.", result.stderr)
        self.assertIn("plugin: bundle skills and MCP tools as specula-codex@specula", result.stderr)
        self.assertIn("Rerun specula setup and choose plugin again to update it.", result.stderr)
        self.assertNotIn("legacy", result.stderr.lower())
        self.assertIn("src/specula/skill_install.py", commands)
        self.assertNotIn("setup_codex_plugin.py", commands)
        self.assertEqual(commands.count("codex\tmcp\tadd"), 3)

    def test_codex_plugin_keeps_explanation_out_of_branch_value(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            result, commands = self.run_setup(Path(tmp), {"codex"}, "plugin\n")

        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("setup_codex_plugin.py", commands)
        self.assertNotIn("src/specula/skill_install.py", commands)
        self.assertNotIn("codex\tmcp\tadd", commands)
        self.assertIn("Codex plugin configured: specula-codex@specula", result.stdout)
        self.assertIn("Rerun specula setup and choose 'plugin' again", result.stdout)


class TestSetupPythonIsolation(unittest.TestCase):
    def test_setup_invokes_trusted_installers_in_isolated_mode(self) -> None:
        setup = SETUP_SCRIPT.read_text()
        copilot_mcp = COPILOT_MCP_HELPER.read_text()

        self.assertIn('cd "$PROJECT_ROOT"', setup)
        self.assertIn('source "$SCRIPT_DIR/copilot_mcp.sh"', setup)
        self.assertIn('python3 -I "$PROJECT_ROOT/src/specula/skill_install.py"', setup)
        self.assertIn('python3 -I "$SCRIPT_DIR/setup_codex_plugin.py"', setup)
        self.assertIn('python3 -I -m venv "$venv_dir"', setup)
        self.assertIn('"$python_path" -I -m pip', setup)
        self.assertIn('--shadow-root "$CLAUDE_USER_CONFIG_DIR/skills"', setup)
        self.assertIn('COPILOT_USER_CONFIG_DIR="${COPILOT_HOME:-$HOME/.copilot}"', setup)
        self.assertIn('--shadow-root "$COPILOT_USER_CONFIG_DIR/skills"', setup)
        self.assertIn('--legacy-root "$HOME/.github/skills"', setup)
        self.assertIn('COPILOT_HOME="$config_dir" copilot mcp add', copilot_mcp)
        self.assertIn("copilot --version </dev/null", copilot_mcp)
        self.assertIn("copilot mcp list --json </dev/null", copilot_mcp)
        self.assertIn('"$server_path" </dev/null 2>&1', copilot_mcp)
        self.assertIn('local config_file="$config_dir/mcp-config.json"', copilot_mcp)
        self.assertIn("python3 -I -c", copilot_mcp)
        self.assertNotIn("copilot mcp remove", copilot_mcp)
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
