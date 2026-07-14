"""Unit tests for specula.cli — the `specula` dispatcher (migration step 7).

The dispatcher was ported from the repo-root bash launcher; the help text and
the exit codes below were captured from that bash before the cutover and are
the compatibility contract. Dispatch itself is exec-based, so tests capture
the argv through the `_exec` seam instead of leaving the process.

stdlib unittest, collected natively by pytest; imports the installed package:

    uv run python -m unittest tests.unit.test_cli -v
"""

from __future__ import annotations

import contextlib
import io
import subprocess
import unittest
from pathlib import Path

from specula import cli

REPO_ROOT = Path(__file__).resolve().parents[2]

# captured from the bash dispatcher (git history: `specula` pre-cutover)
BASH_HELP = """\
usage: specula <command> [options] "name|github|lang|reference" [...]

A framework for finding deep bugs in system code using TLA+.

commands:
  run       Run the full pipeline (all phases: analysis -> classification)
  batch     Batch-run the pipeline over a task queue (workers, quota gate, retries)
  analyze   Phase 1 - static code analysis -> modeling brief
  specgen   Phase 2 - generate TLA+ specs from the modeling brief
  harness   Phase 2.5 - instrument the system + collect traces
  validate  Phase 3 - trace validation + model checking (bug hunting)
  confirm   Phase 4a - confirm & reproduce model-checking bugs
  classify  Phase 4b - assign severity tiers to confirmed bugs
  review    Run an inter-phase review agent
  setup     Install Specula agent skills + MCP tools

Every argument after <command> is forwarded verbatim to the underlying
launch script. Run 'specula <command> --help' for a command's full flag set.
"""


class CaptureExec(unittest.TestCase):
    """Base: replace the exec seam with a recorder (exec never returns; the
    recorder returns 0 so main()'s dispatch path completes in-process)."""

    def setUp(self) -> None:
        self.execs: list[list[str]] = []

        def record(argv: list[str]) -> int:
            self.execs.append(argv)
            return 0

        self.addCleanup(setattr, cli, "_exec", cli._exec)
        cli._exec = record


class TestHelp(CaptureExec):
    def _main(self, argv: list[str]) -> tuple[int, str, str]:
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            rc = cli.main(argv)
        return rc, out.getvalue(), err.getvalue()

    def test_help_matches_bash_byte_for_byte(self) -> None:
        for argv in ([], ["-h"], ["--help"], ["help"]):
            with self.subTest(argv=argv):
                rc, out, err = self._main(argv)
                self.assertEqual((rc, out, err), (0, BASH_HELP, ""))
                self.assertEqual(self.execs, [])

    def test_unknown_command_exit_2_help_on_stderr(self) -> None:
        rc, out, err = self._main(["bogus"])
        self.assertEqual(rc, 2)
        self.assertEqual(out, "")
        self.assertEqual(err, "specula: unknown command 'bogus'\n\n" + BASH_HELP)
        self.assertEqual(self.execs, [])


class TestDispatch(CaptureExec):
    def test_every_command_maps_to_its_script(self) -> None:
        for cmd, script, _ in cli.COMMANDS:
            with self.subTest(cmd=cmd):
                self.execs.clear()
                rc = cli.main([cmd, "--flag", "a|b|c|d"])
                self.assertEqual(rc, 0)
                self.assertEqual(
                    self.execs,
                    [["bash", str(cli.SCRIPTS_DIR / script), "--flag", "a|b|c|d"]],
                )

    def test_args_forwarded_verbatim_no_reparsing(self) -> None:
        # things a sloppy dispatcher would eat: --help after the command, empty
        # args, values with spaces/globs
        cli.main(["run", "--help"])
        cli.main(["batch", "", "--queue", "q w*"])
        pipeline = str(cli.SCRIPTS_DIR / "launch" / "launch_pipeline.sh")
        scheduler = str(cli.SCRIPTS_DIR / "exp" / "scheduler.sh")
        self.assertEqual(
            self.execs,
            [["bash", pipeline, "--help"], ["bash", scheduler, "", "--queue", "q w*"]],
        )

    def test_all_dispatch_targets_exist(self) -> None:
        for cmd, script, _ in cli.COMMANDS:
            with self.subTest(cmd=cmd):
                self.assertTrue((cli.SCRIPTS_DIR / script).is_file(), script)


class TestShim(unittest.TestCase):
    def test_root_launcher_delegates_to_cli(self) -> None:
        r = subprocess.run(
            ["bash", str(REPO_ROOT / "specula"), "--help"],
            capture_output=True,
            text=True,
        )
        self.assertEqual((r.returncode, r.stdout, r.stderr), (0, BASH_HELP, ""))

    def test_subcommand_help_uses_public_cli_and_succeeds(self) -> None:
        for command, _, _ in cli.COMMANDS:
            if command == "setup":
                continue  # setup's full public path is exercised hermetically in test_setup_security.py
            with self.subTest(command=command):
                r = subprocess.run(
                    ["bash", str(REPO_ROOT / "specula"), command, "--help"],
                    capture_output=True,
                    text=True,
                    timeout=10,
                )
                self.assertEqual((r.returncode, r.stderr), (0, ""), r.stdout)
                self.assertIn(f"specula {command}", r.stdout)
                self.assertNotIn("bash scripts/", r.stdout)
                self.assertNotIn("launch_", r.stdout)
                self.assertNotIn("Claude Code agent", r.stdout)
                self.assertNotIn("claude CLI installed", r.stdout)
