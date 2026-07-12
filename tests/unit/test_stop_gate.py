"""Unit tests for src/specula/stop_gate.py — the completion gate.

Pins the decision tree (fail-open, BLOCKED.md surrender, fuse, live-pid
detection, per-phase deliverable contracts) and the by-path CLI entry points
(claude/codex hook wire contract, accept exit codes).

stdlib unittest, no pytest needed:

    python3 -m unittest discover -s tests/unit -v
"""

from __future__ import annotations

import io
import json
import os
import subprocess
import sys
import unittest
from contextlib import redirect_stdout
from pathlib import Path

SRC = Path(__file__).resolve().parents[2] / "src"
sys.path.insert(0, str(SRC))
from specula import stop_gate as sg  # noqa: E402

GATE = SRC / "specula" / "stop_gate.py"


class GateCase(unittest.TestCase):
    """Base: a fresh work dir per test and a clean gate environment."""

    def setUp(self) -> None:
        import tempfile

        self._td = tempfile.TemporaryDirectory()
        self.addCleanup(self._td.cleanup)
        self.wd = Path(self._td.name).resolve()
        (self.wd / "spec").mkdir()
        for var in ("SPECULA_STOP_GATE", "SPECULA_STOP_GATE_CAP", "SPECULA_STOP_GATE_WORK_DIR"):
            self._stash(var)

    def _stash(self, var: str) -> None:
        old = os.environ.pop(var, None)
        if old is not None:
            self.addCleanup(os.environ.__setitem__, var, old)

    # helpers
    def deliver(self, phase: str = "spec_validation", text: str = "# report\n") -> None:
        (self.wd / sg.CONTRACTS[phase]).write_text(text)

    def spawn_sleeper(self, pid_file: Path) -> subprocess.Popen[bytes]:
        proc = subprocess.Popen(["sleep", "300"])
        self.addCleanup(proc.wait)
        self.addCleanup(proc.kill)
        pid_file.parent.mkdir(parents=True, exist_ok=True)
        pid_file.write_text(f"{proc.pid}\n")
        return proc


class TestDecideFailOpen(GateCase):
    def test_no_phase(self) -> None:
        allow, _ = sg.decide("", self.wd)
        self.assertTrue(allow)

    def test_missing_work_dir(self) -> None:
        allow, _ = sg.decide("spec_validation", self.wd / "nope")
        self.assertTrue(allow)

    def test_off_switch(self) -> None:
        os.environ["SPECULA_STOP_GATE"] = "off"
        allow, reason = sg.decide("spec_validation", self.wd)
        self.assertTrue(allow)
        self.assertIn("disabled", reason)

    def test_unknown_phase_no_contract(self) -> None:
        allow, _ = sg.decide("code_analysis", self.wd)
        self.assertTrue(allow)


class TestDeliverableContract(GateCase):
    def test_validation_missing_blocks(self) -> None:
        allow, reason = sg.decide("spec_validation", self.wd)
        self.assertFalse(allow)
        self.assertIn("bug-report.md", reason)
        self.assertIn("BLOCKED.md", reason)  # the surrender path is taught in-band

    def test_confirmation_missing_blocks(self) -> None:
        allow, reason = sg.decide("bug_confirmation", self.wd)
        self.assertFalse(allow)
        self.assertIn("confirmed-bugs.md", reason)

    def test_empty_deliverable_blocks(self) -> None:
        self.deliver(text="")
        allow, _ = sg.decide("spec_validation", self.wd)
        self.assertFalse(allow)

    def test_present_deliverable_allows(self) -> None:
        self.deliver()
        allow, _ = sg.decide("spec_validation", self.wd)
        self.assertTrue(allow)

    def test_whitespace_only_deliverable_blocks(self) -> None:
        # a report of only spaces is a silent quit; st_size > 0 would wave it through
        self.deliver(text="   \n\t\n")
        allow, reason = sg.decide("spec_validation", self.wd)
        self.assertFalse(allow)
        self.assertIn("bug-report.md", reason)


class TestBlockedSurrender(GateCase):
    def test_blocked_in_spec_allows(self) -> None:
        (self.wd / "spec" / "BLOCKED.md").write_text("tried X, failed because Y\n")
        allow, reason = sg.decide("spec_validation", self.wd)
        self.assertTrue(allow)
        self.assertIn("declared failure", reason)

    def test_blocked_at_root_allows(self) -> None:
        (self.wd / "BLOCKED.md").write_text("blocked\n")
        allow, _ = sg.decide("spec_validation", self.wd)
        self.assertTrue(allow)

    def test_empty_blocked_does_not_count(self) -> None:
        (self.wd / "spec" / "BLOCKED.md").write_text("")
        allow, _ = sg.decide("spec_validation", self.wd)
        self.assertFalse(allow)

    def test_whitespace_only_blocked_does_not_count(self) -> None:
        (self.wd / "spec" / "BLOCKED.md").write_text("   \n")
        self.assertIsNone(sg._blocked_file(self.wd))
        allow, _ = sg.decide("spec_validation", self.wd)
        self.assertFalse(allow)

    def test_blocked_with_live_jobs_allows_but_reports(self) -> None:
        # Surrender is terminal, but never silent about orphaned jobs.
        (self.wd / "spec" / "BLOCKED.md").write_text("stuck\n")
        self.spawn_sleeper(self.wd / "spec" / "output" / "job.out.pid")
        allow, reason = sg.decide("spec_validation", self.wd)
        self.assertTrue(allow)
        self.assertIn("left behind", reason)
        self.assertIn("job.out.pid", reason)


class TestFuse(GateCase):
    def test_fuse_opens_at_cap(self) -> None:
        (self.wd / sg.STATE_DIRNAME).mkdir()
        (self.wd / sg.STATE_DIRNAME / "blocks").write_text(f"{sg.DEFAULT_CAP}\n")
        allow, reason = sg.decide("spec_validation", self.wd)
        self.assertTrue(allow)
        self.assertIn("fuse", reason)
        self.assertTrue((self.wd / sg.STATE_DIRNAME / "FAILED-HOOK-CAP").is_file())

    def test_cap_env_override(self) -> None:
        os.environ["SPECULA_STOP_GATE_CAP"] = "1"
        (self.wd / sg.STATE_DIRNAME).mkdir()
        (self.wd / sg.STATE_DIRNAME / "blocks").write_text("1\n")
        allow, _ = sg.decide("spec_validation", self.wd)
        self.assertTrue(allow)

    def test_below_cap_still_blocks(self) -> None:
        (self.wd / sg.STATE_DIRNAME).mkdir()
        (self.wd / sg.STATE_DIRNAME / "blocks").write_text(f"{sg.DEFAULT_CAP - 1}\n")
        allow, _ = sg.decide("spec_validation", self.wd)
        self.assertFalse(allow)

    def test_reset_state(self) -> None:
        sd = self.wd / sg.STATE_DIRNAME
        sd.mkdir()
        (sd / "blocks").write_text("3\n")
        (sd / "FAILED-HOOK-CAP").write_text("x\n")
        (sd / "gate.log").write_text("audit\n")
        sg.reset_state(self.wd)
        self.assertFalse((sd / "blocks").exists())
        self.assertFalse((sd / "FAILED-HOOK-CAP").exists())
        self.assertTrue((sd / "gate.log").exists())  # audit trail survives

    def test_reset_cli(self) -> None:
        # the contract shell adapters actually invoke: `stop_gate.py reset <wd>`
        sd = self.wd / sg.STATE_DIRNAME
        sd.mkdir()
        (sd / "blocks").write_text("3\n")
        (sd / "FAILED-HOOK-CAP").write_text("x\n")
        rc = sg.main(["reset", str(self.wd)])
        self.assertEqual(rc, 0)
        self.assertFalse((sd / "blocks").exists())
        self.assertFalse((sd / "FAILED-HOOK-CAP").exists())


class TestLivePids(GateCase):
    def test_live_background_job_blocks(self) -> None:
        self.deliver()  # deliverable present: the pid check must fire first anyway
        self.spawn_sleeper(self.wd / "spec" / "output" / "MC_run1.out.pid")
        allow, reason = sg.decide("spec_validation", self.wd)
        self.assertFalse(allow)
        self.assertIn("MC_run1.out.pid", reason)
        self.assertIn("wait_for_pid.sh", reason)

    def test_dead_pid_allows(self) -> None:
        self.deliver()
        proc = subprocess.Popen(["true"])
        proc.wait()
        pf = self.wd / "spec" / "output" / "done.out.pid"
        pf.parent.mkdir(parents=True)
        pf.write_text(f"{proc.pid}\n")
        allow, _ = sg.decide("spec_validation", self.wd)
        self.assertTrue(allow)

    @unittest.skipUnless(Path("/proc/self/stat").exists(), "needs /proc for start-time")
    def test_reused_pid_skipped(self) -> None:
        # a live pid whose start time postdates the pid-file mtime by more than
        # the tolerance is a reused pid, not the recorded job -> allow the stop
        self.deliver()
        pf = self.wd / "spec" / "output" / "MC_run1.out.pid"
        self.spawn_sleeper(pf)
        old = pf.stat().st_mtime - sg.PID_REUSE_TOLERANCE_S - 100
        os.utime(pf, (old, old))
        allow, _ = sg.decide("spec_validation", self.wd)
        self.assertTrue(allow)

    def test_own_agent_pid_at_root_ignored(self) -> None:
        # The launcher writes the phase agent's own pid at the work-dir root;
        # that process is alive while its hook runs and must not self-block.
        self.deliver()
        (self.wd / "spec-validation.pid").write_text(f"{os.getpid()}\n")
        allow, _ = sg.decide("spec_validation", self.wd)
        self.assertTrue(allow)

    def test_ancestor_pid_ignored_anywhere(self) -> None:
        self.deliver()
        (self.wd / "spec" / "self.pid").write_text(f"{os.getpid()}\n")
        allow, _ = sg.decide("spec_validation", self.wd)
        self.assertTrue(allow)

    def test_garbage_pid_file_ignored(self) -> None:
        self.deliver()
        (self.wd / "spec" / "junk.pid").write_text("not-a-pid\n")
        allow, _ = sg.decide("spec_validation", self.wd)
        self.assertTrue(allow)

    def test_state_dir_pid_ignored(self) -> None:
        self.deliver()
        sd = self.wd / sg.STATE_DIRNAME
        sd.mkdir()
        self.spawn_sleeper(sd / "x.pid")
        allow, _ = sg.decide("spec_validation", self.wd)
        self.assertTrue(allow)

    def test_pid_in_pruned_states_dir_ignored(self) -> None:
        # TLC metadirs (states/) can hold millions of files; the scan prunes
        # them, so a pid file in there is invisible by design.
        self.deliver()
        self.spawn_sleeper(self.wd / "spec" / "output" / "states" / "x.out.pid")
        allow, _ = sg.decide("spec_validation", self.wd)
        self.assertTrue(allow)

    def test_pid_beyond_depth_limit_ignored(self) -> None:
        self.deliver()
        deep = self.wd / "a" / "b" / "c" / "d" / "e" / "f"
        self.spawn_sleeper(deep / "x.pid")
        allow, _ = sg.decide("spec_validation", self.wd)
        self.assertTrue(allow)

    def test_pid_within_depth_limit_found(self) -> None:
        self.deliver()
        self.spawn_sleeper(self.wd / "a" / "b" / "c" / "d" / "x.pid")
        allow, _ = sg.decide("spec_validation", self.wd)
        self.assertFalse(allow)


class TestHookEntry(GateCase):
    """The claude/codex subcommands, driven exactly as the CLIs drive them:
    by file path, hook JSON on stdin, decision JSON on stdout."""

    def run_hook(
        self,
        flavor: str,
        phase: str = "spec_validation",
        gate_work_dir: Path | None = None,
    ) -> tuple[int, str]:
        env = os.environ.copy()
        env["SPECULA_PHASE"] = phase
        env["SPECULA_WORK_DIR"] = str(self.wd)
        if gate_work_dir is not None:
            env["SPECULA_STOP_GATE_WORK_DIR"] = str(gate_work_dir)
        r = subprocess.run(
            [sys.executable, str(GATE), flavor],
            input=json.dumps({"hook_event_name": "Stop", "stop_hook_active": False}),
            capture_output=True,
            text=True,
            env=env,
        )
        return r.returncode, r.stdout

    def test_claude_block_wire_contract(self) -> None:
        rc, out = self.run_hook("claude")
        self.assertEqual(rc, 0)
        decision = json.loads(out)
        self.assertEqual(decision["decision"], "block")
        self.assertIn("bug-report.md", decision["reason"])

    def test_codex_block_wire_contract(self) -> None:
        rc, out = self.run_hook("codex")
        self.assertEqual(rc, 0)
        self.assertEqual(json.loads(out)["decision"], "block")

    def test_allow_is_silent(self) -> None:
        self.deliver()
        rc, out = self.run_hook("claude")
        self.assertEqual(rc, 0)
        self.assertEqual(out, "")

    def test_block_increments_counter_and_logs(self) -> None:
        self.run_hook("claude")
        self.run_hook("claude")
        self.assertEqual(sg._read_blocks(self.wd), 2)
        log = (self.wd / sg.STATE_DIRNAME / "gate.log").read_text()
        self.assertEqual(log.count("block"), 2)

    def test_parallel_worker_scope_ignores_sibling_pid_and_isolates_fuse(self) -> None:
        scope_a = self.wd / "confirmation" / "MC-1"
        scope_b = self.wd / "confirmation" / "MC-2"
        scope_a.mkdir(parents=True)
        scope_b.mkdir(parents=True)
        self.spawn_sleeper(scope_b / "worktree" / "job.out.pid")

        rc_a, out_a = self.run_hook("claude", "bug_confirmation_turn", scope_a)
        rc_b, out_b = self.run_hook("claude", "bug_confirmation_turn", scope_b)

        self.assertEqual((rc_a, out_a), (0, ""))
        self.assertEqual(rc_b, 0)
        self.assertIn("job.out.pid", json.loads(out_b)["reason"])
        self.assertEqual(sg._read_blocks(scope_a), 0)
        self.assertEqual(sg._read_blocks(scope_b), 1)

    def test_unwritable_state_fails_open(self) -> None:
        os.chmod(self.wd, 0o500)
        self.addCleanup(os.chmod, self.wd, 0o700)
        rc, out = self.run_hook("claude")
        self.assertEqual(rc, 0)
        self.assertEqual(out, "")

    def test_garbage_stdin_fails_open_on_no_context(self) -> None:
        r = subprocess.run(
            [sys.executable, str(GATE), "claude"],
            input="not json",
            capture_output=True,
            text=True,
            env={k: v for k, v in os.environ.items() if not k.startswith("SPECULA_")},
        )
        self.assertEqual(r.returncode, 0)
        self.assertEqual(r.stdout, "")

    def test_decide_exception_fails_open(self) -> None:
        # the load-bearing guarantee: a crash inside decide() must allow the
        # stop (exit 0, no block), never wedge a healthy run
        import unittest.mock as mock

        env = os.environ.copy()
        env["SPECULA_PHASE"] = "spec_validation"
        env["SPECULA_WORK_DIR"] = str(self.wd)
        with mock.patch.object(sg, "decide", side_effect=RuntimeError("boom")):
            buf = io.StringIO()
            with redirect_stdout(buf):
                old = sys.stdin
                sys.stdin = io.StringIO(json.dumps({"hook_event_name": "Stop"}))
                try:
                    rc = sg.main(["claude"])
                finally:
                    sys.stdin = old
        self.assertEqual(rc, 0)
        self.assertEqual(buf.getvalue(), "")


class TestAcceptEntry(GateCase):
    def accept(self, phase: str) -> tuple[int, str]:
        r = subprocess.run(
            [sys.executable, str(GATE), "accept", phase, str(self.wd)],
            capture_output=True,
            text=True,
        )
        return r.returncode, r.stdout.strip()

    def test_ok_silent(self) -> None:
        self.deliver()
        rc, out = self.accept("spec_validation")
        self.assertEqual((rc, out), (0, ""))

    def test_missing_deliverable_exit_1(self) -> None:
        rc, out = self.accept("spec_validation")
        self.assertEqual(rc, 1)
        self.assertIn("bug-report.md", out)

    def test_missing_with_fuse_marker_mentions_it(self) -> None:
        (self.wd / sg.STATE_DIRNAME).mkdir()
        (self.wd / sg.STATE_DIRNAME / "FAILED-HOOK-CAP").write_text("x\n")
        rc, out = self.accept("spec_validation")
        self.assertEqual(rc, 1)
        self.assertIn("fuse", out)

    def test_blocked_exit_3(self) -> None:
        (self.wd / "spec" / "BLOCKED.md").write_text("cannot build\n")
        rc, out = self.accept("spec_validation")
        self.assertEqual(rc, 3)
        self.assertIn("BLOCKED.md", out)

    def test_blocked_reports_orphans(self) -> None:
        (self.wd / "spec" / "BLOCKED.md").write_text("stuck\n")
        self.spawn_sleeper(self.wd / "spec" / "output" / "job.out.pid")
        rc, out = self.accept("spec_validation")
        self.assertEqual(rc, 3)
        self.assertIn("job.out.pid", out)

    def test_blocked_surfaces_even_without_contract(self) -> None:
        (self.wd / "spec" / "BLOCKED.md").write_text("cannot build\n")
        rc, _ = self.accept("harness_generation")
        self.assertEqual(rc, 3)

    def test_no_contract_silent_ok(self) -> None:
        rc, out = self.accept("code_analysis")
        self.assertEqual((rc, out), (0, ""))

    def test_deliverable_wins_over_stale_blocked(self) -> None:
        self.deliver()
        (self.wd / "spec" / "BLOCKED.md").write_text("was stuck earlier\n")
        rc, _ = self.accept("spec_validation")
        self.assertEqual(rc, 0)


class TestUsage(unittest.TestCase):
    def test_bad_argv_exit_2(self) -> None:
        buf = io.StringIO()
        with redirect_stdout(buf):
            rc = sg.main(["bogus"])
        self.assertEqual(rc, 2)


if __name__ == "__main__":
    unittest.main()
