"""Fault injection for continuous orchestration with real process signals.

Each test runs the real ``specula run`` controller with the deterministic
continuous fixture adapter, holds a process at a named fault point (a marker
the fixture or ``fixtures/faults/controller.py`` publishes), delivers a real
SIGKILL or SIGTERM, and attaches with ``specula run --run-id`` to check the
recovery invariants of the S2 robustness matrix. No model or agent CLI runs.

Kill modes:
  agent  SIGKILL only the agent process (a crashed or OOM-killed CLI)
  crash  SIGSTOP then SIGKILL the whole controller process tree (power loss)
"""

from __future__ import annotations

import contextlib
import fcntl
import json
import os
import shutil
import signal
import subprocess
import sys
import time
import unittest
from pathlib import Path
from typing import Any

import test_cli_pipeline as fixtures

from specula.phaselib import _MANUAL_SESSION_RESUME_PROMPT
from specula.rules import RULES_SEPARATOR, RULES_TITLE

FIXTURES = Path(__file__).parent / "fixtures"
FAULTS = FIXTURES / "faults"
TIMEOUT = 120.0


def _ppid(pid: str) -> int | None:
    try:
        stat = Path(f"/proc/{pid}/stat").read_text()
    except OSError:
        return None
    return int(stat.rsplit(")", 1)[1].split()[1])


def descendants(root: int) -> list[int]:
    """``root`` and every live process below it (sessions do not hide children)."""
    children: dict[int, list[int]] = {}
    for entry in Path("/proc").iterdir():
        if entry.name.isdigit() and (parent := _ppid(entry.name)) is not None:
            children.setdefault(parent, []).append(int(entry.name))
    found: list[int] = []
    stack = [root]
    while stack:
        pid = stack.pop()
        found.append(pid)
        stack.extend(children.get(pid, []))
    return found


def alive(pid: int) -> bool:
    """A live, non-zombie process."""
    try:
        stat = Path(f"/proc/{pid}/stat").read_text()
    except OSError:
        return False
    return stat.rsplit(")", 1)[1].split()[0] != "Z"


class ContinuousFaults(unittest.TestCase):
    def setUp(self) -> None:
        self.helper = fixtures.CliE2E()
        self.addCleanup(self.helper.doCleanups)
        self.root = self.helper.specroot(("footest",))
        self.work = self.helper.workdir()
        self.source = self.work / "source"
        self.source.mkdir()
        for args in (
            ["init", "-q"],
            ["config", "user.name", "Fixture"],
            ["config", "user.email", "fixture@example.com"],
        ):
            subprocess.run(["git", "-C", str(self.source), *args], check=True)
        (self.source / "logic.txt").write_text("initial\n")
        subprocess.run(["git", "-C", str(self.source), "add", "."], check=True)
        subprocess.run(["git", "-C", str(self.source), "commit", "-qm", "initial"], check=True)
        self.adapters = self.root / "scripts/launch/adapters"
        shutil.copyfile(FIXTURES / "continuous_adapter.py", self.adapters / "continuous_adapter.py")
        for name in ("fake", "claude-code"):
            script = self.adapters / f"{name}.sh"
            script.write_text(
                f'#!/bin/sh\nFIXTURE_ADAPTER={name} exec "{sys.executable}" '
                f'"{self.adapters / "continuous_adapter.py"}" "$@"\n'
            )
            script.chmod(0o755)
        infra = self.root / "scripts/infra"
        infra.mkdir()
        for helper in ("start_background.sh", "wait_for_pid.sh"):
            shutil.copy2(fixtures.REAL_ROOT / "scripts/infra" / helper, infra / helper)
        shutil.copy2(FAULTS / "run_model_check.sh", infra / "run_model_check.sh")
        (infra / "run_model_check.sh").chmod(0o755)  # exec'd by start_background.sh
        shutil.copy2(FAULTS / "usage.sh", self.root / "scripts/exp/usage.sh")
        (self.root / "tools/context_control").mkdir(parents=True)
        shutil.copy2(FAULTS / "compact.py", self.root / "tools/context_control/compact.py")
        self.invocations = 0
        self.processes: list[subprocess.Popen[bytes]] = []
        self.addCleanup(self.reap)

    # ── processes ──
    def environment(self, extra: dict[str, str] | None = None) -> dict[str, str]:
        env = {key: value for key, value in os.environ.items() if key not in fixtures._VOLATILE}
        env["HOME"] = str(self.work)  # no credentials: the real quota endpoint is never reached
        env.update(extra or {})
        return env

    def start(self, *args: str, faults: str = "", quota: bool = False) -> tuple[subprocess.Popen[bytes], Path]:
        """Start a run in the background; ``faults`` holds controller callables."""
        self.invocations += 1
        output = self.work / f"invocation-{self.invocations}.log"
        if faults or quota:
            command = [sys.executable, str(FAULTS / "controller.py"), str(self.root / "src")]
        else:
            command = [sys.executable, str(self.root / "src/specula/cli.py"), "run"]
        extra = {"FAULT_DIR": str(self.adapters), "FAULT_BLOCK": faults}
        if quota:
            extra["FAULT_QUOTA"] = "1"
        with output.open("wb") as stream:
            process = subprocess.Popen(
                [*command, f"--artifact={self.source}", *args],
                cwd=self.work,
                env=self.environment(extra),
                stdout=stream,
                stderr=subprocess.STDOUT,
                start_new_session=True,
            )
        self.processes.append(process)
        return process, output

    def attach(self, *args: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [sys.executable, str(self.root / "src/specula/cli.py"), "run", f"--run-id={self.run_dir().name}", *args],
            cwd=self.work,
            env=self.environment(),
            capture_output=True,
            text=True,
            timeout=TIMEOUT * 2,
        )

    def reap(self) -> None:
        """Kill everything a test left behind: its controllers and orphans."""
        marker = str(self.root)
        for entry in Path("/proc").iterdir():
            if not entry.name.isdigit() or int(entry.name) == os.getpid():
                continue
            with contextlib.suppress(OSError):
                if marker in (entry / "cmdline").read_bytes().decode(errors="replace"):
                    os.kill(int(entry.name), signal.SIGKILL)
        for process in self.processes:
            with contextlib.suppress(OSError):
                os.kill(process.pid, signal.SIGKILL)
            with contextlib.suppress(subprocess.TimeoutExpired):
                process.wait(timeout=5)

    def wait_until(self, condition: Any, what: str, process: subprocess.Popen[bytes] | None = None) -> None:
        deadline = time.monotonic() + TIMEOUT
        while not condition():
            if process is not None and process.poll() is not None:
                self.fail(f"run exited ({process.returncode}) before {what}:\n{self.output(process)}")
            if time.monotonic() > deadline:
                self.fail(f"timed out waiting for {what}")
            time.sleep(0.02)

    def reached(self, point: str, process: subprocess.Popen[bytes]) -> dict[str, Any]:
        path = self.adapters / f"reached-{point}.json"
        self.wait_until(path.is_file, f"fault point {point}", process)
        value: dict[str, Any] = json.loads(path.read_text())
        return value

    def release(self, point: str) -> None:
        (self.adapters / f"release-{point}").touch()

    def output(self, process: subprocess.Popen[bytes]) -> str:
        index = self.processes.index(process) + 1
        return (self.work / f"invocation-{index}.log").read_text(errors="replace")

    def finish(self, process: subprocess.Popen[bytes]) -> int:
        try:
            return process.wait(timeout=TIMEOUT)
        except subprocess.TimeoutExpired:
            self.fail(f"run did not exit:\n{self.output(process)}")

    def crash(self, process: subprocess.Popen[bytes]) -> None:
        """Freeze, then SIGKILL, the controller and every process below it."""
        tree = descendants(process.pid)
        for pid in tree:
            with contextlib.suppress(ProcessLookupError):
                os.kill(pid, signal.SIGSTOP)
        for pid in tree:
            with contextlib.suppress(ProcessLookupError):
                os.kill(pid, signal.SIGKILL)
        process.wait(timeout=TIMEOUT)
        self.wait_until(lambda: not any(alive(pid) for pid in tree), "the killed tree to exit")

    def kill_agent(self, point: str, process: subprocess.Popen[bytes]) -> int:
        """SIGKILL only the agent process held at ``point``; return the run's exit code."""
        agent = self.reached(point, process)["pid"]
        os.kill(agent, signal.SIGKILL)
        return self.finish(process)

    def lock_is_free(self) -> bool:
        descriptor = os.open(self.run_dir() / ".specula-resume/run.lock", os.O_RDWR)
        try:
            fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            return False
        finally:
            os.close(descriptor)
        return True

    def flag(self, *names: str) -> None:
        for name in names:
            (self.adapters / name).touch()

    # ── durable state ──
    def run_dir(self) -> Path:
        return self.helper.sole_run_dir(self.root)

    def target(self) -> Path:
        return self.run_dir() / "footest/.specula-output"

    def state(self) -> dict[str, Any]:
        value: dict[str, Any] = json.loads((self.target() / ".context-control/main-state.json").read_text())
        return value

    def request(self) -> dict[str, Any]:
        value: dict[str, Any] = json.loads((self.target() / ".context-control/confirmation.json").read_text())
        return value

    def repair_loop(self) -> dict[str, Any]:
        value: dict[str, Any] = json.loads((self.run_dir() / "repair-loop.json").read_text())
        return value

    def active(self) -> list[str]:
        return sorted(path.name for path in (self.run_dir() / ".specula-resume/active").glob("*.json"))

    def events(self) -> list[dict[str, Any]]:
        path = self.adapters / "events.jsonl"
        return [json.loads(line) for line in path.read_text().splitlines()] if path.exists() else []

    def mains(self) -> list[dict[str, Any]]:
        return [e for e in self.events() if e["kind"] == "start" and e["name"] == "main"]

    def sessions(self) -> list[str]:
        return [e["session"] for e in self.mains()]

    def starts(self, name: str) -> list[dict[str, Any]]:
        return [e for e in self.events() if e["kind"] == "start" and e["name"] == name]

    def stages(self, session: str) -> list[str]:
        return [e["name"] for e in self.events() if e["kind"] == "stage" and e["session"] == session]

    def prompt(self, call: int) -> str:
        """Main-session prompt of one call, after its single pinned rules block."""
        text = (self.adapters / f"main-prompt-footest-{call}.md").read_text()
        self.assertEqual(text.count(RULES_TITLE), 1, text[:300])
        return text.split(RULES_SEPARATOR, 1)[1]

    def verdict(self, finding: str) -> Path:
        return self.target() / "confirmation" / finding / "verdict.json"

    def report_rows(self, finding: str) -> int:
        return (self.target() / "confirmed-bugs.md").read_text().count(f"| {finding} |")

    def assert_complete(self, result: subprocess.CompletedProcess[str], findings: tuple[str, ...] = ("CR-1",)) -> None:
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(self.state()["stage"], "complete")
        self.assertEqual(self.request()["status"], "completed")
        for finding in findings:
            self.assertEqual(self.report_rows(finding), 1, finding)
        self.assertTrue((self.target() / "bug-severity.md").is_file())
        self.assertTrue((self.run_dir() / "pipeline-summary.md").is_file())
        self.assertEqual(self.active(), [])
        self.assertTrue(self.lock_is_free())

    def assert_resumed_main(self, call: int) -> None:
        self.assertTrue(self.prompt(call).startswith(_MANUAL_SESSION_RESUME_PROMPT), self.prompt(call)[:300])
        self.assertNotIn("# Specula Main Session", self.prompt(call))

    # ── 1. kill -9 mid-analysis ──
    def check_analysis_kill(self, mode: str) -> None:
        self.flag("block-main-1")
        run, _ = self.start("--agent=fake", "footest")
        self.reached("main-1", run)
        work = self.target()
        analysis = {path: path.read_bytes() for path in (work / "modeling-brief.md", work / "analysis-report.md")}
        if mode == "agent":
            self.assertNotEqual(self.kill_agent("main-1", run), 0)
        else:
            self.crash(run)
        self.assertEqual(self.state()["stage"], "main")
        self.assertTrue(self.lock_is_free())

        resumed = self.attach()
        self.assert_complete(resumed)
        self.assertEqual(self.sessions(), ["main-footest-1"] * 2)
        self.assertEqual([e["resumed"] for e in self.mains()], [False, True])
        self.assert_resumed_main(2)
        self.assertEqual(self.stages("main-footest-1"), ["analysis", "validation"])
        for path, content in analysis.items():
            self.assertEqual(path.read_bytes(), content, path)
        self.assertEqual(len(self.starts("CR-1")), 1)

    def test_agent_sigkill_mid_analysis_resumes_the_same_session(self) -> None:
        self.check_analysis_kill("agent")

    def test_crash_mid_analysis_resumes_the_same_session(self) -> None:
        self.check_analysis_kill("crash")

    # ── 2. kill -9 with a background job running ──
    def job(self) -> dict[str, Any]:
        value: dict[str, Any] = json.loads((self.adapters / "job.json").read_text())
        return value

    def jobs_started(self) -> int:
        return sum(e["kind"] == "job" for e in self.events())

    def harvests(self) -> list[tuple[bool, bool]]:
        return [(e["alive"], e["finished"]) for e in self.events() if e["kind"] == "harvest"]

    def test_agent_sigkill_reaps_its_job_and_the_resumed_session_restarts_it(self) -> None:
        self.flag("block-main-1", "background")
        run, _ = self.start("--agent=fake", "footest")
        self.reached("main-1", run)
        job = self.job()["pid"]
        self.assertTrue(list((self.target() / ".stop-gate/background-pids").glob(f"{job}.pid")))
        self.assertNotEqual(self.kill_agent("main-1", run), 0)
        # Jobs in the agent's session are phase-scoped: reaped with the agent.
        self.assertFalse(alive(job))
        self.assertNotIn("Finished in", (self.target() / "job.log").read_text())
        self.assertTrue(self.lock_is_free())

        self.release("job")
        resumed = self.attach()
        self.assert_complete(resumed)
        self.assertEqual(self.sessions(), ["main-footest-1"] * 2)
        self.assertEqual(self.jobs_started(), 2)
        self.assertEqual(self.harvests(), [(False, True)])

    def test_escaped_job_holding_the_run_lock_defers_attach_until_it_ends(self) -> None:
        self.flag("block-main-1", "background", "background-detached", "background-lock")
        run, _ = self.start("--agent=fake", "footest")
        self.reached("main-1", run)
        job = self.job()["pid"]
        self.assertNotEqual(self.kill_agent("main-1", run), 0)
        self.assertTrue(alive(job))
        active = self.active()

        refused = self.attach()
        self.assertEqual(refused.returncode, 1, refused.stdout + refused.stderr)
        self.assertIn("still has a live phase or agent", refused.stderr)
        self.assertEqual((self.active(), self.state()["stage"]), (active, "main"))
        self.assertEqual(len(self.mains()), 1)

        self.release("job")
        self.wait_until(lambda: not alive(job), "the background job to finish")
        resumed = self.attach()
        self.assert_complete(resumed)
        self.assertEqual(self.sessions(), ["main-footest-1"] * 2)
        self.assertEqual((self.jobs_started(), self.harvests()), (1, [(False, True)]))

    def test_unharvested_escaped_job_blocks_the_handoff(self) -> None:
        self.flag("block-main-1", "background", "background-detached", "abandon-job")
        run, _ = self.start("--agent=fake", "footest")
        self.reached("main-1", run)
        job = self.job()["pid"]
        self.assertNotEqual(self.kill_agent("main-1", run), 0)
        self.assertTrue(alive(job))
        self.assertTrue(self.lock_is_free())

        # The resumed session hands off while its registered job still runs:
        # rejected, resumed automatically twice with the reason, then failed.
        early = self.attach()
        self.assertEqual(early.returncode, 1, early.stdout + early.stderr)
        self.assertEqual(self.request()["status"], "rejected")
        self.assertIn("live background job", self.state()["rejection"])
        self.assertEqual(len(self.mains()), 4)
        self.assertEqual(self.starts("consolidate") + self.starts("CR-1"), [])
        self.assertTrue(alive(job))

        self.release("job")
        self.wait_until(lambda: not alive(job), "the background job to finish")
        resumed = self.attach()
        self.assert_complete(resumed)
        self.assertEqual(set(self.sessions()), {"main-footest-1"})
        self.assertIn("Confirmation Request Not Accepted", self.prompt(len(self.mains())))
        self.assertEqual(len(self.starts("CR-1")), 1)

    # ── 3. kill -9 during the native-compaction helper ──
    def test_sigkill_of_the_compaction_helper_continues_the_same_session(self) -> None:
        self.flag("compact-1", "block-compact")
        run, _ = self.start("--agent=fake", "footest")
        helper = self.reached("compact", run)["pid"]
        os.kill(helper, signal.SIGKILL)
        self.assertEqual(self.finish(run), 0, self.output(run))
        self.assertIn("Context compaction failed; continuing", self.output(run))
        self.assertEqual(self.sessions(), ["main-footest-1"] * 2)
        self.assertEqual([e["session"] for e in self.starts("compact")], ["main-footest-1"])
        continued = self.prompt(2)
        self.assertIn("Context compaction failed", continued)
        self.assertIn(str(self.target() / "notes/handoff.md"), continued)
        receipts = list(self.target().glob(".context-control/invocation-*/1/compaction.json"))
        self.assertEqual([path.read_text() for path in receipts], ['{"status": "comp'])
        self.assertEqual(self.state()["stage"], "complete")
        self.assertEqual(self.report_rows("CR-1"), 1)

    def test_crash_during_compaction_resumes_the_same_session(self) -> None:
        self.flag("compact-1", "block-compact")
        run, _ = self.start("--agent=fake", "footest")
        self.reached("compact", run)
        self.crash(run)
        (self.adapters / "block-compact").unlink()
        resumed = self.attach()
        self.assert_complete(resumed)
        self.assertEqual(self.sessions(), ["main-footest-1"] * 2)
        self.assert_resumed_main(2)
        self.assertEqual(len(self.starts("compact")), 1)
        self.assertEqual(self.stages("main-footest-1"), ["analysis", "validation"])

    # ── 4. kill after the yield, before confirmation starts ──
    def check_yield_kill(self, fault: str, status: str) -> None:
        run, _ = self.start("--agent=fake", "footest", faults=fault)
        self.reached(fault.split(":")[1], run)
        self.assertEqual(self.request()["status"], status)
        self.assertEqual(self.state()["stage"], "confirm")
        self.crash(run)
        resumed = self.attach()
        self.assert_complete(resumed)
        self.assertEqual(len(self.mains()), 1)
        self.assertEqual(len(self.starts("consolidate")), 1)
        self.assertEqual(len(self.starts("CR-1")), 1)
        self.assertEqual(self.request()["session_id"], "main-footest-1")

    def test_crash_after_the_yield_dispatches_the_pending_request_once(self) -> None:
        self.check_yield_kill("specula.continuous:ContinuousRun._dispatch", "pending")

    def test_crash_after_dispatch_is_recorded_confirms_once(self) -> None:
        self.check_yield_kill("specula.pipelinelib:Pipeline.run_phase4_confirmation_for", "confirming")

    # ── 5. kill -9 of the controller mid-confirmation ──
    def hold_second_worker(self) -> subprocess.Popen[bytes]:
        self.flag("cr2", "block-worker-CR-2")
        run, _ = self.start("--agent=fake", "footest")
        self.reached("worker-CR-2", run)
        self.wait_until(self.verdict("CR-1").is_file, "the CR-1 verdict", run)
        self.assertEqual(self.request()["status"], "confirming")
        return run

    def test_controller_sigkill_mid_confirmation_keeps_one_verdict_per_finding(self) -> None:
        run = self.hold_second_worker()
        os.kill(run.pid, signal.SIGKILL)
        run.wait(timeout=TIMEOUT)
        self.assertFalse(self.lock_is_free())  # the confirmation phase and its worker live on
        refused = self.attach()
        self.assertEqual(refused.returncode, 1, refused.stdout + refused.stderr)
        self.assertIn("still has a live phase or agent", refused.stderr)

        self.release("worker-CR-2")
        self.wait_until(self.lock_is_free, "the orphaned confirmation to finish")
        resumed = self.attach()
        self.assert_complete(resumed, ("CR-1", "CR-2"))
        self.assertEqual(len(self.mains()), 1)
        self.assertEqual((len(self.starts("CR-1")), len(self.starts("CR-2"))), (1, 1))

    def test_crash_mid_confirmation_reruns_only_the_unfinished_worker(self) -> None:
        run = self.hold_second_worker()
        self.crash(run)
        verdict = self.verdict("CR-1").read_bytes()
        (self.adapters / "block-worker-CR-2").unlink()
        resumed = self.attach()
        self.assert_complete(resumed, ("CR-1", "CR-2"))
        self.assertEqual(len(self.mains()), 1)
        self.assertEqual(len(self.starts("CR-1")), 1)
        self.assertEqual([e["resumed"] for e in self.starts("CR-2")], [False, True])
        self.assertEqual(self.verdict("CR-1").read_bytes(), verdict)

    # ── 6. kill during the repair resume of the main session ──
    def check_repair_kill(self, mode: str) -> None:
        self.flag("repair", "block-main-2")
        run, _ = self.start("--agent=fake", "footest")
        self.reached("main-2", run)
        if mode == "agent":
            self.assertNotEqual(self.kill_agent("main-2", run), 0)
        else:
            self.crash(run)
        state = self.state()
        self.assertEqual((state["stage"], state["repair_round"]), ("main", 1))
        self.assertEqual((self.repair_loop()["round"], self.repair_loop()["pending"]), (1, ["footest"]))
        self.assertTrue((self.target() / "spec/.repair-phase3-snapshot.json").is_file())

        resumed = self.attach()
        self.assert_complete(resumed)
        self.assertEqual(self.sessions(), ["main-footest-1"] * 3)
        self.assert_resumed_main(3)
        self.assertIn("## Repair Round 1", self.prompt(3))
        self.assertEqual((self.repair_loop()["round"], self.repair_loop()["pending"]), (1, []))
        self.assertEqual((self.state()["repair_round"], self.request()["repair_round"]), (1, 1))
        self.assertEqual(len(self.starts("MC-1")), 1)
        self.assertEqual(self.stages("main-footest-1"), ["analysis", "validation", "repair-1"])
        rr = (self.target() / "spec/repair-requests/RR-001.md").read_text()
        self.assertIn("status: CONSUMED", rr)
        self.assertEqual(rr.count("- r1: Fixed model"), 1)
        self.assertTrue((self.target() / "confirmed-bugs-round-1.md").is_file())
        self.assertFalse((self.target() / "spec/.repair-phase3-snapshot.json").exists())
        self.assertFalse((self.target() / "spec/.repair-phase3-commit.json").exists())

    def test_agent_sigkill_during_the_repair_resume_keeps_the_round(self) -> None:
        self.check_repair_kill("agent")

    def test_crash_during_the_repair_resume_keeps_the_round(self) -> None:
        self.check_repair_kill("crash")

    # ── 7. quota pause ──
    def test_rate_limit_pause_interrupted_by_sigterm_resumes_the_same_session(self) -> None:
        self.flag("rate-limit-1")
        run, _ = self.start("--agent=fake", "footest")
        self.wait_until(lambda: "after rate limit" in self.output(run), "the rate-limit pause", run)
        self.assertEqual(self.sessions(), ["main-footest-1"])
        os.kill(run.pid, signal.SIGTERM)
        self.assertEqual(self.finish(run), 143, self.output(run))
        self.assertTrue(self.lock_is_free())
        self.assertEqual(self.state()["stage"], "main")

        (self.adapters / "rate-limit-1").unlink()
        resumed = self.attach()
        self.assert_complete(resumed)
        self.assertEqual(self.sessions(), ["main-footest-1"] * 2)
        self.assert_resumed_main(2)

    def quota_pause_before_repair(self) -> subprocess.Popen[bytes]:
        self.flag("repair", "quota-after-MC-1")
        run, _ = self.start("--agent=claude-code", "footest", quota=True)
        self.reached("quota", run)
        state = self.state()
        self.assertEqual((state["stage"], state["repair_round"]), ("main", 1))
        self.assertEqual(self.repair_loop()["round"], 1)
        self.assertEqual(len(self.mains()), 1)
        return run

    def assert_repair_completed_in_one_session(self) -> None:
        self.assertEqual(self.sessions(), ["main-footest-1"] * 2)
        self.assertIn("## Repair Round 1", self.prompt(2))
        self.assertEqual((self.repair_loop()["round"], self.repair_loop()["pending"]), (1, []))
        self.assertEqual(len(self.starts("MC-1")), 1)

    def test_quota_pause_before_the_repair_resume_continues_the_same_session(self) -> None:
        run = self.quota_pause_before_repair()
        (self.adapters / "quota-over").unlink()
        self.release("quota")
        self.assertEqual(self.finish(run), 0, self.output(run))
        self.assertIn("Quota: 5h=99%", self.output(run))
        self.assertEqual(self.state()["stage"], "complete")
        self.assert_repair_completed_in_one_session()

    # ── 8. SIGTERM to the controller ──
    def test_sigterm_during_a_quota_pause_releases_the_lock(self) -> None:
        run = self.quota_pause_before_repair()
        os.kill(run.pid, signal.SIGTERM)
        self.finish(run)
        self.assertTrue(self.lock_is_free())
        (self.adapters / "quota-over").unlink()
        resumed = self.attach("--agent=claude-code")
        self.assert_complete(resumed)
        self.assert_repair_completed_in_one_session()
        self.assert_resumed_main(2)

    def test_sigterm_mid_main_session_releases_the_lock_and_resumes(self) -> None:
        self.flag("block-main-1")
        run, _ = self.start("--agent=fake", "footest")
        agent = self.reached("main-1", run)["pid"]
        os.kill(run.pid, signal.SIGTERM)
        self.assertEqual(self.finish(run), 143, self.output(run))
        self.assertFalse(alive(agent))
        self.assertTrue(self.lock_is_free())
        self.assertIn("finished (exit 143)", (self.run_dir() / "pipeline.log").read_text())
        (self.adapters / "block-main-1").unlink()
        resumed = self.attach()
        self.assert_complete(resumed)
        self.assertEqual(self.sessions(), ["main-footest-1"] * 2)
        self.assert_resumed_main(2)

    def test_sigterm_mid_confirmation_resumes_without_duplicate_verdicts(self) -> None:
        run = self.hold_second_worker()
        worker = self.reached("worker-CR-2", run)["pid"]
        os.kill(run.pid, signal.SIGTERM)
        self.assertEqual(self.finish(run), 143, self.output(run))
        self.assertFalse(alive(worker))
        self.assertTrue(self.lock_is_free())
        (self.adapters / "block-worker-CR-2").unlink()
        resumed = self.attach()
        self.assert_complete(resumed, ("CR-1", "CR-2"))
        self.assertEqual(len(self.mains()), 1)
        self.assertEqual((len(self.starts("CR-1")), len(self.starts("CR-2"))), (1, 2))

    # ── 9. --fresh-context after a crash ──
    def assert_fresh_session(self, resumed: subprocess.CompletedProcess[str], findings: tuple[str, ...]) -> None:
        self.assert_complete(resumed, findings)
        self.assertEqual(self.sessions()[-1], "main-footest-2")
        self.assertFalse(self.mains()[-1]["resumed"])
        self.assertEqual(self.request()["session_id"], "main-footest-2")
        self.assertEqual(self.state()["context"], "fresh")
        self.assertEqual(self.stages("main-footest-2"), ["analysis", "validation"])

    def test_fresh_context_after_a_crash_mid_main_starts_a_new_session(self) -> None:
        self.flag("block-main-1")
        run, _ = self.start("--agent=fake", "footest")
        self.reached("main-1", run)
        self.crash(run)
        (self.adapters / "block-main-1").unlink()
        fresh = self.attach("--fresh-context")
        self.assert_fresh_session(fresh, ("CR-1",))
        self.assertEqual(self.sessions(), ["main-footest-1", "main-footest-2"])
        self.assertIn("## Continue From Existing Work", self.prompt(2))
        archived = list(self.target().glob(".context-control/abandoned/*/main-state.json"))
        self.assertEqual(len(archived), 1)

    def test_fresh_context_after_a_crash_after_the_yield_ignores_the_old_request(self) -> None:
        run, _ = self.start("--agent=fake", "footest", faults="specula.continuous:ContinuousRun._dispatch")
        self.reached("ContinuousRun._dispatch", run)
        self.crash(run)
        (self.adapters / "release-ContinuousRun._dispatch").touch()
        fresh = self.attach("--fresh-context")
        self.assert_fresh_session(fresh, ("CR-1",))
        archived = list(self.target().glob(".context-control/abandoned/*/confirmation.json"))
        self.assertEqual([json.loads(path.read_text())["session_id"] for path in archived], ["main-footest-1"])
        self.assertEqual(len(self.starts("consolidate")), 1)
        self.assertEqual(len(self.starts("CR-1")), 1)

    def test_fresh_context_after_a_crash_mid_confirmation_ignores_the_abandoned_batch(self) -> None:
        run = self.hold_second_worker()
        self.crash(run)
        (self.adapters / "block-worker-CR-2").unlink()
        fresh = self.attach("--fresh-context")
        self.assert_fresh_session(fresh, ("CR-1", "CR-2"))
        # The abandoned batch's verdicts and worker sessions are not reused.
        self.assertEqual(len(self.starts("CR-1")), 2)
        self.assertEqual([e["resumed"] for e in self.starts("CR-2")], [False, False])

    def test_crash_during_the_fresh_context_abandonment_is_finished_by_the_next_attach(self) -> None:
        self.flag("block-main-1")
        run, _ = self.start("--agent=fake", "footest")
        self.reached("main-1", run)
        self.crash(run)
        (self.adapters / "block-main-1").unlink()
        fault = "specula.pipelinelib:Pipeline.prepare_repair_state"
        fresh, _ = self.start(f"--run-id={self.run_dir().name}", "--fresh-context", faults=fault)
        self.reached("Pipeline.prepare_repair_state", fresh)
        self.assertFalse((self.target() / ".context-control/main-state.json").exists())
        self.crash(fresh)
        # A plain attach finishes the abandonment instead of finding no state.
        resumed = self.attach()
        self.assert_fresh_session(resumed, ("CR-1",))
        self.assertEqual(self.sessions(), ["main-footest-1", "main-footest-2"])
        control = self.target() / ".context-control"
        self.assertFalse((control / "abandoning.json").exists())
        archived = list(control.glob("abandoned/*/main-state.json"))
        self.assertEqual(len(archived), 1)
        self.assertEqual(json.loads(archived[0].read_text())["context"], "original")

    # ── 10. crash after classification, before the summary ──
    def test_crash_after_classification_does_not_repeat_it(self) -> None:
        run, _ = self.start("--agent=fake", "footest", faults="specula.pipelinelib:Pipeline.generate_summary")
        self.reached("Pipeline.generate_summary", run)
        self.assertEqual(self.state()["stage"], "classified")
        self.crash(run)
        resumed = self.attach()
        self.assert_complete(resumed)
        self.assertIn("Phase 4b already completed for every target", resumed.stdout)
        self.assertEqual(len(self.starts("classify")), 1)
        self.assertEqual((len(self.mains()), len(self.starts("CR-1"))), (1, 1))

    def test_crash_during_classification_reruns_only_classification(self) -> None:
        self.flag("block-classify")
        run, _ = self.start("--agent=fake", "footest")
        self.reached("classify", run)
        self.assertEqual(self.state()["stage"], "closed")
        self.crash(run)
        (self.adapters / "block-classify").unlink()
        resumed = self.attach()
        self.assert_complete(resumed)
        self.assertEqual(len(self.starts("classify")), 2)
        self.assertEqual((len(self.mains()), len(self.starts("CR-1"))), (1, 1))


if __name__ == "__main__":
    unittest.main()
