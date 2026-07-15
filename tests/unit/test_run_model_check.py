"""Integration-style unit tests for the TLC shell wrappers.

The fixtures build a minimal temporary Specula root with an empty
``tla2tools.jar`` and a fake ``java`` executable.  This exercises admission and
the background-launch handshake without starting a JVM or a real model check.
"""

from __future__ import annotations

import contextlib
import fcntl
import hashlib
import json
import os
import shutil
import signal
import subprocess
import tempfile
import time
import unittest
from pathlib import Path

from specula import stop_gate as sg

REPO_ROOT = Path(__file__).resolve().parents[2]


class RunModelCheckTests(unittest.TestCase):
    def setUp(self) -> None:
        self._temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self._temporary.cleanup)
        self.root = Path(self._temporary.name)
        self.work = self.root / "work"
        self.bin = self.root / "bin"
        self.tmp = self.root / "tmp"
        for directory in (self.work, self.bin, self.tmp, self.root / "lib", self.root / "src/specula"):
            directory.mkdir(parents=True, exist_ok=True)

        for relative in (
            "scripts/tlc/run_model_check.sh",
            "scripts/tlc/PrintAvailableProcessors.java",
            "scripts/infra/start_background.sh",
        ):
            destination = self.root / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(REPO_ROOT / relative, destination)
        (self.root / "scripts/infra/run_model_check.sh").symlink_to("../tlc/run_model_check.sh")
        shutil.copy2(REPO_ROOT / "src/specula/tlc_resources.py", self.root / "src/specula/tlc_resources.py")

        # The wrapper only checks that the jar exists; fake java never reads it.
        (self.root / "lib/tla2tools.jar").touch()
        self.spec = self.work / "MC.tla"
        self.config = self.work / "MC.cfg"
        self.spec.write_text("---- MODULE MC ----\n====\n")
        self.config.write_text("SPECIFICATION Spec\n")

        self.java_log = self.root / "java.args"
        fake_java = self.bin / "java"
        fake_java.write_text(
            "#!/bin/sh\n"
            ': "${FAKE_JAVA_LOG:?}"\n'
            'if [ "${1##*/}" = PrintAvailableProcessors.java ]; then\n'
            '  [ -f "$1" ] || exit 91\n'
            "  printf '6\\n'\n"
            "  exit 0\n"
            "fi\n"
            'printf \'%s\\n\' "$@" > "$FAKE_JAVA_LOG"\n'
            'if [ -n "${FAKE_JAVA_PID:-}" ]; then printf \'%s\\n\' "$$" > "$FAKE_JAVA_PID"; fi\n'
            'if [ "${FAKE_JAVA_HOLD:-0}" = 1 ]; then\n'
            "  exec sleep 60\n"
            "fi\n"
            'exit "${FAKE_JAVA_EXIT:-0}"\n'
        )
        fake_java.chmod(0o755)

    def env(self, **updates: str) -> dict[str, str]:
        env = os.environ.copy()
        for name in (
            "SPECULA_RUN_DIR",
            "SPECULA_WORK_DIR",
            "SPECULA_STOP_GATE_WORK_DIR",
            "SPECULA_TLC_ADMISSION_STATUS",
            "SPECULA_TLC_MEMORY_LIMIT",
            "SPECULA_TLC_WORKER_LIMIT",
            "SPECULA_TLC_RESOURCE_DIR",
            "SPECULA_TLC_SCOPE",
            "TLC_STATE_DIR",
            "FAKE_JAVA_HOLD",
            "FAKE_JAVA_EXIT",
            "FAKE_JAVA_PID",
            "SPECULA_TLC_AUTO_WORKERS",
        ):
            env.pop(name, None)
        env.update(
            {
                "PATH": f"{self.bin}{os.pathsep}{env['PATH']}",
                "SPECULA_ROOT": str(self.root),
                "SPECULA_TLC_MEMORY_LIMIT": "4G",
                "SPECULA_TLC_RESOURCE_DIR": str(self.root / "resources"),
                "SPECULA_TLC_SCOPE": str(self.root / "run"),
                "TMPDIR": str(self.tmp),
                "FAKE_JAVA_LOG": str(self.java_log),
            }
        )
        env.update(updates)
        return env

    def wrapper_args(self, log_name: str) -> list[str]:
        return [
            "-s",
            str(self.spec),
            "-c",
            str(self.config),
            "-m",
            "1G",
            "-M",
            "1G",
            "-t",
            "0",
            "-k",
            "0",
            "-o",
            str(self.work / log_name),
        ]

    def run_wrapper(self, env: dict[str, str], log_name: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [str(self.root / "scripts/tlc/run_model_check.sh"), *self.wrapper_args(log_name)],
            cwd=self.work,
            env=env,
            capture_output=True,
            text=True,
            timeout=10,
            check=False,
        )

    def test_explicit_worker_budget_rejects_before_java_starts(self) -> None:
        result = self.run_wrapper(self.env(SPECULA_TLC_WORKER_LIMIT="4"), "rejected.log")

        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        self.assertIn("worker limit: 4", result.stdout)
        self.assertIn("this request workers: 6 (auto)", result.stdout)
        self.assertIn("result: rejected", result.stdout)
        self.assertIn("aggregate workers would be 6, above 4", result.stdout)
        self.assertFalse(self.java_log.exists(), "Java must not start when admission is rejected")

    def test_success_preserves_jvm_memory_flags_and_workers_auto(self) -> None:
        result = self.run_wrapper(self.env(), "accepted.log")

        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("worker limit: unbounded (report only)", result.stdout)
        self.assertIn("this request workers: 6 (auto)", result.stdout)
        self.assertIn("result: admitted", result.stdout)
        argv = self.java_log.read_text().splitlines()
        self.assertIn("-XX:MaxDirectMemorySize=1G", argv)
        self.assertIn("-Xmx1G", argv)
        self.assertIn("-Xms1G", argv)
        self.assertEqual(argv[argv.index("-workers") + 1], "auto")
        self.assertEqual(argv[argv.index("-cp") + 1], str(self.root / "lib/tla2tools.jar"))

    def test_specula_root_relocation_uses_one_runtime_root(self) -> None:
        relocated_wrapper = self.root / "relocated/scripts/tlc/run_model_check.sh"
        relocated_wrapper.parent.mkdir(parents=True)
        relocated_wrapper.symlink_to(self.root / "scripts/tlc/run_model_check.sh")

        result = subprocess.run(
            [str(relocated_wrapper), *self.wrapper_args("relocated.log")],
            cwd=self.work,
            env=self.env(),
            capture_output=True,
            text=True,
            timeout=10,
            check=False,
        )

        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        argv = self.java_log.read_text().splitlines()
        self.assertEqual(argv[argv.index("-cp") + 1], str(self.root / "lib/tla2tools.jar"))

    def test_tlc_exit_code_is_preserved_and_reservation_released(self) -> None:
        result = self.run_wrapper(self.env(FAKE_JAVA_EXIT="12"), "violation.log")

        self.assertEqual(result.returncode, 12, result.stdout + result.stderr)
        ledger_file = next((self.root / "resources").glob("*/ledger.json"))
        self.assertEqual(json.loads(ledger_file.read_text())["reservations"], {})

    def test_sigkill_wrapper_keeps_surviving_tlc_reserved(self) -> None:
        gate_dir = self.root / "direct-gate"
        gate_dir.mkdir()
        env = self.env(
            FAKE_JAVA_HOLD="1",
            SPECULA_TLC_MEMORY_LIMIT="3G",
            SPECULA_WORK_DIR=str(gate_dir),
        )
        wrapper = subprocess.Popen(
            [str(self.root / "scripts/tlc/run_model_check.sh"), *self.wrapper_args("killed-wrapper.log")],
            cwd=self.work,
            env=env,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
        self.addCleanup(self._terminate, wrapper.pid)

        deadline = time.monotonic() + 3
        ledger_files: list[Path] = []
        while time.monotonic() < deadline:
            ledger_files = list((self.root / "resources").glob("*/ledger.json"))
            if self.java_log.exists() and ledger_files:
                break
            time.sleep(0.02)
        self.assertTrue(self.java_log.exists(), "first fake TLC did not start")
        self.assertEqual(len(ledger_files), 1)
        ledger = json.loads(ledger_files[0].read_text())
        reservations = list(ledger["reservations"].values())
        self.assertEqual(len(reservations), 1)
        tlc_pid = int(reservations[0]["pid"])
        self.addCleanup(self._terminate, tlc_pid)

        os.kill(wrapper.pid, signal.SIGKILL)
        wrapper.wait(timeout=3)
        assert wrapper.stdout is not None and wrapper.stderr is not None
        wrapper.stdout.close()
        wrapper.stderr.close()
        os.kill(tlc_pid, 0)
        live, incomplete = sg._live_pid_files(gate_dir)
        self.assertFalse(incomplete)
        self.assertIn(tlc_pid, [pid for _path, pid in live])
        self.java_log.unlink()

        rejected = self.run_wrapper(env, "after-kill-rejected.log")
        self.assertEqual(rejected.returncode, 2, rejected.stdout + rejected.stderr)
        self.assertIn("active TLC reserved before request: 2 GiB", rejected.stdout)
        self.assertIn("aggregate memory would be 4 GiB, above 3 GiB", rejected.stdout)
        self.assertFalse(self.java_log.exists(), "second TLC must not start while the orphan is reserved")

    def test_timeout_watchdog_keeps_java_as_the_lease_owner(self) -> None:
        java_pid_file = self.root / "java.pid"
        env = self.env(FAKE_JAVA_HOLD="1", FAKE_JAVA_PID=str(java_pid_file))
        args = self.wrapper_args("timeout-owner.log")
        args[args.index("-t") + 1] = "1"
        wrapper = subprocess.Popen(
            [str(self.root / "scripts/tlc/run_model_check.sh"), *args],
            cwd=self.work,
            env=env,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        try:
            deadline = time.monotonic() + 3
            ledger_files: list[Path] = []
            while time.monotonic() < deadline:
                ledger_files = list((self.root / "resources").glob("*/ledger.json"))
                if java_pid_file.exists() and ledger_files:
                    break
                time.sleep(0.02)
            self.assertTrue(java_pid_file.exists(), "fake TLC did not start")
            self.assertEqual(len(ledger_files), 1)
            ledger = json.loads(ledger_files[0].read_text())
            reservation = next(iter(ledger["reservations"].values()))
            self.assertEqual(reservation["pid"], int(java_pid_file.read_text()))
        finally:
            with contextlib.suppress(ProcessLookupError):
                os.kill(wrapper.pid, signal.SIGTERM)
            wrapper.wait(timeout=5)

    @unittest.skipUnless(Path("/proc/self").is_dir(), "requires Linux /proc child discovery")
    def test_watchdog_death_stops_tlc_instead_of_disabling_timeout(self) -> None:
        env = self.env(FAKE_JAVA_HOLD="1")
        args = self.wrapper_args("watchdog-killed.log")
        args[args.index("-t") + 1] = "1"
        wrapper = subprocess.Popen(
            [str(self.root / "scripts/tlc/run_model_check.sh"), *args],
            cwd=self.work,
            env=env,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        owner_pid = 0
        try:
            deadline = time.monotonic() + 3
            watchdog_pid = 0
            while time.monotonic() < deadline:
                ledger_files = list((self.root / "resources").glob("*/ledger.json"))
                if ledger_files:
                    ledger = json.loads(ledger_files[0].read_text())
                    reservations = list(ledger["reservations"].values())
                    if reservations:
                        owner_pid = int(reservations[0]["pid"])
                children_file = Path(f"/proc/{wrapper.pid}/task/{wrapper.pid}/children")
                with contextlib.suppress(OSError):
                    for raw_pid in children_file.read_text().split():
                        cmdline = Path(f"/proc/{raw_pid}/cmdline").read_bytes().replace(b"\0", b" ")
                        if b"tlc_resources.py watchdog" in cmdline:
                            watchdog_pid = int(raw_pid)
                            break
                if owner_pid and watchdog_pid:
                    break
                time.sleep(0.02)
            self.assertGreater(owner_pid, 0, "TLC lease owner was not published")
            self.assertGreater(watchdog_pid, 0, "timeout watchdog was not found")

            os.kill(watchdog_pid, signal.SIGKILL)
            self.assertEqual(wrapper.wait(timeout=5), 2)
            with self.assertRaises(ProcessLookupError):
                os.kill(owner_pid, 0)
            ledger = json.loads(next((self.root / "resources").glob("*/ledger.json")).read_text())
            self.assertEqual(ledger["reservations"], {})
        finally:
            with contextlib.suppress(ProcessLookupError):
                os.kill(wrapper.pid, signal.SIGKILL)
            with contextlib.suppress(ProcessLookupError):
                os.kill(owner_pid, signal.SIGKILL)

    def run_background(self, env: dict[str, str], log_name: str) -> tuple[subprocess.CompletedProcess[str], Path]:
        log = self.work / log_name
        result = subprocess.run(
            [
                str(self.root / "scripts/infra/start_background.sh"),
                "-d",
                str(self.work),
                *self.wrapper_args(log_name),
            ],
            cwd=self.work,
            env=env,
            capture_output=True,
            text=True,
            timeout=10,
            check=False,
        )
        return result, Path(f"{log}.pid")

    def test_background_rejection_returns_nonzero_without_pid_file(self) -> None:
        result, pid_file = self.run_background(self.env(SPECULA_TLC_WORKER_LIMIT="4"), "background-rejected.log")

        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        self.assertIn("result: rejected", result.stdout)
        self.assertIn("ERROR: model check was not started.", result.stderr)
        self.assertFalse(pid_file.exists())
        self.assertFalse(self.java_log.exists(), "Java must not start when background admission is rejected")

    def test_background_auto_worker_probe_uses_tlc_script_path(self) -> None:
        result, pid_file = self.run_background(
            self.env(SPECULA_TLC_AUTO_WORKERS="", SPECULA_TLC_WORKER_LIMIT="4"),
            "background-probe-rejected.log",
        )

        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        self.assertIn("this request workers: 6 (auto)", result.stdout)
        self.assertFalse(pid_file.exists())
        self.assertFalse(self.java_log.exists(), "worker probe must not start TLC")

    def test_background_success_returns_pid(self) -> None:
        result, pid_file = self.run_background(self.env(FAKE_JAVA_HOLD="1"), "background-accepted.log")

        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("result: admitted", result.stdout)
        self.assertIn("Process started! PID:", result.stdout)
        self.assertTrue(pid_file.is_file())
        pid = int(pid_file.read_text().strip())
        self.addCleanup(self._terminate, pid)
        os.kill(pid, 0)
        deadline = time.monotonic() + 2
        while not self.java_log.exists() and time.monotonic() < deadline:
            time.sleep(0.02)
        self.assertTrue(self.java_log.exists(), "admitted background TLC did not start")

    def test_stop_gate_tracks_java_owner_if_wrapper_is_sigkilled(self) -> None:
        gate_dir = self.root / "gate"
        gate_dir.mkdir()
        result, pid_file = self.run_background(
            self.env(FAKE_JAVA_HOLD="1", SPECULA_WORK_DIR=str(gate_dir)),
            "background-owner-registry.log",
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        wrapper_pid = int(pid_file.read_text())
        ledger = json.loads(next((self.root / "resources").glob("*/ledger.json")).read_text())
        owner_pid = int(next(iter(ledger["reservations"].values()))["pid"])
        self.addCleanup(self._terminate, owner_pid)
        registry = gate_dir / ".stop-gate/background-pids"
        self.assertTrue((registry / f"{wrapper_pid}.pid").is_file())
        self.assertTrue((registry / f"{owner_pid}.pid").is_file())

        os.kill(wrapper_pid, signal.SIGKILL)
        deadline = time.monotonic() + 3
        while time.monotonic() < deadline:
            live, incomplete = sg._live_pid_files(gate_dir)
            if any(pid == owner_pid for _path, pid in live):
                break
            time.sleep(0.02)

        self.assertFalse(incomplete)
        self.assertIn(owner_pid, [pid for _path, pid in live])

    def test_background_fast_success_is_not_reported_as_failure(self) -> None:
        result, pid_file = self.run_background(self.env(), "background-fast.log")

        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        completed_inline = "completed successfully before background PID handoff" in result.stdout
        handed_off = "Process started! PID:" in result.stdout
        self.assertTrue(completed_inline or handed_off, result.stdout)
        if completed_inline:
            self.assertFalse(pid_file.exists())
        else:
            self.assertTrue(pid_file.is_file())
            self.addCleanup(self._terminate, int(pid_file.read_text()))

    def test_background_cancellation_during_admission_stops_unmanaged_wrapper(self) -> None:
        env = self.env(FAKE_JAVA_HOLD="1")
        scope = str(self.root / "run")
        digest = hashlib.sha256(scope.encode()).hexdigest()[:24]
        state = self.root / "resources" / digest
        state.mkdir(parents=True)
        lock = (state / "lock").open("a+")
        self.addCleanup(lock.close)
        fcntl.flock(lock.fileno(), fcntl.LOCK_EX)
        log_name = "background-cancelled.log"
        pid_file = Path(f"{self.work / log_name}.pid")
        launcher = subprocess.Popen(
            [
                str(self.root / "scripts/infra/start_background.sh"),
                "-d",
                str(self.work),
                *self.wrapper_args(log_name),
            ],
            cwd=self.work,
            env=env,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
        deadline = time.monotonic() + 3
        candidate_locks: list[Path] = []
        while time.monotonic() < deadline:
            candidate_locks = list((state / "leases").glob("*.lock"))
            if len(candidate_locks) == 1:
                break
            time.sleep(0.02)
        self.assertEqual(len(candidate_locks), 1, "owner did not create its lifetime lock before cancellation")
        orphan_lock = candidate_locks[0]
        self.assertFalse(self.java_log.exists())
        os.kill(launcher.pid, signal.SIGTERM)
        try:
            stdout, stderr = launcher.communicate(timeout=5)
        finally:
            fcntl.flock(lock.fileno(), fcntl.LOCK_UN)
        time.sleep(0.2)

        self.assertEqual(launcher.returncode, 143, stdout + stderr)
        self.assertFalse(pid_file.exists())
        self.assertFalse(self.java_log.exists(), "cancelled admission must never start Java")
        ledger_file = state / "ledger.json"
        if ledger_file.exists():
            self.assertEqual(json.loads(ledger_file.read_text())["reservations"], {})
        replacement = self.run_wrapper(self.env(), "background-after-cancel.log")
        self.assertEqual(replacement.returncode, 0, replacement.stdout + replacement.stderr)
        self.assertFalse(orphan_lock.exists())
        self.assertEqual(list((state / "leases").glob("*.lock")), [])

    @staticmethod
    def _terminate(pid: int) -> None:
        with contextlib.suppress(ProcessLookupError):
            os.kill(pid, signal.SIGTERM)
        deadline = time.monotonic() + 3
        while time.monotonic() < deadline:
            try:
                os.kill(pid, 0)
            except ProcessLookupError:
                return
            time.sleep(0.05)
        with contextlib.suppress(ProcessLookupError):
            os.kill(pid, signal.SIGKILL)


if __name__ == "__main__":
    unittest.main()
