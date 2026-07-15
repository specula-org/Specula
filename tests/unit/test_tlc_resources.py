"""Unit tests for run-scoped TLC resource admission control.

These tests exercise the stdlib API directly.  The concurrency case uses two
independent processes so it covers the on-disk ``flock`` transaction rather
than merely serializing threads inside one interpreter.
"""

from __future__ import annotations

import contextlib
import json
import multiprocessing
import os
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from collections.abc import Callable
from pathlib import Path
from typing import Any, cast
from unittest import mock

from specula import tlc_resources as tr


def _wait_for_file(path: Path, timeout: float = 5.0) -> str:
    deadline = time.monotonic() + timeout
    while time.monotonic() < deadline:
        with contextlib.suppress(OSError):
            value = path.read_text()
            if value:
                return value
        time.sleep(0.02)
    raise AssertionError(f"timed out waiting for {path}")


def _race_acquire(
    state_root: str,
    scope: str,
    lease_file: str,
    ready: Any,
    start: Any,
    release_winner: Any,
    results: Any,
) -> None:
    """Process target: contend for six MiB in one ten-MiB run budget."""
    os.environ[tr.STATE_DIR_ENV] = state_root
    ready.put(os.getpid())
    start.wait(10)
    owner_lock = tr._open_owner_lock(scope)
    try:
        admission = tr.acquire(
            heap=3 * tr.MIB,
            offheap=3 * tr.MIB,
            workers=1,
            workers_label="1",
            owner_lock=owner_lock,
            lease_file=Path(lease_file),
            scope=scope,
            agent=f"{scope}/agent-{os.getpid()}",
            memory_limit_raw="10M",
        )
        results.put(("ok", admission.admitted, admission.report))
        if admission.admitted:
            release_winner.wait(10)
            owner_lock.close()
            tr.release(Path(lease_file))
        else:
            owner_lock.discard()
    except BaseException as exc:
        owner_lock.discard()
        results.put(("error", False, repr(exc)))


class ResourceCase(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self._tmp.cleanup)
        self.root = Path(self._tmp.name).resolve()
        self.state_root = self.root / "state"
        self.leases = self.root / "leases"
        self.leases.mkdir()
        self._lease_files: list[Path] = []
        self._owner_locks: dict[Path, tr.OwnerLock] = {}

        self._saved_env = {
            name: os.environ.get(name)
            for name in (tr.STATE_DIR_ENV, tr.MEMORY_LIMIT_ENV, tr.WORKER_LIMIT_ENV, tr.SCOPE_ENV)
        }
        os.environ[tr.STATE_DIR_ENV] = str(self.state_root)
        os.environ.pop(tr.MEMORY_LIMIT_ENV, None)
        os.environ.pop(tr.WORKER_LIMIT_ENV, None)
        os.environ.pop(tr.SCOPE_ENV, None)
        self.addCleanup(self._restore_env)

    def tearDown(self) -> None:
        for lease in self._lease_files:
            owner_lock = self._owner_locks.pop(lease, None)
            if owner_lock is not None:
                owner_lock.close()
            with contextlib.suppress(OSError, tr.ResourceError):
                tr.release(lease)

    def _restore_env(self) -> None:
        for name, value in self._saved_env.items():
            if value is None:
                os.environ.pop(name, None)
            else:
                os.environ[name] = value

    def acquire(
        self,
        name: str,
        *,
        scope: str,
        heap: int,
        offheap: int,
        workers: int = 1,
        workers_label: str = "1",
        agent: str | None = None,
        memory_limit: str = "auto",
        worker_limit: str | None = None,
        snapshot: tr.MemorySnapshot | None = None,
        owner_pid: int | None = None,
        precommit: Callable[[], bool] | None = None,
    ) -> tuple[tr.Admission, Path]:
        lease = self.leases / f"{name}.json"
        owner_lock = tr._open_owner_lock(scope)
        try:
            admission = tr.acquire(
                heap=heap,
                offheap=offheap,
                workers=workers,
                workers_label=workers_label,
                owner_lock=owner_lock,
                owner_pid=owner_pid or os.getpid(),
                lease_file=lease,
                scope=scope,
                agent=agent or f"{scope}/agent",
                memory_limit_raw=memory_limit,
                worker_limit_raw=worker_limit,
                snapshot=snapshot,
                precommit=precommit,
            )
        except BaseException:
            owner_lock.discard()
            raise
        if admission.admitted:
            self._lease_files.append(lease)
            self._owner_locks[lease] = owner_lock
        else:
            owner_lock.discard()
        return admission, lease

    def close_owner(self, lease: Path) -> None:
        owner_lock = self._owner_locks.pop(lease)
        owner_lock.close()

    def release(self, lease: Path) -> None:
        owner_lock = self._owner_locks.pop(lease, None)
        if owner_lock is not None:
            owner_lock.close()
        tr.release(lease)

    def ledger(self, scope: str) -> dict[str, Any]:
        value: object = json.loads((tr._state_dir(scope) / "ledger.json").read_text())
        if not isinstance(value, dict):
            raise AssertionError("ledger must contain a JSON object")
        return cast(dict[str, Any], value)


class TestParsing(unittest.TestCase):
    def test_memory_sizes_and_limits(self) -> None:
        cases = {
            "1": 1,
            "2b": 2,
            "3K": 3 * 1024,
            "4 KiB": 4 * 1024,
            "5m": 5 * tr.MIB,
            "6MB": 6 * tr.MIB,
            "7GiB": 7 * tr.GIB,
            "1t": 1024**4,
        }
        for raw, expected in cases.items():
            with self.subTest(raw=raw):
                self.assertEqual(tr.parse_memory_size(raw), expected)
                self.assertEqual(tr.parse_memory_limit(raw), expected)

        for raw in ("", "0", "-1G", "1.5G", "G", "1PB", "1GiBB"):
            with self.subTest(raw=raw), self.assertRaises(ValueError):
                tr.parse_memory_size(raw)

        for raw in ("auto", " AUTO ", "Auto"):
            with self.subTest(raw=raw):
                self.assertIsNone(tr.parse_memory_limit(raw))

    def test_worker_limits(self) -> None:
        self.assertEqual(tr.parse_worker_limit("1"), 1)
        self.assertEqual(tr.parse_worker_limit(" 64 "), 64)
        for raw in ("", "0", "-1", "1.5", "auto", "four"):
            with self.subTest(raw=raw), self.assertRaises(ValueError):
                tr.parse_worker_limit(raw)


class TestMemoryDetection(unittest.TestCase):
    def test_linux_uses_smaller_cgroup_limit_and_remaining(self) -> None:
        meminfo = "MemTotal:       16777216 kB\nMemAvailable:   12582912 kB\n"
        with (
            mock.patch.object(Path, "read_text", return_value=meminfo),
            mock.patch.object(tr, "_cgroup_memory_constraints", return_value=(8 * tr.GIB, 3 * tr.GIB)),
        ):
            snapshot = tr._linux_memory_snapshot()

        self.assertEqual(snapshot.total, 8 * tr.GIB)
        self.assertEqual(snapshot.available, 3 * tr.GIB)
        self.assertEqual(snapshot.source, "/proc/meminfo + cgroup")

    def test_hybrid_cgroup_falls_back_to_v1_memory_controller(self) -> None:
        with tempfile.TemporaryDirectory() as raw_root:
            root = Path(raw_root)
            v2 = root / "v2"
            v1 = root / "v1"
            v2.mkdir()
            v1.mkdir()
            (v1 / "memory.limit_in_bytes").write_text(str(4 * tr.GIB))
            (v1 / "memory.usage_in_bytes").write_text(str(tr.GIB))

            def mounted(fs_type: str, controller: str | None) -> tuple[Path, Path] | None:
                if fs_type == "cgroup2":
                    return v2, v2
                if fs_type == "cgroup" and controller == "memory":
                    return v1, v1
                return None

            with mock.patch.object(tr, "_mounted_cgroup_dir", side_effect=mounted):
                limit, available = tr._cgroup_memory_constraints()

        self.assertEqual(limit, 4 * tr.GIB)
        self.assertEqual(available, 3 * tr.GIB)

    def test_macos_vm_stat_honors_reported_page_size(self) -> None:
        vm_stat = (
            "Mach Virtual Memory Statistics: (page size of 16384 bytes)\n"
            "Pages free:                               100.\n"
            "Pages inactive:                           200.\n"
            "Pages speculative:                         50.\n"
        )

        def run(argv: list[str], **_kwargs: Any) -> subprocess.CompletedProcess[str]:
            output = str(16 * tr.GIB) if argv[0] == "sysctl" else vm_stat
            return subprocess.CompletedProcess(argv, 0, stdout=output, stderr="")

        with mock.patch.object(subprocess, "run", side_effect=run):
            snapshot = tr._macos_memory_snapshot()

        self.assertEqual(snapshot.total, 16 * tr.GIB)
        self.assertEqual(snapshot.available, 350 * 16384)
        self.assertEqual(snapshot.source, "sysctl + vm_stat")


class TestMemoryPolicy(ResourceCase):
    def test_owner_death_while_waiting_does_not_create_policy(self) -> None:
        scope = str(self.root / "cancelled-run")
        with self.assertRaisesRegex(tr.ResourceError, "cancelled before admission"):
            self.acquire(
                "cancelled",
                scope=scope,
                heap=tr.MIB,
                offheap=tr.MIB,
                memory_limit="4M",
                precommit=lambda: False,
            )

        self.assertFalse((tr._state_dir(scope) / "ledger.json").exists())

    def test_auto_is_eighty_percent_and_fixed_for_the_run(self) -> None:
        scope = str(self.root / "auto-run")
        first_snapshot = tr.MemorySnapshot(
            total=16 * tr.GIB,
            available=10 * tr.GIB + 777_777,
            source="first fixture",
        )
        expected_limit = first_snapshot.available * tr.AUTO_MEMORY_PERCENT // 100
        expected_limit -= expected_limit % tr.MIB

        first, first_lease = self.acquire(
            "auto-first",
            scope=scope,
            heap=tr.GIB,
            offheap=tr.GIB,
            snapshot=first_snapshot,
        )
        self.assertTrue(first.admitted, first.report)
        self.assertEqual(self.ledger(scope)["memory"]["limit"], expected_limit)
        self.release(first_lease)

        second_snapshot = tr.MemorySnapshot(total=4 * tr.GIB, available=2 * tr.GIB, source="later fixture")
        second, _ = self.acquire(
            "auto-second",
            scope=scope,
            heap=tr.GIB,
            offheap=tr.GIB,
            snapshot=second_snapshot,
        )

        self.assertTrue(second.admitted, second.report)
        policy = self.ledger(scope)["memory"]
        self.assertEqual(policy["limit"], expected_limit)
        self.assertEqual(policy["snapshot"]["available"], first_snapshot.available)
        self.assertIn("80% of effective available memory at first TLC start", second.report)
        self.assertIn("10 GiB available", second.report)
        self.assertNotIn("2 GiB available", second.report)

    def test_explicit_aggregate_allows_boundary_and_rejects_overage(self) -> None:
        scope = str(self.root / "configured-run")
        first, _ = self.acquire(
            "configured-first",
            scope=scope,
            heap=3 * tr.MIB,
            offheap=tr.MIB,
            memory_limit="10M",
        )
        second, _ = self.acquire(
            "configured-second",
            scope=scope,
            heap=4 * tr.MIB,
            offheap=2 * tr.MIB,
            memory_limit="10M",
        )
        rejected, rejected_lease = self.acquire(
            "configured-rejected",
            scope=scope,
            heap=tr.MIB,
            offheap=tr.MIB,
            memory_limit="10M",
        )

        self.assertTrue(first.admitted, first.report)
        self.assertTrue(second.admitted, second.report)
        self.assertFalse(rejected.admitted)
        self.assertIn("aggregate memory would be 12 MiB, above 10 MiB", rejected.report)
        self.assertFalse(rejected_lease.exists())
        self.assertEqual(len(self.ledger(scope)["reservations"]), 2)


class TestWorkers(ResourceCase):
    def test_worker_bound_is_optional_and_aggregate_when_set(self) -> None:
        unbounded_scope = str(self.root / "workers-unbounded")
        first, _ = self.acquire(
            "unbounded-first",
            scope=unbounded_scope,
            heap=tr.MIB,
            offheap=tr.MIB,
            workers=64,
            workers_label="auto",
            memory_limit="100M",
        )
        second, _ = self.acquire(
            "unbounded-second",
            scope=unbounded_scope,
            heap=tr.MIB,
            offheap=tr.MIB,
            workers=64,
            workers_label="auto",
            memory_limit="100M",
        )
        self.assertTrue(first.admitted, first.report)
        self.assertTrue(second.admitted, second.report)
        self.assertIn("worker limit: unbounded (report only)", second.report)
        self.assertIn("concurrent auto runs can oversubscribe CPUs", second.report)

        bounded_scope = str(self.root / "workers-bounded")
        allowed, _ = self.acquire(
            "bounded-first",
            scope=bounded_scope,
            heap=tr.MIB,
            offheap=tr.MIB,
            workers=2,
            memory_limit="100M",
            worker_limit="3",
        )
        rejected, _ = self.acquire(
            "bounded-second",
            scope=bounded_scope,
            heap=tr.MIB,
            offheap=tr.MIB,
            workers=2,
            memory_limit="100M",
            worker_limit="3",
        )
        self.assertTrue(allowed.admitted, allowed.report)
        self.assertFalse(rejected.admitted)
        self.assertIn("aggregate workers would be 4, above 3", rejected.report)


class TestLeaseLifecycle(ResourceCase):
    def test_release_removes_only_its_reservation_and_is_idempotent(self) -> None:
        scope = str(self.root / "release-run")
        admission, lease = self.acquire(
            "release",
            scope=scope,
            heap=tr.MIB,
            offheap=tr.MIB,
            memory_limit="10M",
        )
        self.assertTrue(admission.admitted, admission.report)
        self.assertTrue(lease.is_file())
        self.assertEqual(len(self.ledger(scope)["reservations"]), 1)

        with self.assertRaisesRegex(tr.ResourceError, "owner is still running"):
            tr.release(lease)
        self.assertTrue(lease.exists())
        self.assertEqual(len(self.ledger(scope)["reservations"]), 1)

        self.release(lease)
        self.assertFalse(lease.exists())
        self.assertEqual(self.ledger(scope)["reservations"], {})
        tr.release(lease)

    def test_dead_owner_is_cleaned_before_next_admission(self) -> None:
        scope = str(self.root / "stale-run")
        stale, stale_lease = self.acquire(
            "stale",
            scope=scope,
            heap=4 * tr.MIB,
            offheap=4 * tr.MIB,
            memory_limit="10M",
        )
        self.assertTrue(stale.admitted, stale.report)

        self.close_owner(stale_lease)
        replacement, replacement_lease = self.acquire(
            "replacement",
            scope=scope,
            heap=4 * tr.MIB,
            offheap=4 * tr.MIB,
            memory_limit="10M",
        )

        self.assertTrue(replacement.admitted, replacement.report)
        self.assertIn("active TLC reserved before request: 0 bytes", replacement.report)
        self.assertEqual(len(self.ledger(scope)["reservations"]), 1)
        tr.release(stale_lease)
        self.assertEqual(len(self.ledger(scope)["reservations"]), 1)
        self.release(replacement_lease)
        self.assertEqual(self.ledger(scope)["reservations"], {})

    def test_pid_identity_mismatch_cannot_clear_a_held_reservation(self) -> None:
        scope = str(self.root / "namespace-run")
        first, _ = self.acquire(
            "namespace-first",
            scope=scope,
            heap=3 * tr.MIB,
            offheap=3 * tr.MIB,
            memory_limit="10M",
            owner_pid=2,
        )
        with (
            mock.patch.object(tr, "_process_identity", return_value="different-namespace-process"),
            mock.patch.object(tr, "_process_alive", return_value=False),
        ):
            second, _ = self.acquire(
                "namespace-second",
                scope=scope,
                heap=3 * tr.MIB,
                offheap=3 * tr.MIB,
                memory_limit="10M",
                owner_pid=2,
            )

        self.assertTrue(first.admitted, first.report)
        self.assertFalse(second.admitted)
        self.assertIn("active TLC reserved before request: 6 MiB", second.report)
        self.assertIn("aggregate memory would be 12 MiB, above 10 MiB", second.report)

    def test_old_pid_only_ledger_fails_closed(self) -> None:
        scope = str(self.root / "old-ledger-run")
        state = tr._state_dir(scope)
        (state / "ledger.json").write_text('{"version": 1}\n')

        with self.assertRaisesRegex(tr.ResourceError, "invalid TLC resource ledger"):
            self.acquire(
                "old-ledger",
                scope=scope,
                heap=tr.MIB,
                offheap=tr.MIB,
                memory_limit="10M",
            )

        self.assertEqual(json.loads((state / "ledger.json").read_text()), {"version": 1})

    def test_lock_inspection_error_fails_closed(self) -> None:
        scope = str(self.root / "lock-error-run")
        first, _ = self.acquire(
            "lock-error-first",
            scope=scope,
            heap=3 * tr.MIB,
            offheap=3 * tr.MIB,
            memory_limit="10M",
        )
        with (
            mock.patch.object(tr, "_reservation_is_live", side_effect=tr.ResourceError("lock unavailable")),
            self.assertRaisesRegex(tr.ResourceError, "lock unavailable"),
        ):
            self.acquire(
                "lock-error-second",
                scope=scope,
                heap=tr.MIB,
                offheap=tr.MIB,
                memory_limit="10M",
            )

        self.assertTrue(first.admitted, first.report)
        self.assertEqual(len(self.ledger(scope)["reservations"]), 1)

    def test_unlocked_candidate_not_in_ledger_is_cleaned(self) -> None:
        scope = str(self.root / "orphan-lock-run")
        orphan = tr._open_owner_lock(scope)
        orphan_path = orphan.path
        orphan.close()

        admitted, lease = self.acquire(
            "orphan-lock-replacement",
            scope=scope,
            heap=tr.MIB,
            offheap=tr.MIB,
            memory_limit="10M",
        )

        self.assertTrue(admitted.admitted, admitted.report)
        self.assertFalse(orphan_path.exists())
        self.release(lease)

    def test_held_candidate_not_in_ledger_is_preserved(self) -> None:
        scope = str(self.root / "waiting-owner-run")
        waiting = tr._open_owner_lock(scope)
        try:
            admitted, lease = self.acquire(
                "waiting-owner-admitted",
                scope=scope,
                heap=tr.MIB,
                offheap=tr.MIB,
                memory_limit="10M",
            )

            self.assertTrue(admitted.admitted, admitted.report)
            self.assertTrue(waiting.path.exists())
            self.assertTrue(tr._reservation_is_live(waiting.state, waiting.token))
            self.release(lease)
        finally:
            waiting.discard()


class TestReporting(ResourceCase):
    def test_reports_aggregate_and_current_agent_separately(self) -> None:
        scope = str(self.root / "agents-run")
        agent_a = f"{scope}/agent-a"
        agent_b = f"{scope}/agent-b"
        first, _ = self.acquire(
            "agent-a-first",
            scope=scope,
            agent=agent_a,
            heap=tr.MIB,
            offheap=tr.MIB,
            memory_limit="10M",
        )
        second, _ = self.acquire(
            "agent-b",
            scope=scope,
            agent=agent_b,
            heap=tr.MIB,
            offheap=tr.MIB,
            memory_limit="10M",
        )
        third, _ = self.acquire(
            "agent-a-second",
            scope=scope,
            agent=agent_a,
            heap=tr.MIB,
            offheap=tr.MIB,
            memory_limit="10M",
        )

        self.assertTrue(first.admitted, first.report)
        self.assertTrue(second.admitted, second.report)
        self.assertTrue(third.admitted, third.report)
        self.assertIn("active TLC reserved before request: 2 MiB (this agent: 0 bytes)", second.report)
        self.assertIn("active TLC workers before request: 1 (this agent: 0)", second.report)
        self.assertIn("active TLC reserved before request: 4 MiB (this agent: 2 MiB)", third.report)
        self.assertIn("active TLC workers before request: 2 (this agent: 1)", third.report)


class TestOwnerCommand(ResourceCase):
    def setUp(self) -> None:
        super().setUp()
        os.environ[tr.SCOPE_ENV] = str(self.root / "run")

    def owner_argv(
        self,
        name: str,
        command: list[str],
        *,
        heap: str = "1M",
        offheap: str = "1M",
    ) -> tuple[list[str], dict[str, Path]]:
        files = {label: self.root / f"{name}-{label}" for label in ("lease", "status", "report", "start", "stop")}
        argv = [
            sys.executable,
            str(Path(tr.__file__).resolve()),
            "owner",
            "--heap",
            heap,
            "--offheap",
            offheap,
            "--workers",
            "1",
            "--workers-label",
            "1",
            "--lease-file",
            str(files["lease"]),
            "--status-file",
            str(files["status"]),
            "--report-file",
            str(files["report"]),
            "--start-file",
            str(files["start"]),
            "--stop-file",
            str(files["stop"]),
            "--parent-pid",
            str(os.getpid()),
            "--",
            *command,
        ]
        return argv, files

    @staticmethod
    def terminate(process: subprocess.Popen[str]) -> None:
        if process.poll() is None:
            process.terminate()
        with contextlib.suppress(subprocess.TimeoutExpired):
            process.wait(timeout=5)
        if process.poll() is None:
            process.kill()
            process.wait(timeout=5)
        if process.stdout is not None:
            process.stdout.close()
        if process.stderr is not None:
            process.stderr.close()

    def test_owner_publishes_admission_then_execs_with_the_same_locked_pid(self) -> None:
        pid_file = self.root / "exec-owner.pid"
        command = [
            sys.executable,
            "-c",
            "import os,sys,time; from pathlib import Path; "
            "Path(sys.argv[1]).write_text(str(os.getpid())); time.sleep(60)",
            str(pid_file),
        ]
        argv, files = self.owner_argv("exec", command)
        process = subprocess.Popen(
            argv, env=os.environ.copy(), stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True
        )
        self.addCleanup(self.terminate, process)

        self.assertEqual(_wait_for_file(files["status"]), "admitted\n")
        self.assertIn("result: admitted", files["report"].read_text())
        self.assertFalse(pid_file.exists(), "owner must wait for the wrapper start signal")
        ledger = self.ledger(str(self.root / "run"))
        self.assertEqual(ledger["version"], tr.LEDGER_VERSION)
        token, reservation = next(iter(ledger["reservations"].items()))
        self.assertEqual(reservation["pid"], process.pid)
        self.assertTrue(tr._reservation_is_live(tr._state_dir(str(self.root / "run")), token))

        with self.assertRaisesRegex(tr.ResourceError, "owner is still running"):
            tr.release(files["lease"])
        files["start"].touch()
        self.assertEqual(int(_wait_for_file(pid_file)), process.pid)
        self.assertTrue(tr._reservation_is_live(tr._state_dir(str(self.root / "run")), token))

        self.terminate(process)
        tr.release(files["lease"])
        self.assertEqual(self.ledger(str(self.root / "run"))["reservations"], {})

    @unittest.skipUnless(shutil.which("java"), "requires Java to verify inherited descriptors")
    def test_owner_lock_survives_exec_into_the_real_jvm(self) -> None:
        source = self.root / "Hold.java"
        pid_file = self.root / "java-owner.pid"
        source.write_text(
            "import java.nio.file.*; "
            "class Hold { public static void main(String[] args) throws Exception { "
            "Files.writeString(Path.of(args[0]), Long.toString(ProcessHandle.current().pid())); "
            "Thread.sleep(60000); } }\n"
        )
        java = shutil.which("java")
        assert java is not None
        argv, files = self.owner_argv("java", [java, str(source), str(pid_file)])
        files["start"].touch()
        process = subprocess.Popen(
            argv, env=os.environ.copy(), stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True
        )
        self.addCleanup(self.terminate, process)

        self.assertEqual(_wait_for_file(files["status"], timeout=10), "admitted\n")
        self.assertEqual(int(_wait_for_file(pid_file, timeout=10)), process.pid)
        ledger = self.ledger(str(self.root / "run"))
        token = next(iter(ledger["reservations"]))
        self.assertTrue(tr._reservation_is_live(tr._state_dir(str(self.root / "run")), token))

        self.terminate(process)
        tr.release(files["lease"])
        self.assertEqual(self.ledger(str(self.root / "run"))["reservations"], {})

    def test_owner_error_is_published_atomically(self) -> None:
        argv, files = self.owner_argv("empty", [])
        result = subprocess.run(argv, env=os.environ.copy(), capture_output=True, text=True, timeout=5, check=False)

        self.assertEqual(result.returncode, 2)
        self.assertEqual(files["status"].read_text(), "error\n")
        self.assertIn("owner command is empty", files["report"].read_text())

    def test_owner_parse_error_is_published(self) -> None:
        argv, files = self.owner_argv("invalid-memory", ["true"], heap="invalid")
        result = subprocess.run(argv, env=os.environ.copy(), capture_output=True, text=True, timeout=5, check=False)

        self.assertEqual(result.returncode, 2)
        self.assertEqual(files["status"].read_text(), "error\n")
        self.assertIn("invalid memory size", files["report"].read_text())

    @unittest.skipUnless(sys.platform.startswith("linux") and shutil.which("bwrap"), "requires bubblewrap")
    def test_owner_flock_is_shared_across_pid_namespaces(self) -> None:
        bwrap = shutil.which("bwrap")
        assert bwrap is not None
        probe = subprocess.run(
            [bwrap, "--unshare-pid", "--ro-bind", "/", "/", "--proc", "/proc", "--dev", "/dev", "--", "true"],
            capture_output=True,
            text=True,
            timeout=5,
            check=False,
        )
        if probe.returncode != 0:
            self.skipTest(f"bubblewrap cannot create a PID namespace: {probe.stderr.strip()}")

        scope = "/shared/pid-namespace-run"

        def sandbox_argv(name: str, command: list[str]) -> tuple[list[str], dict[str, Path]]:
            files = {
                label: self.root / f"bwrap-{name}-{label}" for label in ("lease", "status", "report", "start", "stop")
            }
            files["start"].touch()
            owner = [
                sys.executable,
                str(Path(tr.__file__).resolve()),
                "owner",
                "--heap",
                "3M",
                "--offheap",
                "3M",
                "--workers",
                "1",
                "--workers-label",
                "1",
                "--lease-file",
                str(files["lease"]),
                "--status-file",
                str(files["status"]),
                "--report-file",
                str(files["report"]),
                "--start-file",
                str(files["start"]),
                "--stop-file",
                str(files["stop"]),
                "--parent-pid",
                "1",
                "--",
                *command,
            ]
            argv = [
                bwrap,
                "--die-with-parent",
                "--unshare-pid",
                "--ro-bind",
                "/",
                "/",
                "--bind",
                str(self.root),
                str(self.root),
                "--proc",
                "/proc",
                "--dev",
                "/dev",
                "--setenv",
                tr.STATE_DIR_ENV,
                str(self.state_root),
                "--setenv",
                tr.SCOPE_ENV,
                scope,
                "--setenv",
                tr.MEMORY_LIMIT_ENV,
                "10M",
                "--",
                *owner,
            ]
            return argv, files

        first_argv, first_files = sandbox_argv("first", ["sleep", "60"])
        first = subprocess.Popen(first_argv, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        self.addCleanup(self.terminate, first)
        self.assertEqual(_wait_for_file(first_files["status"]), "admitted\n")

        second_argv, second_files = sandbox_argv("second", ["true"])
        second = subprocess.run(second_argv, capture_output=True, text=True, timeout=10, check=False)
        self.assertEqual(second.returncode, 2, second.stdout + second.stderr)
        self.assertEqual(second_files["status"].read_text(), "rejected\n")
        second_report = second_files["report"].read_text()
        self.assertIn("active TLC reserved before request: 6 MiB", second_report)
        self.assertIn("aggregate memory would be 12 MiB, above 10 MiB", second_report)
        state = tr._state_dir(scope)
        ledger = json.loads((state / "ledger.json").read_text())
        self.assertEqual([entry["pid"] for entry in ledger["reservations"].values()], [2])

        self.terminate(first)
        third_argv, third_files = sandbox_argv("third", ["true"])
        third = subprocess.run(third_argv, capture_output=True, text=True, timeout=10, check=False)
        self.assertEqual(third.returncode, 0, third.stdout + third.stderr)
        self.assertEqual(third_files["status"].read_text(), "admitted\n")
        tr.release(first_files["lease"])
        tr.release(third_files["lease"])
        self.assertEqual(json.loads((state / "ledger.json").read_text())["reservations"], {})


class TestConcurrency(ResourceCase):
    def test_same_scope_admission_is_atomic_across_processes(self) -> None:
        scope = str(self.root / "concurrent-run")
        ctx = multiprocessing.get_context("spawn")
        ready = ctx.Queue()
        results = ctx.Queue()
        start = ctx.Event()
        release_winner = ctx.Event()
        processes = [
            ctx.Process(
                target=_race_acquire,
                args=(
                    str(self.state_root),
                    scope,
                    str(self.leases / f"race-{index}.json"),
                    ready,
                    start,
                    release_winner,
                    results,
                ),
            )
            for index in range(2)
        ]
        for process in processes:
            process.start()
        try:
            for _ in processes:
                ready.get(timeout=10)
            start.set()
            outcomes = [results.get(timeout=10) for _ in processes]
            self.assertEqual([item[0] for item in outcomes], ["ok", "ok"])
            self.assertEqual(sorted(item[1] for item in outcomes), [False, True])
            rejected_report = next(item[2] for item in outcomes if not item[1])
            self.assertIn("aggregate memory would be 12 MiB, above 10 MiB", rejected_report)
        finally:
            release_winner.set()
            for process in processes:
                process.join(timeout=10)
                if process.is_alive():
                    process.kill()
                    process.join(timeout=5)
        self.assertEqual([process.exitcode for process in processes], [0, 0])
        self.assertEqual(self.ledger(scope)["reservations"], {})

    def test_timeout_watchdog_does_not_signal_a_reused_pid(self) -> None:
        status = self.root / "watchdog-status"
        with (
            mock.patch.object(tr, "_process_identity", side_effect=["original", "replacement"]),
            mock.patch.object(time, "sleep"),
            mock.patch.object(os, "kill") as kill,
            mock.patch.object(os, "pidfd_open", side_effect=OSError, create=True),
        ):
            timed_out = tr.enforce_timeout(os.getpid(), 1, status)

        self.assertFalse(timed_out)
        self.assertEqual(status.read_text(), "ready\n")
        self.assertFalse(any(call.args == (os.getpid(), signal.SIGTERM) for call in kill.call_args_list))

    def test_timeout_watchdog_signals_the_original_owner(self) -> None:
        owner = subprocess.Popen(["sleep", "60"])
        self.addCleanup(owner.wait)
        self.addCleanup(owner.kill)
        status = self.root / "watchdog-status-live"

        timed_out = tr.enforce_timeout(owner.pid, 1, status)

        self.assertTrue(timed_out)
        self.assertEqual(owner.wait(timeout=3), -signal.SIGTERM)
        self.assertEqual(status.read_text(), "timed-out\n")


if __name__ == "__main__":
    unittest.main()
