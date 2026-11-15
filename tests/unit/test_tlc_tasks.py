"""Real process/MCP waits, with a deterministic substitute for the TLC JVM."""

from __future__ import annotations

import asyncio
import contextlib
import json
import os
import shutil
import signal
import subprocess
import sys
import time
from collections.abc import Iterator
from pathlib import Path
from typing import Any

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent))

import test_adapters as adapters
import test_run_model_check as wrappers

from specula import context_runner, phaselib
from specula import tlc_resources as resources
from specula import tlc_tasks as tasks
from specula.adapters.utils.resume import capture_session_id


@pytest.fixture(autouse=True)
def release_launcher_locks() -> Iterator[None]:
    before = set(tasks._LAUNCHER_LOCKS)
    yield
    for work, owner in set(tasks._LAUNCHER_LOCKS) - before:
        tasks.stop_owned_tasks(work, owner)


@pytest.fixture
def runtime(monkeypatch: pytest.MonkeyPatch) -> Iterator[wrappers.RunModelCheckTests]:
    fixture = wrappers.RunModelCheckTests()
    fixture.setUp()
    for key in list(os.environ):
        if key.startswith("SPECULA_TLC_TOOL_"):
            monkeypatch.delenv(key)
    for key, value in fixture.env().items():
        monkeypatch.setenv(key, value)
    monkeypatch.setenv("SPECULA_WORK_DIR", str(fixture.work))
    monkeypatch.setenv("SPECULA_TLC_TOOL_OWNER", str(fixture.work / "agent.log"))
    java = fixture.bin / "java"
    java.write_text(
        '#!/bin/sh\nprintf \'TLC fixture output\\n\'\nsleep "${FAKE_JAVA_SECONDS:-0.3}"\nexit "${FAKE_JAVA_EXIT:-0}"\n'
    )
    try:
        yield fixture
    finally:
        tasks.stop_owned_tasks(fixture.work, fixture.work / "agent.log")
        deadline = time.monotonic() + 8
        while time.monotonic() < deadline:
            pending = list((fixture.work / ".tlc-tasks/jobs").glob("*/request.json"))
            if all(
                p.with_name("result.json").exists()
                or (p.with_name("worker.json").exists() and not tasks._lock_is_held(p.with_name("worker.lock")))
                for p in pending
            ):
                break
            time.sleep(0.05)
        fixture.doCleanups()


def start_args(runtime: wrappers.RunModelCheckTests) -> dict[str, Any]:
    return {
        "work_dir": str(runtime.work),
        "spec_file": "MC.tla",
        "config_file": "MC.cfg",
        "options": ["-m", "1G", "-M", "1G", "-w", "1", "-t", "1"],
    }


def wait_until(predicate: Any, timeout: float = 10) -> None:
    deadline = time.monotonic() + timeout
    while not predicate():
        assert time.monotonic() < deadline, "managed task did not reach the expected state"
        time.sleep(0.02)


@contextlib.contextmanager
def managed_job(
    runtime: wrappers.RunModelCheckTests,
    monkeypatch: pytest.MonkeyPatch,
    *,
    deadline: str = "0",
    stubborn: bool = False,
    real_tlc: bool = False,
    sigterm_exit: int | None = None,
) -> Iterator[tuple[str, Path, int, resources._ManagedProcess, Path]]:
    """Use real worker/wrapper/locks, and leave no process behind on assertion failure."""
    if real_tlc:
        java = shutil.which("java", path="/usr/bin:/bin")
        jar = tasks.ROOT / "lib/tla2tools.jar"
        if java is None or not jar.is_file():
            pytest.skip("requires Java and the TLC jar")
        (runtime.bin / "java").unlink()
        (runtime.bin / "java").symlink_to(java)
        runtime.spec.write_text(
            "---- MODULE MC ----\nEXTENDS Naturals\nVARIABLE x\n"
            "Init == x = 0\nNext == x' = x + 1\nSpec == Init /\\ [][Next]_x\n====\n"
        )
        runtime.config.write_text("SPECIFICATION Spec\nCHECK_DEADLOCK FALSE\n")
    else:
        (runtime.bin / "java").write_text(
            f"#!{sys.executable}\nimport os,signal,sys,time\nfrom pathlib import Path\n"
            + ("signal.signal(signal.SIGTERM, signal.SIG_IGN)\n" if stubborn else "")
            + (
                f"signal.signal(signal.SIGTERM, lambda *_: sys.exit({sigterm_exit}))\n"
                if sigterm_exit is not None
                else ""
            )
            + f"Path({str(runtime.work / 'java.pid')!r}).write_text(str(os.getpid()))\n"
            + "while True: time.sleep(0.05)\n"
        )
    owner = runtime.work / "agent.log"
    parent_lock = tasks._launcher_lock(runtime.work, owner)
    monkeypatch.setenv("SPECULA_TLC_TOOL_PARENT_LOCK", str(parent_lock))
    args = start_args(runtime)
    args["options"] = ["-m", "64M", "-M", "64M", "-w", "1", "-k", "0", "-t", deadline]
    started = asyncio.run(tasks.start_tlc(**args))
    task_id = started["task_id"]
    path = tasks.task_path(task_id)
    process: resources._ManagedProcess | None = None
    worker_pid = 0
    try:
        wait_until(lambda: bool(list(runtime.tmp.glob("specula-tlc-control-*/owner-identity.json"))))
        identity_file = next(runtime.tmp.glob("specula-tlc-control-*/owner-identity.json"))
        value = json.loads(identity_file.read_text())
        # The fixture can force a portable identity in its guard. Observe the
        # same PID using this test process's own identity format instead.
        identity = resources._process_identity(value["pid"])
        assert identity is not None
        process = resources._ManagedProcess(value["pid"], identity, None)
        worker_pid = json.loads((path / "worker.json").read_text())["pid"]
        if real_tlc:
            wait_until(lambda: (path / "tlc.log").exists() and "Starting..." in (path / "tlc.log").read_text())
        else:
            wait_until((runtime.work / "java.pid").exists)
            assert int((runtime.work / "java.pid").read_text()) == process.pid
        assert process.running()
        yield task_id, path, worker_pid, process, identity_file.parent
    finally:
        tasks.stop_owned_tasks(runtime.work, owner)
        if process is not None and process.running():
            process.send(signal.SIGKILL)
            wait_until(lambda: not process.running())
        if worker_pid and tasks._lock_is_held(path / "worker.lock"):
            os.kill(worker_pid, signal.SIGTERM)
            wait_until(lambda: not tasks._lock_is_held(path / "worker.lock"))


@pytest.mark.parametrize("cleanup", ["stop-owned", "launcher-exit", "none"])
@pytest.mark.parametrize("deadline", ["0", "1"])
@pytest.mark.parametrize("real_tlc", [False, True])
def test_hard_worker_loss_stops_tlc_without_worker_cleanup(
    runtime: wrappers.RunModelCheckTests,
    monkeypatch: pytest.MonkeyPatch,
    cleanup: str,
    deadline: str,
    real_tlc: bool,
) -> None:
    with managed_job(runtime, monkeypatch, deadline=deadline, real_tlc=real_tlc) as job:
        task_id, path, worker_pid, process, control = job
        os.kill(worker_pid, signal.SIGKILL)
        wait_until(lambda: not tasks._lock_is_held(path / "worker.lock"))
        if cleanup == "stop-owned":
            tasks.stop_owned_tasks(runtime.work, runtime.work / "agent.log")
        elif cleanup == "launcher-exit":
            lease = tasks._LAUNCHER_LOCKS.pop((runtime.work.resolve(), (runtime.work / "agent.log").resolve()))
            os.close(lease[1])
        wait_until(lambda: not process.running())
        wait_until(lambda: not control.exists())
        assert tasks.status(task_id)["status"] == "interrupted"
        assert not (path / "result.json").exists()
        assert asyncio.run(tasks.wait_tlc([task_id], timeout_seconds=0))["outcome"] == "finished"
        ledger = next((runtime.root / "resources").glob("*/ledger.json"))
        assert json.loads(ledger.read_text())["reservations"] == {}


@pytest.mark.parametrize("kill_worker", [False, True])
def test_managed_cleanup_escalates_for_tlc_that_ignores_sigterm(
    runtime: wrappers.RunModelCheckTests, monkeypatch: pytest.MonkeyPatch, kill_worker: bool
) -> None:
    with managed_job(runtime, monkeypatch, stubborn=True) as job:
        task_id, path, worker_pid, process, _control = job
        if kill_worker:
            os.kill(worker_pid, signal.SIGKILL)
        tasks.stop_owned_tasks(runtime.work, runtime.work / "agent.log")
        # During the grace period, live Java must still hold its reservation.
        time.sleep(0.3)
        assert process.running()
        ledger = next((runtime.root / "resources").glob("*/ledger.json"))
        token = next(iter(json.loads(ledger.read_text())["reservations"]))
        assert resources._reservation_is_live(ledger.parent, token)
        wait_until(lambda: not process.running(), timeout=12)
        if not kill_worker:
            wait_until(lambda: (path / "result.json").exists())
        assert tasks.status(task_id)["status"] == "interrupted"


@pytest.mark.skipif(sys.platform != "linux", reason="uses /proc to locate the guard and wrapper")
@pytest.mark.parametrize("lost", ["lifeline", "watchdog", "wrapper"])
def test_managed_job_survives_loss_of_one_cleanup_process(
    runtime: wrappers.RunModelCheckTests, monkeypatch: pytest.MonkeyPatch, lost: str
) -> None:
    with managed_job(runtime, monkeypatch, deadline="1" if lost == "watchdog" else "0") as job:
        _task_id, _path, _worker_pid, process, control = job
        wrapper_pid = int(Path(f"/proc/{process.pid}/stat").read_text().rpartition(")")[2].split()[1])
        victim = wrapper_pid if lost == "wrapper" else int((control / "lifeline.pid").read_text())
        if lost == "watchdog":
            children = Path(f"/proc/{wrapper_pid}/task/{wrapper_pid}/children").read_text().split()
            victim = next(
                int(pid)
                for pid in children
                if b" watchdog " in Path(f"/proc/{pid}/cmdline").read_bytes().replace(b"\0", b" ")
            )
        os.kill(victim, signal.SIGKILL)
        wait_until(lambda: not process.running())
        if lost == "lifeline":
            wait_until(lambda: not control.exists())


def test_worker_loss_is_not_success_when_java_handles_sigterm_with_exit_zero(
    runtime: wrappers.RunModelCheckTests, monkeypatch: pytest.MonkeyPatch
) -> None:
    with managed_job(runtime, monkeypatch, sigterm_exit=0) as job:
        task_id, path, worker_pid, process, control = job
        os.kill(worker_pid, signal.SIGKILL)
        wait_until(lambda: not process.running())
        wait_until(lambda: not control.exists())
        assert tasks.status(task_id)["status"] == "interrupted"
        assert "exit code: 143" in (path / "launcher.log").read_text()


@contextlib.contextmanager
def managed_wrapper(
    runtime: wrappers.RunModelCheckTests,
) -> Iterator[tuple[dict[str, str], Path, Path]]:
    worker = runtime.work / "managed-worker.lock"
    parent = runtime.work / "managed-parent.lock"
    descriptors = [tasks._hold_lock(worker), tasks._hold_lock(parent)]
    lifeline_read, lifeline_write = os.pipe()
    descriptors.extend((lifeline_read, lifeline_write))
    stop = runtime.work / "managed-stop"
    (runtime.bin / "java").write_text(
        '#!/bin/sh\nif [ "${1##*/}" = PrintAvailableProcessors.java ]; then echo 1; exit 0; fi\n'
        f"touch '{runtime.work / 'java-started'}'\nexec sleep 60\n"
    )
    env = runtime.env(
        SPECULA_TLC_TOOL_WORKER_LOCK=str(worker),
        SPECULA_TLC_TOOL_STOP_FILE=str(stop),
        SPECULA_TLC_TOOL_PARENT_LOCK=str(parent),
        SPECULA_TLC_TOOL_LIFELINE_FD=str(lifeline_read),
    )
    try:
        yield env, stop, worker
    finally:
        for descriptor in descriptors:
            os.close(descriptor)


@pytest.mark.parametrize("failure", ["startup", "readiness-publication"])
def test_managed_lifeline_startup_failure_never_starts_java(runtime: wrappers.RunModelCheckTests, failure: str) -> None:
    wrapper = runtime.root / "scripts/tlc/run_model_check.sh"
    source = wrapper.read_text()
    if failure == "startup":
        source = source.replace("lifeline_watch() {", "lifeline_watch() {\n    return 2")
    else:
        source = source.replace("printf 'ready\\n' >", "false >")
    wrapper.write_text(source)
    with managed_wrapper(runtime) as (env, _stop, _worker):
        result = runtime.run_wrapper(env, "failed-start.log")
    assert result.returncode == 2, result.stdout + result.stderr
    assert not (runtime.work / "java-started").exists()
    ledger = next((runtime.root / "resources").glob("*/ledger.json"))
    assert json.loads(ledger.read_text())["reservations"] == {}


@pytest.mark.parametrize("boundary", ["before-ready", "after-ready"])
@pytest.mark.parametrize("cancellation", ["stop", "worker-lost", "launcher-lost"])
def test_managed_startup_cancellation_never_starts_java(
    runtime: wrappers.RunModelCheckTests, boundary: str, cancellation: str
) -> None:
    barrier = runtime.work / "startup-barrier"
    proceed = runtime.work / "startup-proceed"
    if boundary == "before-ready":
        wrapper = runtime.root / "scripts/tlc/run_model_check.sh"
        source = wrapper.read_text().replace(
            "lifeline_watch() {",
            f'lifeline_watch() {{\ntouch "{barrier}"\nwhile [ ! -f "{proceed}" ]; do sleep 0.01; done',
        )
        wrapper.write_text(source)
    else:
        wrapper = runtime.root / "scripts/tlc/run_model_check.sh"
        wrapper.write_text(
            wrapper.read_text().replace(
                'touch "$START_FILE"',
                f'touch "{barrier}"\nwhile [ ! -f "{proceed}" ]; do sleep 0.01; done\ntouch "$START_FILE"',
            )
        )
    with managed_wrapper(runtime) as (env, stop, worker):
        process = subprocess.Popen(
            [str(runtime.root / "scripts/tlc/run_model_check.sh"), *runtime.wrapper_args("cancel-start.log")],
            env=env,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            start_new_session=True,
            pass_fds=(int(env["SPECULA_TLC_TOOL_LIFELINE_FD"]),),
        )
        try:
            wait_until(barrier.exists)
            if cancellation == "stop":
                stop.touch()
            else:
                # Simulate lost ownership by removing the observed path. The
                # original test owner keeps its descriptor for safe teardown.
                (worker if cancellation == "worker-lost" else Path(env["SPECULA_TLC_TOOL_PARENT_LOCK"])).unlink()
            proceed.touch()
            stdout, stderr = process.communicate(timeout=10)
            assert process.returncode != 0, stdout + stderr
            assert not (runtime.work / "java-started").exists()
        finally:
            if process.poll() is None:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait(timeout=3)
            if process.stdout is not None:
                process.stdout.close()
            if process.stderr is not None:
                process.stderr.close()
    ledger = next((runtime.root / "resources").glob("*/ledger.json"))
    assert json.loads(ledger.read_text())["reservations"] == {}


def test_managed_deadline_keeps_timeout_exit_code(runtime: wrappers.RunModelCheckTests) -> None:
    wrapper = runtime.root / "scripts/tlc/run_model_check.sh"
    wrapper.write_text(wrapper.read_text().replace("TIMEOUT_MINUTES * 60", "TIMEOUT_MINUTES * 1"))
    with managed_wrapper(runtime) as (env, _stop, _worker):
        result = subprocess.run(
            [str(wrapper), *runtime.wrapper_args("managed-timeout.log"), "-t", "1"],
            env=env,
            capture_output=True,
            text=True,
            timeout=10,
            pass_fds=(int(env["SPECULA_TLC_TOOL_LIFELINE_FD"]),),
        )
    assert result.returncode == 124, result.stdout + result.stderr
    assert (runtime.work / "java-started").exists()


@pytest.mark.parametrize("deadline", ["0", "1"])
@pytest.mark.parametrize("portable", [False, True])
def test_idle_managed_job_does_not_spawn_ps(
    runtime: wrappers.RunModelCheckTests, monkeypatch: pytest.MonkeyPatch, deadline: str, portable: bool
) -> None:
    # Spawn the worker from the fixture too, so an installed TLC jar cannot
    # make it bypass the modified guard below.
    for filename in ("__init__.py", "context_control.py", "tlc_tasks.py"):
        shutil.copy2(tasks.ROOT / "src/specula" / filename, runtime.root / "src/specula" / filename)
    monkeypatch.setattr(tasks, "__file__", str(runtime.root / "src/specula/tlc_tasks.py"))
    if portable:
        guard = runtime.root / "src/specula/tlc_resources.py"
        source = guard.read_text().replace('Path(f"/proc/{pid}/stat")', 'Path(f"/absent-proc/{pid}/stat")')
        source = source.replace('Path(f"/proc/{self.pid}/stat")', 'Path(f"/absent-proc/{self.pid}/stat")')
        guard.write_text(source.replace('hasattr(os, "pidfd_open")', "False"))
    real_ps = shutil.which("ps")
    assert real_ps is not None
    calls = runtime.work / "ps.calls"
    spy = runtime.bin / "ps"
    spy.write_text(f"#!/bin/sh\nprintf 'ps\\n' >> '{calls}'\nexec '{real_ps}' \"$@\"\n")
    spy.chmod(0o755)
    with managed_job(runtime, monkeypatch, deadline=deadline) as job:
        if portable:
            value = json.loads((job[4] / "owner-identity.json").read_text())
            assert value["identity"].startswith("ps:")
        before = calls.read_text()
        time.sleep(0.5)
        assert calls.read_text() == before


@pytest.mark.skipif(sys.platform != "linux", reason="inspects inherited file descriptors in /proc")
def test_only_worker_holds_lifeline_write_end(
    runtime: wrappers.RunModelCheckTests, monkeypatch: pytest.MonkeyPatch
) -> None:
    with managed_job(runtime, monkeypatch) as job:
        _task_id, _path, worker_pid, process, control = job
        helper_pid = int((control / "lifeline.pid").read_text())
        helper_pipes = {
            path.readlink()
            for path in Path(f"/proc/{helper_pid}/fd").iterdir()
            if str(path.readlink()).startswith("pipe:")
        }
        lifelines = []
        for path in Path(f"/proc/{worker_pid}/fd").iterdir():
            if path.readlink() not in helper_pipes:
                continue
            info = Path(f"/proc/{worker_pid}/fdinfo/{path.name}").read_text()
            flags = next(line.split()[1] for line in info.splitlines() if line.startswith("flags:"))
            if int(flags, 8) & os.O_ACCMODE == os.O_WRONLY:
                lifelines.append(path.readlink())
        assert len(lifelines) == 1
        assert lifelines[0] not in {path.readlink() for path in Path(f"/proc/{process.pid}/fd").iterdir()}
        os.kill(worker_pid, signal.SIGKILL)
        wait_until(lambda: not process.running())


@pytest.mark.asyncio
async def test_worker_loss_does_not_stop_another_managed_task(
    runtime: wrappers.RunModelCheckTests, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setenv("FAKE_JAVA_SECONDS", "3")
    first = await tasks.start_tlc(**start_args(runtime))
    second = await tasks.start_tlc(**start_args(runtime))
    first_path = tasks.task_path(first["task_id"])
    worker_pid = json.loads((first_path / "worker.json").read_text())["pid"]
    os.kill(worker_pid, signal.SIGKILL)
    await asyncio.sleep(0.3)
    assert tasks.status(first["task_id"])["status"] == "interrupted"
    assert tasks.status(second["task_id"])["status"] == "running"
    result = await tasks.wait_tlc([second["task_id"]], timeout_seconds=10)
    assert result["tasks"][0]["status"] == "exited"
    assert result["tasks"][0]["exit_code"] == 0


@pytest.mark.asyncio
@pytest.mark.parametrize("code", [0, 12, 124, 2])
async def test_exit_receipt_is_not_a_verification_verdict(
    runtime: wrappers.RunModelCheckTests, monkeypatch: pytest.MonkeyPatch, code: int
) -> None:
    monkeypatch.setenv("FAKE_JAVA_EXIT", str(code))
    started = await tasks.start_tlc(**start_args(runtime))
    result = await tasks.wait_tlc([started["task_id"]], timeout_seconds=10)
    assert result["outcome"] == "finished"
    task = result["tasks"][0]
    assert task["status"] == "exited"
    assert task["exit_code"] == code
    assert Path(task["log_path"]).read_text() == "TLC fixture output\n"
    assert "verified" not in task and "passed" not in task
    assert json.loads(Path(task["result_path"]).read_text()) == task
    assert await tasks.wait_tlc([started["task_id"]]) == result


@pytest.mark.asyncio
async def test_wait_timeout_and_cancellation_do_not_restart_or_stop_tlc(
    runtime: wrappers.RunModelCheckTests, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setenv("FAKE_JAVA_SECONDS", "3")
    started = await tasks.start_tlc(**start_args(runtime))
    task_id = started["task_id"]
    timed = await tasks.wait_tlc([task_id], timeout_seconds=0)
    assert timed["outcome"] == "wait_timeout"
    waiter = asyncio.create_task(tasks.wait_tlc([task_id]))
    await asyncio.sleep(0.1)
    waiter.cancel()
    with pytest.raises(asyncio.CancelledError):
        await waiter
    assert tasks.status(task_id)["status"] == "running"
    result = await tasks.wait_tlc([task_id], timeout_seconds=10)
    assert result["tasks"][0]["exit_code"] == 0
    assert len(list(tasks.tasks_root().iterdir())) == 1


@pytest.mark.asyncio
async def test_any_all_and_parallel_jobs_have_distinct_evidence(
    runtime: wrappers.RunModelCheckTests, monkeypatch: pytest.MonkeyPatch
) -> None:
    first = await tasks.start_tlc(**start_args(runtime))
    monkeypatch.setenv("FAKE_JAVA_SECONDS", "3")
    second = await tasks.start_tlc(**start_args(runtime))
    ids = [first["task_id"], second["task_id"]]
    result = await tasks.wait_tlc(ids, timeout_seconds=10)
    assert result["tasks"][0]["status"] == "exited"
    assert result["tasks"][1]["status"] == "running"
    result = await tasks.wait_tlc(ids + ids, mode="all", timeout_seconds=10)
    assert len(result["tasks"]) == 2
    assert all(t["exit_code"] == 0 for t in result["tasks"])
    assert first["log_path"] != second["log_path"]


@pytest.mark.asyncio
async def test_admission_failure_surfaces_launcher_evidence(runtime: wrappers.RunModelCheckTests) -> None:
    args = start_args(runtime)
    args["options"] = ["-m", "4G", "-M", "4G", "-w", "1", "-t", "1"]
    started = await tasks.start_tlc(**args)
    result = (await tasks.wait_tlc([started["task_id"]], timeout_seconds=10))["tasks"][0]
    assert result["exit_code"] == 2
    assert "rejected" in Path(result["launcher_log_path"]).read_text()


@pytest.mark.asyncio
async def test_explicit_owner_cleanup_stops_only_owned_tasks(
    runtime: wrappers.RunModelCheckTests, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setenv("FAKE_JAVA_SECONDS", "3")
    started = await tasks.start_tlc(**start_args(runtime))
    tasks.stop_owned_tasks(runtime.work, runtime.work / "another-agent.log")
    assert tasks.status(started["task_id"])["status"] == "running"
    tasks.stop_owned_tasks(runtime.work, runtime.work / "agent.log")
    result = (await tasks.wait_tlc([started["task_id"]], timeout_seconds=10))["tasks"][0]
    assert result["status"] == "interrupted"


@pytest.mark.asyncio
async def test_disappeared_launcher_stops_tlc(
    runtime: wrappers.RunModelCheckTests, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setenv("FAKE_JAVA_SECONDS", "30")
    monkeypatch.setenv("SPECULA_TLC_TOOL_PARENT_LOCK", str(runtime.work / "absent-parent.lock"))
    started = await tasks.start_tlc(**start_args(runtime))
    result = await tasks.wait_tlc([started["task_id"]], timeout_seconds=10)
    assert result["tasks"][0]["status"] == "interrupted"


@pytest.mark.asyncio
@pytest.mark.parametrize("options", [["-t", "bad"], ["-o", "overwrite.log"], ["-s", "Other.tla"], [";"], ["-w"]])
async def test_invalid_start_has_no_task_side_effects(runtime: wrappers.RunModelCheckTests, options: list[str]) -> None:
    args = start_args(runtime)
    args["options"] = options
    with pytest.raises(ValueError):
        await tasks.start_tlc(**args)
    assert not tasks.tasks_root().exists()


@pytest.mark.asyncio
async def test_invalid_wait_has_no_side_effects(runtime: wrappers.RunModelCheckTests) -> None:
    for ids in ([], ["../escape"], ["0" * 32]):
        with pytest.raises(ValueError):
            await tasks.wait_tlc(ids)
    assert not tasks.tasks_root().exists()


@pytest.mark.asyncio
async def test_zero_tlc_deadline_preserves_wrapper_semantics(runtime: wrappers.RunModelCheckTests) -> None:
    args = start_args(runtime)
    args["options"][-1] = "0"
    started = await tasks.start_tlc(**args)
    result = await tasks.wait_tlc([started["task_id"]], timeout_seconds=10)
    assert result["tasks"][0]["exit_code"] == 0


def test_runtime_registration_is_local_and_preserves_budgets(tmp_path: Path) -> None:
    tool = tmp_path / "tools/tlc_tools/.venv/bin"
    tool.mkdir(parents=True)
    (tool / "python").symlink_to(sys.executable)
    env = {
        "SPECULA_WORK_DIR": str(tmp_path / "work"),
        "SPECULA_PHASE": "spec_validation",
        "SPECULA_TLC_MEMORY_LIMIT": "8G",
        "SPECULA_TLC_WORKER_LIMIT": "4",
        "SECRET": "never copy me",
    }
    tasks.prepare_environment(env, tmp_path / "agent.log", tmp_path)
    saved = json.loads(Path(env["SPECULA_TLC_TOOL_CONFIG"]).read_text())["mcpServers"]["specula_tlc"]
    assert saved["env"]["SPECULA_TLC_MEMORY_LIMIT"] == "8G"
    assert saved["env"]["SPECULA_TLC_WORKER_LIMIT"] == "4"
    assert "SECRET" not in saved["env"]
    assert "SPECULA_TLC_TOOL_PARENT" not in saved["env"]
    assert tasks._lock_is_held(Path(saved["env"]["SPECULA_TLC_TOOL_PARENT_LOCK"]))
    assert "tool_timeout_sec=3720" in env["SPECULA_TLC_TOOL_CODEX"]
    assert json.loads(env["SPECULA_TLC_TOOL_JSON"])["mcpServers"]["specula_tlc"]["timeout"] == 3720000
    assert not (tmp_path / ".codex/config.toml").exists()


@pytest.mark.parametrize("agent", ["claude-code", "copilot-cli", "codex", "opencode", "pi"])
def test_incremental_compaction_and_tlc_tools_coexist(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, agent: str
) -> None:
    tool = tmp_path / "tools/tlc_tools/.venv/bin"
    tool.mkdir(parents=True)
    (tool / "python").symlink_to(sys.executable)
    env = {"SPECULA_WORK_DIR": str(tmp_path / "work"), "SPECULA_PHASE": "incremental"}
    tasks.prepare_environment(env, tmp_path / "agent.log", tmp_path)
    for key, value in env.items():
        monkeypatch.setenv(key, value)
    directory = tmp_path / "context"
    directory.mkdir()
    combined = context_runner.tool_environment(directory, tmp_path / "work", Path(sys.executable), agent)
    servers = json.loads(combined["SPECULA_CONTEXT_MCP_JSON"])["mcpServers"]
    assert set(servers) == {"specula_context", "specula_tlc"}
    if agent == "copilot-cli":
        assert servers["specula_tlc"]["timeout"] == tasks.CLIENT_TIMEOUT_MS


@pytest.mark.parametrize("retry", [False, True])
def test_blocking_phase_registers_tools_automatically(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    retry: bool,
) -> None:
    tool = tmp_path / "tools/tlc_tools/.venv/bin"
    tool.mkdir(parents=True)
    (tool / "python").symlink_to(sys.executable)
    monkeypatch.setattr(phaselib, "SPECULA_ROOT", tmp_path)
    monkeypatch.setattr(phaselib, "_transient_resume_delay", lambda _attempt: 0)
    adapter = tmp_path / "fake.sh"
    log = tmp_path / "agent.log"
    adapter.write_text(
        f"#!{sys.executable}\n"
        "import json,os,sys\nfrom pathlib import Path\n"
        f"sys.path.insert(0,{str(tasks.ROOT / 'src')!r})\n"
        "from specula.tlc_tasks import _lock_is_held\n"
        "config=json.loads(Path(os.environ['SPECULA_TLC_TOOL_CONFIG']).read_text())\n"
        "assert 'specula_tlc' in config['mcpServers']\n"
        "lock=Path(config['mcpServers']['specula_tlc']['env']['SPECULA_TLC_TOOL_PARENT_LOCK'])\n"
        "assert _lock_is_held(lock)\n"
        f"previous=Path({str(tmp_path / 'previous-lock')!r})\n"
        "if previous.exists():\n"
        " assert previous.read_text()!=str(lock)\n"
        " assert not _lock_is_held(Path(previous.read_text()))\n"
        f"elif {retry!r}:\n"
        " previous.write_text(str(lock)); sys.exit(74)\n"
        f"Path({str(log)!r}).write_text('tools available')\n"
    )
    adapter.chmod(0o755)
    rc, text = phaselib.run_agent_blocking(
        adapter,
        "Smoke test",
        tmp_path / "prompt.md",
        log,
        phase_key="spec_validation",
        work_dir=tmp_path,
        claude_alias="claude",
    )
    assert rc == 0 and text == "tools available"


@pytest.mark.asyncio
async def test_real_mcp_disconnect_and_reconnect_reuses_task(
    runtime: wrappers.RunModelCheckTests, monkeypatch: pytest.MonkeyPatch
) -> None:
    from mcp import ClientSession, StdioServerParameters
    from mcp.client.stdio import stdio_client

    monkeypatch.setenv("FAKE_JAVA_SECONDS", "3")
    params = StdioServerParameters(
        command=sys.executable, args=[str(tasks.ROOT / "tools/tlc_tools/mcp_server.py")], env=dict(os.environ)
    )
    async with stdio_client(params) as (reader, writer), ClientSession(reader, writer) as session:
        await session.initialize()
        listed = await session.list_tools()
        assert {t.name for t in listed.tools} == {"start_tlc", "wait_tlc"}
        started = await session.call_tool("start_tlc", start_args(runtime))
        assert not started.isError
        task_id = json.loads(started.content[0].text)["task_id"]  # type: ignore[union-attr]
        timed = await session.call_tool("wait_tlc", {"task_ids": [task_id], "timeout_seconds": 0})
        assert not timed.isError
    async with stdio_client(params) as (reader, writer), ClientSession(reader, writer) as session:
        await session.initialize()
        waited = await session.call_tool("wait_tlc", {"task_ids": [task_id], "timeout_seconds": 10})
        assert not waited.isError
        result = json.loads(waited.content[0].text)  # type: ignore[union-attr]
        assert result["tasks"][0]["exit_code"] == 0
    assert len(list(tasks.tasks_root().iterdir())) == 1


def test_pi_start_returns_before_tlc_exits(
    runtime: wrappers.RunModelCheckTests, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setenv("FAKE_JAVA_SECONDS", "3")
    result = subprocess.run(
        [sys.executable, str(Path(tasks.__file__)), "start_tlc", json.dumps(start_args(runtime))],
        capture_output=True,
        text=True,
        timeout=2,
    )
    assert result.returncode == 0, result.stderr
    assert json.loads(result.stdout)["status"] == "running"


def test_lost_worker_is_not_success(runtime: wrappers.RunModelCheckTests) -> None:
    path = tasks.tasks_root() / ("a" * 32)
    path.mkdir(parents=True)
    (path / "request.json").write_text(json.dumps({"created_at": time.time() - 60, "owner": ""}))
    (path / "worker.json").write_text(json.dumps({"pid": os.getpid(), "identity": "different process"}))
    assert tasks.status(path.name)["status"] == "interrupted"
    assert tasks.status(path.name)["exit_code"] is None


@pytest.fixture(scope="module")
def bubblewrap() -> str:
    binary = shutil.which("bwrap")
    if sys.platform != "linux" or not binary:
        pytest.skip("requires Linux and bubblewrap")
    probe = subprocess.run(
        [binary, "--unshare-pid", "--ro-bind", "/", "/", "--proc", "/proc", "--dev", "/dev", "--", "true"],
        capture_output=True,
        text=True,
        timeout=5,
    )
    if probe.returncode:
        pytest.skip(f"PID namespaces unavailable: {probe.stderr.strip()}")
    return binary


def sandbox_argv(binary: str, runtime: wrappers.RunModelCheckTests, isolated: bool = True) -> list[str]:
    return (
        [
            binary,
            "--unshare-pid",
            "--ro-bind",
            "/",
            "/",
            "--bind",
            str(runtime.root),
            str(runtime.root),
            "--proc",
            "/proc",
            "--dev",
            "/dev",
            "--",
        ]
        if isolated
        else []
    )


def prepare_task_environment(runtime: wrappers.RunModelCheckTests) -> dict[str, str]:
    python = runtime.root / "tools/tlc_tools/.venv/bin/python"
    python.parent.mkdir(parents=True, exist_ok=True)
    python.symlink_to(sys.executable)
    env = dict(os.environ)
    tasks.prepare_environment(env, runtime.work / "agent.log", runtime.root)
    env["PYTHONPATH"] = str(tasks.ROOT / "src")
    return env


@pytest.mark.parametrize("isolated", [False, True])
def test_launcher_liveness_across_pid_namespace(
    runtime: wrappers.RunModelCheckTests,
    monkeypatch: pytest.MonkeyPatch,
    bubblewrap: str,
    isolated: bool,
) -> None:
    monkeypatch.setenv("FAKE_JAVA_SECONDS", "1")
    env = prepare_task_environment(runtime)
    code = (
        "import asyncio,json\nfrom specula import tlc_tasks as t\n"
        "async def run():\n"
        f" s=await t.start_tlc(**{start_args(runtime)!r})\n"
        " print(json.dumps(await t.wait_tlc([s['task_id']],timeout_seconds=10)))\n"
        "asyncio.run(run())\n"
    )
    result = subprocess.run(
        [*sandbox_argv(bubblewrap, runtime, isolated), sys.executable, "-c", code],
        env=env,
        capture_output=True,
        text=True,
        timeout=15,
    )
    assert result.returncode == 0, result.stderr
    task = json.loads(result.stdout)["tasks"][0]
    assert task["status"] == "exited", task
    assert task["exit_code"] == 0, task


@contextlib.contextmanager
def sandbox_job(
    runtime: wrappers.RunModelCheckTests,
    binary: str,
    env: dict[str, str],
    *,
    cancel_wait: bool = False,
) -> Iterator[subprocess.Popen[str]]:
    ready = runtime.work / "sandbox-ready.json"
    code = (
        "import asyncio,contextlib,json,time\nfrom pathlib import Path\nfrom specula import tlc_tasks as t\n"
        "async def run():\n"
        f" s=await t.start_tlc(**{start_args(runtime)!r})\n"
        " log=Path(s['log_path']); deadline=time.monotonic()+8\n"
        " while not log.exists() or 'TLC fixture output' not in log.read_text():\n"
        "  assert time.monotonic()<deadline, t.status(s['task_id'])\n"
        "  await asyncio.sleep(0.05)\n"
        f" if {cancel_wait!r}:\n"
        "  pending=asyncio.create_task(t.wait_tlc([s['task_id']]))\n"
        "  await asyncio.sleep(0.1); pending.cancel()\n"
        "  with contextlib.suppress(asyncio.CancelledError): await pending\n"
        f" Path({str(ready)!r}).write_text(json.dumps(t.status(s['task_id'])))\n"
        " print(json.dumps(await t.wait_tlc([s['task_id']],timeout_seconds=20)))\n"
        "asyncio.run(run())\n"
    )
    process = subprocess.Popen(
        [*sandbox_argv(binary, runtime), sys.executable, "-c", code],
        env=env,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        start_new_session=True,
    )
    try:
        deadline = time.monotonic() + 10
        while not ready.exists():
            if process.poll() is not None or time.monotonic() >= deadline:
                raise AssertionError(f"Sandbox did not start TLC: {process.communicate(timeout=2)}")
            time.sleep(0.02)
        yield process
    finally:
        if process.poll() is None:
            with contextlib.suppress(ProcessLookupError):
                os.killpg(process.pid, signal.SIGKILL)
            process.wait(timeout=5)
        if process.stdout is not None:
            process.stdout.close()
        if process.stderr is not None:
            process.stderr.close()


def test_host_can_observe_worker_and_cancelled_wait_keeps_tlc_running(
    runtime: wrappers.RunModelCheckTests,
    monkeypatch: pytest.MonkeyPatch,
    bubblewrap: str,
) -> None:
    monkeypatch.setenv("FAKE_JAVA_SECONDS", "3")
    env = prepare_task_environment(runtime)
    with sandbox_job(runtime, bubblewrap, env, cancel_wait=True) as process:
        ready = json.loads((runtime.work / "sandbox-ready.json").read_text())
        assert ready["status"] == "running"
        assert tasks.status(ready["task_id"])["status"] == "running"
        stdout, stderr = process.communicate(timeout=10)
        assert process.returncode == 0, stderr
        task = json.loads(stdout)["tasks"][0]
        assert task["status"] == "exited" and task["exit_code"] == 0


def test_host_stops_only_owned_sandbox_tasks_without_using_pids(
    runtime: wrappers.RunModelCheckTests,
    monkeypatch: pytest.MonkeyPatch,
    bubblewrap: str,
) -> None:
    monkeypatch.setenv("FAKE_JAVA_SECONDS", "30")
    env = prepare_task_environment(runtime)
    with sandbox_job(runtime, bubblewrap, env) as process:
        ready = json.loads((runtime.work / "sandbox-ready.json").read_text())
        with monkeypatch.context() as scoped:
            scoped.setattr(os, "kill", lambda *_args: pytest.fail("must not signal a foreign PID"))
            tasks.stop_owned_tasks(runtime.work, runtime.work / "another-agent.log")
            assert tasks.status(ready["task_id"])["status"] == "running"
            tasks.stop_owned_tasks(runtime.work, runtime.work / "agent.log")
        stdout, stderr = process.communicate(timeout=10)
        assert process.returncode == 0, stderr
        assert json.loads(stdout)["tasks"][0]["status"] == "interrupted"
        assert (tasks.task_path(ready["task_id"]) / "stop.json").is_file()


@pytest.mark.parametrize("crash", [False, True])
def test_real_launcher_exit_releases_lock_across_namespace(
    runtime: wrappers.RunModelCheckTests,
    monkeypatch: pytest.MonkeyPatch,
    bubblewrap: str,
    crash: bool,
) -> None:
    monkeypatch.setenv("FAKE_JAVA_SECONDS", "30")
    env = prepare_task_environment(runtime)
    code = (
        "import json,os,sys\nfrom pathlib import Path\nfrom specula import tlc_tasks as t\n"
        "env=dict(os.environ)\n"
        f"t.prepare_environment(env,Path({str(runtime.work / 'agent.log')!r}),Path({str(runtime.root)!r}))\n"
        "print(json.dumps({k:v for k,v in env.items() if k.startswith('SPECULA_TLC_TOOL_')}),flush=True)\n"
        "sys.stdin.read()\n"
    )
    launcher = subprocess.Popen(
        [sys.executable, "-c", code],
        env=env,
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        text=True,
    )
    try:
        assert launcher.stdout is not None and launcher.stdin is not None
        env.update(json.loads(launcher.stdout.readline()))
        lock = Path(env["SPECULA_TLC_TOOL_PARENT_LOCK"])
        assert tasks._lock_is_held(lock)
        with sandbox_job(runtime, bubblewrap, env) as process:
            if crash:
                launcher.kill()
            else:
                launcher.stdin.close()
            launcher.wait(timeout=5)
            assert not tasks._lock_is_held(lock)
            stdout, stderr = process.communicate(timeout=10)
            assert process.returncode == 0, stderr
            assert json.loads(stdout)["tasks"][0]["status"] == "interrupted"
    finally:
        if launcher.poll() is None:
            launcher.kill()
        launcher.wait(timeout=5)
        if launcher.stdin is not None:
            launcher.stdin.close()
        if launcher.stdout is not None:
            launcher.stdout.close()


@pytest.mark.parametrize("phase", ["spec_validation", "incremental"])
@pytest.mark.parametrize(
    ("agent", "resume"),
    [(agent, False) for agent in ("codex", "claude-code", "copilot-cli", "opencode", "pi")] + [("codex", True)],
)
def test_all_adapters_receive_tools_without_skill_changes(tmp_path: Path, phase: str, agent: str, resume: bool) -> None:
    case = adapters.AdapterCase()
    tool = tmp_path / "tools/tlc_tools/.venv/bin"
    tool.mkdir(parents=True)
    (tool / "python").symlink_to(sys.executable)
    env = {"SPECULA_WORK_DIR": str(tmp_path / "work"), "SPECULA_PHASE": phase, "SPECULA_STOP_GATE": "off"}
    tasks.prepare_environment(env, tmp_path / "agent.log", tmp_path)
    env["COPILOT_HELP_TEXT"] = "--autopilot --additional-mcp-config"
    fake = {"claude-code": "claude", "copilot-cli": "copilot"}.get(agent, agent)
    fixture = json.dumps(adapters.CLAUDE_JSON) if agent == "claude-code" else ""
    if agent == "opencode":
        fixture = json.dumps({"type": "step_finish", "part": {"reason": "stop", "tokens": {}, "cost": 0}})
    elif agent == "pi":
        fixture = json.dumps(
            {"type": "message_end", "message": {"role": "assistant", "content": [], "stopReason": "stop"}}
        )
    flags = ["--prompt=tool registration smoke", "--max-turns=1", f"--log={tmp_path / 'agent.log'}"]
    if resume and agent == "codex":
        state = tmp_path / "resume.json"
        session_id = "019f0000-0000-7000-8000-000000000000"
        capture_session_id(state, adapter="codex", session_id=session_id, cwd=str(tmp_path))
        fixture = "\n".join(
            [
                json.dumps({"type": "thread.started", "thread_id": session_id}),
                json.dumps({"type": "turn.completed", "usage": {}}),
            ]
        )
        flags.append(f"--resume-state={state}")
    try:
        observed = case.run_adapter(
            [str(tasks.ROOT / "scripts/launch/adapters" / f"{agent}.sh")],
            flags,
            fake_name=fake,
            fixture_text=fixture,
            env_extra=env,
            timeout=10,
            run_dir=tmp_path,
        )
        assert observed["returncode"] == 0, observed["stderr"]
        argv = observed["argv"]
        if agent == "codex":
            assert "mcp_servers.specula_tlc=" + env["SPECULA_TLC_TOOL_CODEX"] in argv
            assert 'features.code_mode.direct_only_tool_namespaces=["mcp__specula_tlc"]' in argv
            assert "features.code_mode.enabled=false" in argv
            assert ("resume" in argv) is resume
        elif agent == "claude-code":
            assert argv[argv.index("--mcp-config") + 1] == env["SPECULA_TLC_TOOL_CONFIG"]
        elif agent == "copilot-cli":
            assert argv[argv.index("--additional-mcp-config") + 1] == env["SPECULA_TLC_TOOL_JSON"]
        elif agent == "opencode":
            config = json.loads(observed["opencode_config"])
            assert config["mcp"]["specula_tlc"]["timeout"] == tasks.CLIENT_TIMEOUT_MS
        else:
            assert argv[argv.index("--extension") + 1] == env["SPECULA_TLC_TOOL_EXTENSION"]
    finally:
        case.doCleanups()
