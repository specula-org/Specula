"""TLC task handles and waits, independent of an Agent's terminal sessions."""

from __future__ import annotations

import argparse
import asyncio
import contextlib
import fcntl
import json
import os
import re
import signal
import subprocess
import sys
import threading
import time
import uuid
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from specula.context_control import write_json

ROOT = Path(__file__).resolve().parents[2]
MAX_WAIT_SECONDS = 3600
CLIENT_TIMEOUT_MS = (MAX_WAIT_SECONDS + 120) * 1000
_LAUNCHER_LOCKS: dict[tuple[Path, Path], tuple[Path, int]] = {}
_LOCK_GUARD = threading.Lock()
START_DESCRIPTION = (
    "Start TLC model checking or simulation in the background using Specula's resource-budgeted wrapper. "
    "Prefer this over starting java/tlc2.TLC in a shell. Returns a durable task ID, log paths, and waiting instructions. "
    "Pass wrapper options as separate arguments: -m heap (default 50G), -M offheap (200G), -w workers (auto), "
    "-t minutes (180); choose memory/workers within the run budget. Simulation: -S -n traces -p depth. "
    "Other options: -d depth, -k checkpoint minutes, -D check deadlocks, -C continue on errors, -A cdot, "
    "-j JSON trace path, -f simulation trace prefix. Do not pass -s, -c, or -o; logs are unique per task."
)
WAIT_DESCRIPTION = (
    "Wait inside the tool for TLC tasks returned by start_tlc; use this instead of repeated shell/status/log polling. "
    "The default waits up to one hour for any listed task to finish. Set mode=all to wait for all. "
    "Timeout or cancellation ends only this wait, not TLC; wait again with the same IDs. "
    "Returns process outcomes and evidence paths, not a verification verdict. Read logs to interpret counterexamples "
    "and coverage; a normal TLC time budget ending is not itself CI failure."
)


def _hold_lock(path: Path) -> int:
    descriptor = os.open(path, os.O_RDWR | os.O_CREAT | os.O_EXCL, 0o600)
    try:
        # Only the owner holds this descriptor, never its Agent/MCP/TLC children.
        os.set_inheritable(descriptor, False)
        fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
        return descriptor
    except BaseException:
        os.close(descriptor)
        raise


def _lock_is_held(path: Path) -> bool:
    """Probe the shared inode, not a PID from another namespace."""
    try:
        descriptor = os.open(path, os.O_RDWR | getattr(os, "O_NOFOLLOW", 0))
    except FileNotFoundError:
        return False
    try:
        try:
            fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            return True
        return False
    finally:
        os.close(descriptor)


def _launcher_lock(work: Path, owner: Path) -> Path:
    key = (work.resolve(), owner.resolve())
    with _LOCK_GUARD:
        if key not in _LAUNCHER_LOCKS:
            directory = key[0] / ".tlc-tasks/owners"
            directory.mkdir(parents=True, exist_ok=True)
            path = directory / f"{uuid.uuid4().hex}.lock"
            _LAUNCHER_LOCKS[key] = (path, _hold_lock(path))
        return _LAUNCHER_LOCKS[key][0]


def prepare_environment(env: dict[str, str], log: Path, root: Path = ROOT) -> None:
    """Install run-local tool configuration; never change the user's Agent settings."""
    for key in list(env):
        if key.startswith("SPECULA_TLC_TOOL_"):
            del env[key]
    python = root / "tools/tlc_tools/.venv/bin/python"
    if not python.is_file():
        print("WARNING: TLC task tools are not installed; run specula setup to enable them.", file=sys.stderr)
        return
    directory = Path(env["SPECULA_WORK_DIR"]).resolve() / ".tlc-tasks"
    directory.mkdir(parents=True, exist_ok=True)
    tool_env = {
        key: value
        for key, value in env.items()
        if key
        in {
            "PATH",
            "JAVA_HOME",
            "JAVA_TOOL_OPTIONS",
            "TMPDIR",
            "TLC_STATE_DIR",
            "SPECULA_RUN_DIR",
            "SPECULA_WORK_DIR",
            "SPECULA_STOP_GATE_WORK_DIR",
            "SPECULA_TLC_MEMORY_LIMIT",
            "SPECULA_TLC_WORKER_LIMIT",
            "SPECULA_TLC_RESOURCE_DIR",
            "SPECULA_TLC_SCOPE",
        }
    }
    tool_env.update(
        {
            "SPECULA_ROOT": str(root),
            "SPECULA_TLC_TOOL_OWNER": str(log.resolve()),
            "SPECULA_TLC_TOOL_PARENT_LOCK": str(_launcher_lock(Path(env["SPECULA_WORK_DIR"]), log)),
        }
    )
    entry = {"command": str(python), "args": [str(root / "tools/tlc_tools/mcp_server.py")], "env": tool_env}
    config_path = directory / f"connection-{uuid.uuid4().hex}.json"
    write_json(config_path, {"mcpServers": {"specula_tlc": entry}})
    env["SPECULA_TLC_TOOL_CONFIG"] = str(config_path)
    env["SPECULA_TLC_TOOL_JSON"] = json.dumps(
        {
            "mcpServers": {
                "specula_tlc": {
                    **entry,
                    "tools": ["*"],
                    "timeout": CLIENT_TIMEOUT_MS,
                }
            }
        }
    )
    env["SPECULA_TLC_TOOL_CODEX"] = (
        "{command="
        + json.dumps(entry["command"])
        + ",args="
        + json.dumps(entry["args"])
        + ",env={"
        + ",".join(json.dumps(k) + "=" + json.dumps(v) for k, v in tool_env.items())
        + "},tool_timeout_sec="
        + str(CLIENT_TIMEOUT_MS // 1000)
        + "}"
    )
    env["SPECULA_TLC_TOOL_PYTHON"] = str(python)
    env["SPECULA_TLC_TOOL_EXTENSION"] = str(root / "tools/tlc_tools/pi-extension.js")
    # Pi invokes the same worker directly instead of using an MCP transport.
    env.update({k: v for k, v in tool_env.items() if k.startswith("SPECULA_TLC_TOOL_")})


def tasks_root() -> Path:
    work = os.environ.get("SPECULA_WORK_DIR")
    if not work:
        raise ValueError("TLC task tools require a Specula working directory.")
    return Path(work).resolve() / ".tlc-tasks" / "jobs"


def task_path(task_id: str) -> Path:
    if not re.fullmatch(r"[0-9a-f]{32}", task_id):
        raise ValueError("Invalid TLC task ID; use an ID returned by start_tlc.")
    path = tasks_root() / task_id
    if not (path / "request.json").is_file():
        raise ValueError(f"Unknown TLC task: {task_id}")
    return path


def status(task_id: str) -> dict[str, Any]:
    path = task_path(task_id)
    request = json.loads((path / "request.json").read_text())
    result = path / "result.json"
    if result.is_file():
        return dict(json.loads(result.read_text()))
    pid = path / "worker.json"
    state = "starting"
    if pid.is_file():
        state = "running" if _lock_is_held(path / "worker.lock") else "interrupted"
        # The result may have been committed between reading it and probing liveness.
        if result.is_file():
            return dict(json.loads(result.read_text()))
    elif time.time() - request["created_at"] > 30:
        state = "interrupted"
    return {
        "task_id": task_id,
        "status": state,
        "exit_code": None,
        "log_path": str(path / "tlc.log"),
        "launcher_log_path": str(path / "launcher.log"),
        "result_path": str(result),
    }


async def start_tlc(
    work_dir: str, spec_file: str, config_file: str, options: list[str] | None = None
) -> dict[str, Any]:
    work = Path(work_dir).resolve()
    allowed = Path(os.environ.get("SPECULA_WORK_DIR", "")).resolve()
    if not work.is_relative_to(allowed) or not work.is_dir():
        raise ValueError("work_dir must be inside the Specula working directory.")
    for filename in (spec_file, config_file):
        file = (work / filename).resolve()
        if not file.is_relative_to(allowed) or not file.is_file():
            raise ValueError(f"Spec/config file is missing or outside the working directory: {filename}")
    arguments = list(options or [])
    flags = {"-S", "-D", "-C", "-A"}
    values = {"-m", "-M", "-w", "-t", "-d", "-k", "-j", "-n", "-f", "-p"}
    index = 0
    while index < len(arguments):
        option = arguments[index]
        if option in flags:
            index += 1
        elif option in values and index + 1 < len(arguments):
            if option == "-t" and not arguments[index + 1].isdigit():
                raise ValueError("TLC's time budget (-t) must be nonnegative minutes; 0 disables the deadline.")
            index += 2
        else:
            raise ValueError(f"Unsupported wrapper option: {option}. See start_tlc's tool description.")
    path = tasks_root() / uuid.uuid4().hex
    path.mkdir(parents=True)
    write_json(
        path / "request.json",
        {
            "work_dir": str(work),
            "spec_file": spec_file,
            "config_file": config_file,
            "options": arguments,
            "created_at": time.time(),
            "owner": os.environ.get("SPECULA_TLC_TOOL_OWNER", ""),
        },
    )
    with (path / "worker.log").open("w") as log:
        process = subprocess.Popen(
            [sys.executable, str(Path(__file__).resolve()), "worker", str(path)],
            stdin=subprocess.DEVNULL,
            stdout=log,
            stderr=subprocess.STDOUT,
            start_new_session=True,
        )
    # Worker owns the long check. Reap this direct child without tying its life to this request.
    threading.Thread(target=process.wait, daemon=True).start()
    deadline = time.monotonic() + 2
    while not (path / "worker.json").exists() and process.poll() is None and time.monotonic() < deadline:
        await asyncio.sleep(0.05)
    result = status(path.name)
    if result["status"] in {"starting", "running"}:
        result["instruction"] = (
            f"TLC is running. Do independent work, or call wait_tlc(task_ids=['{path.name}']). Do not repeatedly poll shell sessions or logs."
        )
    return result


async def wait_tlc(task_ids: list[str], timeout_seconds: int = MAX_WAIT_SECONDS, mode: str = "any") -> dict[str, Any]:
    if not task_ids or mode not in {"any", "all"} or not 0 <= timeout_seconds <= MAX_WAIT_SECONDS:
        raise ValueError(
            f"Provide task IDs, mode any/all, and a wait timeout between 0 and {MAX_WAIT_SECONDS} seconds."
        )
    deadline = time.monotonic() + timeout_seconds
    while True:
        tasks = [status(task_id) for task_id in dict.fromkeys(task_ids)]
        terminal = [task["status"] not in {"starting", "running"} for task in tasks]
        if any(terminal) if mode == "any" else all(terminal):
            return {"outcome": "finished", "tasks": tasks}
        if time.monotonic() >= deadline:
            return {
                "outcome": "wait_timeout",
                "tasks": tasks,
                "instruction": "TLC continues with its original budget. Call wait_tlc again with the same task IDs; do not restart it.",
            }
        await asyncio.sleep(min(1, max(0, deadline - time.monotonic())))


def _stop_child(process: subprocess.Popen[bytes]) -> None:
    with contextlib.suppress(ProcessLookupError):
        os.killpg(process.pid, signal.SIGTERM)
    try:
        process.wait(timeout=5)
    except subprocess.TimeoutExpired:
        with contextlib.suppress(ProcessLookupError):
            os.killpg(process.pid, signal.SIGKILL)
        process.wait()


def worker(path: Path) -> None:
    request = json.loads((path / "request.json").read_text())
    worker_lock = _hold_lock(path / "worker.lock")
    # PID is diagnostic only; the lock is the cross-namespace liveness authority.
    write_json(path / "worker.json", {"pid": os.getpid()})
    stopped = False

    def interrupt(_signum: int, _frame: Any) -> None:
        nonlocal stopped
        stopped = True

    for sig in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP):
        signal.signal(sig, interrupt)
    parent_lock = os.environ.get("SPECULA_TLC_TOOL_PARENT_LOCK")
    result: dict[str, Any] = {
        "task_id": path.name,
        "status": "interrupted",
        "exit_code": None,
        "log_path": str(path / "tlc.log"),
        "launcher_log_path": str(path / "launcher.log"),
        "result_path": str(path / "result.json"),
    }
    process = None
    try:
        with (path / "launcher.log").open("w") as log:
            process = subprocess.Popen(
                [
                    str(ROOT / "scripts/tlc/run_model_check.sh"),
                    "-s",
                    request["spec_file"],
                    "-c",
                    request["config_file"],
                    *request["options"],
                    "-o",
                    str(path / "tlc.log"),
                ],
                cwd=request["work_dir"],
                stdin=subprocess.DEVNULL,
                stdout=log,
                stderr=subprocess.STDOUT,
                start_new_session=True,
            )
            while process.poll() is None:
                if stopped or (path / "stop.json").exists() or (parent_lock and not _lock_is_held(Path(parent_lock))):
                    stopped = True
                    _stop_child(process)
                    break
                time.sleep(0.2)
            result.update(exit_code=process.returncode, status="interrupted" if stopped else "exited")
    except Exception as exc:
        result["error"] = str(exc)
    finally:
        try:
            if process is not None and process.poll() is None:
                _stop_child(process)
            result["finished_at"] = time.time()
            write_json(path / "result.json", result)
        finally:
            os.close(worker_lock)


def stop_owned_tasks(work: Path, owner: Path) -> None:
    """Use the existing phase teardown boundary, not a wait-call cancellation."""
    for request_file in (work / ".tlc-tasks/jobs").glob("*/request.json"):
        try:
            request = json.loads(request_file.read_text())
            if request["owner"] != str(owner.resolve()) or request_file.with_name("result.json").exists():
                continue
            write_json(request_file.with_name("stop.json"), {})
        except (OSError, ValueError, KeyError):
            continue
    with _LOCK_GUARD:
        lease = _LAUNCHER_LOCKS.pop((work.resolve(), owner.resolve()), None)
        if lease is not None:
            os.close(lease[1])


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("operation", choices=["worker", "start_tlc", "wait_tlc"])
    parser.add_argument("argument")
    args = parser.parse_args()
    if args.operation == "worker":
        worker(Path(args.argument))
    else:
        function = start_tlc if args.operation == "start_tlc" else wait_tlc
        print(json.dumps(asyncio.run(function(**json.loads(args.argument)))))


if __name__ == "__main__":
    main()
