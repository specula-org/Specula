"""Run-scoped admission control for TLC heap, direct memory, and workers.

The TLC wrapper calls this module before starting Java and releases its lease
when Java exits.  Reservations are declarations (``-m + -M`` and ``-w``), not
measurements of RSS or CPU usage.  A file lock makes concurrent admissions for
the same Specula run atomic on Linux and macOS.
"""

from __future__ import annotations

import argparse
import contextlib
import fcntl
import hashlib
import json
import os
import platform
import re
import signal
import stat
import subprocess
import sys
import tempfile
import time
import uuid
from collections.abc import Callable, Iterator
from dataclasses import dataclass
from pathlib import Path
from typing import Any

AUTO_MEMORY_PERCENT = 80
MIB = 1024**2
GIB = 1024**3
LEDGER_VERSION = 2
OWNER_START_TIMEOUT_SECONDS = 30.0
OWNER_POLL_SECONDS = 0.05

MEMORY_LIMIT_ENV = "SPECULA_TLC_MEMORY_LIMIT"
WORKER_LIMIT_ENV = "SPECULA_TLC_WORKER_LIMIT"
STATE_DIR_ENV = "SPECULA_TLC_RESOURCE_DIR"
SCOPE_ENV = "SPECULA_TLC_SCOPE"
RUN_POLICY_FILENAME = "tlc-resources.json"

_SIZE_RE = re.compile(r"^([1-9][0-9]*)\s*([kmgt]?i?b?)?$", re.IGNORECASE)
_TOKEN_RE = re.compile(r"^[0-9a-f]{32}$")
_SIZE_MULTIPLIERS = {
    "": 1,
    "b": 1,
    "k": 1024,
    "kb": 1024,
    "kib": 1024,
    "m": MIB,
    "mb": MIB,
    "mib": MIB,
    "g": GIB,
    "gb": GIB,
    "gib": GIB,
    "t": 1024**4,
    "tb": 1024**4,
    "tib": 1024**4,
}


class ResourceError(Exception):
    """Invalid configuration or unsafe/corrupt admission state."""


@dataclass(frozen=True)
class MemorySnapshot:
    total: int
    available: int
    source: str


@dataclass(frozen=True)
class Admission:
    admitted: bool
    report: str


@dataclass
class OwnerLock:
    """A reservation liveness lock held by the holder and inherited by Java."""

    state: Path
    token: str
    path: Path
    descriptor: int | None

    def close(self) -> None:
        if self.descriptor is None:
            return
        descriptor = self.descriptor
        self.descriptor = None
        os.close(descriptor)

    def discard(self) -> None:
        """Close and remove a candidate lock which never entered the ledger."""
        self.close()
        with contextlib.suppress(FileNotFoundError):
            self.path.unlink()


def load_run_policy(run_dir: Path) -> tuple[str, str | None]:
    """Load and validate the durable TLC policy for an isolated run."""
    policy_file = run_dir / RUN_POLICY_FILENAME
    try:
        policy = json.loads(policy_file.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        raise ResourceError(f"cannot read TLC resource config {policy_file}: {exc}") from exc
    if not isinstance(policy, dict) or policy.get("version") != 1:
        raise ResourceError(f"invalid TLC resource config in {policy_file}")
    memory = policy.get("memory_limit")
    workers = policy.get("worker_limit")
    if not isinstance(memory, str) or (workers is not None and not isinstance(workers, str)):
        raise ResourceError(f"invalid TLC resource config in {policy_file}")
    try:
        parse_memory_limit(memory)
        if workers is not None:
            parse_worker_limit(workers)
    except ValueError as exc:
        raise ResourceError(f"invalid TLC resource config in {policy_file}: {exc}") from exc
    return memory, workers


def parse_memory_size(raw: str) -> int:
    """Parse a positive Java-style memory size into bytes."""
    value = raw.strip()
    match = _SIZE_RE.fullmatch(value)
    if match is None:
        raise ValueError(f"invalid memory size '{raw}' (use a positive value such as 64G)")
    number = int(match.group(1))
    suffix = (match.group(2) or "").casefold()
    multiplier = _SIZE_MULTIPLIERS.get(suffix)
    if multiplier is None:  # Defensive: the regex and table intentionally match.
        raise ValueError(f"invalid memory unit in '{raw}'")
    return number * multiplier


def parse_memory_limit(raw: str) -> int | None:
    """Return None for the automatic 80% policy, otherwise configured bytes."""
    if raw.strip().casefold() == "auto":
        return None
    return parse_memory_size(raw)


def parse_worker_limit(raw: str) -> int:
    value = raw.strip()
    if not value.isdigit() or int(value) < 1:
        raise ValueError(f"invalid TLC worker limit '{raw}' (use a positive integer)")
    return int(value)


def format_bytes(value: int) -> str:
    if value >= GIB:
        amount = f"{value / GIB:.2f}".rstrip("0").rstrip(".")
        return f"{amount} GiB"
    if value >= MIB:
        amount = f"{value / MIB:.2f}".rstrip("0").rstrip(".")
        return f"{amount} MiB"
    return f"{value} bytes"


def _read_int(path: Path) -> int | None:
    try:
        raw = path.read_text().strip()
    except OSError:
        return None
    if not raw or raw == "max":
        return None
    try:
        return int(raw)
    except ValueError:
        return None


def _unescape_mount_path(raw: str) -> str:
    return raw.replace("\\040", " ").replace("\\011", "\t").replace("\\012", "\n").replace("\\134", "\\")


def _mount_for(fs_type: str, controller: str | None = None) -> tuple[Path, Path] | None:
    try:
        lines = Path("/proc/self/mountinfo").read_text().splitlines()
    except OSError:
        return None
    for line in lines:
        left, separator, right = line.partition(" - ")
        if not separator:
            continue
        left_fields = left.split()
        right_fields = right.split()
        if len(left_fields) < 5 or not right_fields or right_fields[0] != fs_type:
            continue
        if controller is not None and controller not in ",".join(right_fields[2:]).split(","):
            continue
        return Path(_unescape_mount_path(left_fields[4])), Path(_unescape_mount_path(left_fields[3]))
    return None


def _cgroup_path(controller: str | None) -> Path | None:
    try:
        lines = Path("/proc/self/cgroup").read_text().splitlines()
    except OSError:
        return None
    for line in lines:
        hierarchy, separator, rest = line.partition(":")
        if not separator:
            continue
        controllers, separator, raw_path = rest.partition(":")
        if not separator:
            continue
        if controller is None and hierarchy == "0" and not controllers:
            return Path(raw_path)
        if controller is not None and controller in controllers.split(","):
            return Path(raw_path)
    return None


def _mounted_cgroup_dir(fs_type: str, controller: str | None) -> tuple[Path, Path] | None:
    mounted = _mount_for(fs_type, controller)
    cgroup = _cgroup_path(controller)
    if mounted is None or cgroup is None:
        return None
    mount_point, mount_root = mounted
    raw_cgroup = str(cgroup)
    raw_root = str(mount_root)
    if raw_root != "/" and (raw_cgroup == raw_root or raw_cgroup.startswith(raw_root.rstrip("/") + "/")):
        relative = raw_cgroup[len(raw_root) :].lstrip("/")
    else:
        relative = raw_cgroup.lstrip("/")
    return mount_point / relative, mount_point


def _walk_to_mount(start: Path, mount_point: Path) -> Iterator[Path]:
    current = start
    while True:
        yield current
        if current == mount_point:
            return
        parent = current.parent
        if parent == current or mount_point not in parent.parents and parent != mount_point:
            return
        current = parent


def _cgroup_memory_constraints() -> tuple[int | None, int | None]:
    """Return the smallest applicable (limit, remaining) across ancestors."""
    limits: list[int] = []
    remaining: list[int] = []
    v2 = _mounted_cgroup_dir("cgroup2", None)
    if v2 is not None:
        start, mount_point = v2
        for directory in _walk_to_mount(start, mount_point):
            limit = _read_int(directory / "memory.max")
            current = _read_int(directory / "memory.current")
            if limit is not None:
                limits.append(limit)
                if current is not None:
                    remaining.append(max(0, limit - current))

    v1 = _mounted_cgroup_dir("cgroup", "memory")
    if v1 is not None:
        start, mount_point = v1
        for directory in _walk_to_mount(start, mount_point):
            limit = _read_int(directory / "memory.limit_in_bytes")
            current = _read_int(directory / "memory.usage_in_bytes")
            if limit is not None:
                limits.append(limit)
                if current is not None:
                    remaining.append(max(0, limit - current))
    return (min(limits) if limits else None, min(remaining) if remaining else None)


def _linux_memory_snapshot() -> MemorySnapshot:
    fields: dict[str, int] = {}
    try:
        for line in Path("/proc/meminfo").read_text().splitlines():
            name, separator, rest = line.partition(":")
            if not separator:
                continue
            match = re.match(r"\s*([0-9]+)\s+kB\s*$", rest)
            if match is not None:
                fields[name] = int(match.group(1)) * 1024
    except OSError as exc:
        raise ResourceError(f"cannot read /proc/meminfo: {exc}") from exc
    total = fields.get("MemTotal")
    available = fields.get("MemAvailable")
    if total is None or available is None:
        raise ResourceError("/proc/meminfo does not provide MemTotal and MemAvailable")
    cgroup_limit, cgroup_remaining = _cgroup_memory_constraints()
    source = "/proc/meminfo"
    if cgroup_limit is not None:
        total = min(total, cgroup_limit)
        source += " + cgroup"
    if cgroup_remaining is not None:
        available = min(available, cgroup_remaining)
    return MemorySnapshot(total=total, available=min(total, available), source=source)


def _macos_memory_snapshot() -> MemorySnapshot:
    try:
        total_raw = subprocess.run(
            ["sysctl", "-n", "hw.memsize"], check=True, capture_output=True, text=True
        ).stdout.strip()
        vm_stat = subprocess.run(["vm_stat"], check=True, capture_output=True, text=True).stdout
        total = int(total_raw)
    except (OSError, subprocess.CalledProcessError, ValueError) as exc:
        raise ResourceError(f"cannot read macOS memory availability: {exc}") from exc
    page_match = re.search(r"page size of ([0-9]+) bytes", vm_stat)
    if page_match is None:
        raise ResourceError("vm_stat did not report its page size")
    page_size = int(page_match.group(1))
    pages: dict[str, int] = {}
    for line in vm_stat.splitlines():
        match = re.match(r"([^:]+):\s*([0-9]+)\.\s*$", line)
        if match is not None:
            pages[match.group(1)] = int(match.group(2))
    available_pages = sum(pages.get(name, 0) for name in ("Pages free", "Pages inactive", "Pages speculative"))
    available = min(total, available_pages * page_size)
    return MemorySnapshot(total=total, available=available, source="sysctl + vm_stat")


def _posix_memory_snapshot() -> MemorySnapshot:
    try:
        page_size = int(os.sysconf("SC_PAGE_SIZE"))
        total = int(os.sysconf("SC_PHYS_PAGES")) * page_size
        available = int(os.sysconf("SC_AVPHYS_PAGES")) * page_size
    except (OSError, ValueError) as exc:
        raise ResourceError(f"cannot determine available memory: {exc}") from exc
    return MemorySnapshot(total=total, available=min(total, available), source="sysconf")


def memory_snapshot() -> MemorySnapshot:
    system = platform.system()
    if system == "Linux":
        return _linux_memory_snapshot()
    if system == "Darwin":
        return _macos_memory_snapshot()
    return _posix_memory_snapshot()


def _scope() -> str:
    for name in (SCOPE_ENV, "SPECULA_RUN_DIR", "SPECULA_WORK_DIR"):
        value = os.environ.get(name)
        if value:
            return str(Path(value).expanduser().resolve())
    return str(Path.cwd().resolve())


def _agent_scope(scope: str) -> str:
    for name in ("SPECULA_STOP_GATE_WORK_DIR", "SPECULA_WORK_DIR"):
        value = os.environ.get(name)
        if value:
            return str(Path(value).expanduser().resolve())
    return scope


def _ensure_private_dir(path: Path) -> None:
    try:
        info = path.lstat()
    except FileNotFoundError:
        # Two first TLCs for a run can reach this simultaneously. mkdir with
        # exist_ok closes that creation race; lstat below still rejects a
        # non-directory or symlink planted at the path.
        path.mkdir(parents=True, mode=0o700, exist_ok=True)
        info = path.lstat()
    if stat.S_ISLNK(info.st_mode) or not stat.S_ISDIR(info.st_mode):
        raise ResourceError(f"unsafe TLC resource directory: {path}")
    if hasattr(os, "getuid") and info.st_uid != os.getuid():
        raise ResourceError(f"TLC resource directory is owned by another user: {path}")
    with contextlib.suppress(OSError):
        path.chmod(0o700)


def _state_dir(scope: str) -> Path:
    configured = os.environ.get(STATE_DIR_ENV)
    if configured:
        root = Path(configured).expanduser().resolve()
    else:
        uid = os.getuid() if hasattr(os, "getuid") else 0
        root = Path(tempfile.gettempdir()) / f"specula-tlc-resources-{uid}"
    _ensure_private_dir(root)
    digest = hashlib.sha256(scope.encode()).hexdigest()[:24]
    state = root / digest
    _ensure_private_dir(state)
    return state


def _reservation_lock_path(state: Path, token: str) -> Path:
    if _TOKEN_RE.fullmatch(token) is None:
        raise ResourceError("TLC resource ledger contains an invalid reservation token")
    leases = state / "leases"
    _ensure_private_dir(leases)
    return leases / f"{token}.lock"


def _open_owner_lock(scope: str) -> OwnerLock:
    """Create and exclusively lock a unique liveness file for one TLC owner."""
    state = _state_dir(scope)
    flags = os.O_RDWR | os.O_CREAT | os.O_EXCL
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    for _ in range(10):
        token = uuid.uuid4().hex
        path = _reservation_lock_path(state, token)
        try:
            descriptor = os.open(path, flags, 0o600)
        except FileExistsError:
            continue
        try:
            info = os.fstat(descriptor)
            if not stat.S_ISREG(info.st_mode):
                raise ResourceError(f"unsafe TLC reservation lock: {path}")
            fcntl.flock(descriptor, fcntl.LOCK_EX)
            return OwnerLock(state=state, token=token, path=path, descriptor=descriptor)
        except BaseException:
            os.close(descriptor)
            with contextlib.suppress(FileNotFoundError):
                path.unlink()
            raise
    raise ResourceError("cannot allocate a unique TLC reservation lock")


def _validate_owner_lock(owner_lock: OwnerLock, state: Path) -> int:
    descriptor = owner_lock.descriptor
    if descriptor is None or owner_lock.state != state:
        raise ResourceError("TLC reservation owner lock is not active for this run")
    expected = _reservation_lock_path(state, owner_lock.token)
    if owner_lock.path != expected:
        raise ResourceError("TLC reservation owner lock path mismatch")
    try:
        descriptor_info = os.fstat(descriptor)
        path_info = expected.stat()
    except OSError as exc:
        raise ResourceError(f"cannot validate TLC reservation owner lock {expected}: {exc}") from exc
    if (
        not stat.S_ISREG(descriptor_info.st_mode)
        or descriptor_info.st_dev != path_info.st_dev
        or descriptor_info.st_ino != path_info.st_ino
    ):
        raise ResourceError(f"unsafe TLC reservation owner lock: {expected}")
    return descriptor


def _reservation_is_live(state: Path, token: str) -> bool:
    """Return whether the token's lock is held, independent of PID namespaces."""
    path = _reservation_lock_path(state, token)
    flags = os.O_RDWR
    if hasattr(os, "O_CLOEXEC"):
        flags |= os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        descriptor = os.open(path, flags)
    except FileNotFoundError:
        return False
    except OSError as exc:
        raise ResourceError(f"cannot inspect TLC reservation lock {path}: {exc}") from exc
    try:
        info = os.fstat(descriptor)
        if not stat.S_ISREG(info.st_mode):
            raise ResourceError(f"unsafe TLC reservation lock: {path}")
        try:
            fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            return True
        except OSError as exc:
            raise ResourceError(f"cannot inspect TLC reservation lock {path}: {exc}") from exc
        # No live owner can ever reacquire an existing token. Remove the stale
        # inode while holding its exclusive lock so another observer cannot race
        # with cleanup through the same pathname.
        try:
            path.unlink()
        except FileNotFoundError:
            pass
        except OSError as exc:
            raise ResourceError(f"cannot remove stale TLC reservation lock {path}: {exc}") from exc
        return False
    finally:
        os.close(descriptor)


def _clean_unreferenced_locks(state: Path, referenced: set[str]) -> None:
    """Remove unlocked owner candidates that died before entering the ledger."""
    leases = state / "leases"
    if not leases.exists():
        return
    _ensure_private_dir(leases)
    try:
        entries = list(leases.iterdir())
    except OSError as exc:
        raise ResourceError(f"cannot inspect TLC reservation locks in {leases}: {exc}") from exc
    for path in entries:
        match = re.fullmatch(r"([0-9a-f]{32})\.lock", path.name)
        if match is None:
            raise ResourceError(f"unsafe TLC reservation lock entry: {path}")
        token = match.group(1)
        if token not in referenced:
            # A live, not-yet-admitted owner may be waiting for the ledger lock;
            # its held flock is preserved. An unlocked inode can only be debris
            # from an owner killed before admission and is removed here.
            _reservation_is_live(state, token)


@contextlib.contextmanager
def _locked(state: Path) -> Iterator[None]:
    lock_path = state / "lock"
    descriptor = os.open(lock_path, os.O_RDWR | os.O_CREAT, 0o600)
    try:
        with os.fdopen(descriptor, "a+") as lock:
            fcntl.flock(lock.fileno(), fcntl.LOCK_EX)
            try:
                yield
            finally:
                fcntl.flock(lock.fileno(), fcntl.LOCK_UN)
    except BaseException:
        with contextlib.suppress(OSError):
            os.close(descriptor)
        raise


def _atomic_json(path: Path, payload: dict[str, Any]) -> None:
    descriptor, raw_tmp = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    tmp = Path(raw_tmp)
    try:
        with os.fdopen(descriptor, "w") as output:
            json.dump(payload, output, indent=2, sort_keys=True)
            output.write("\n")
            output.flush()
            os.fsync(output.fileno())
        tmp.chmod(0o600)
        tmp.replace(path)
    finally:
        with contextlib.suppress(FileNotFoundError):
            tmp.unlink()


def _atomic_text(path: Path, value: str) -> None:
    descriptor, raw_tmp = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    tmp = Path(raw_tmp)
    try:
        with os.fdopen(descriptor, "w") as output:
            output.write(value)
            output.flush()
            os.fsync(output.fileno())
        tmp.chmod(0o600)
        tmp.replace(path)
    finally:
        with contextlib.suppress(FileNotFoundError):
            tmp.unlink()


def _load_ledger(path: Path) -> dict[str, Any] | None:
    if not path.exists():
        return None
    try:
        value = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        raise ResourceError(f"cannot read TLC resource ledger {path}: {exc}") from exc
    if not isinstance(value, dict) or value.get("version") != LEDGER_VERSION:
        raise ResourceError(f"invalid TLC resource ledger: {path}")
    return value


def _process_identity(pid: int) -> str | None:
    proc_stat = Path(f"/proc/{pid}/stat")
    if proc_stat.is_file():
        try:
            raw = proc_stat.read_text()
            _before, separator, after = raw.rpartition(")")
            fields = after.split() if separator else []
            if len(fields) > 19:
                return f"linux:{fields[19]}"
        except OSError:
            return None
    try:
        result = subprocess.run(["ps", "-o", "lstart=", "-p", str(pid)], capture_output=True, text=True, check=False)
    except OSError:
        return None
    stamp = result.stdout.strip()
    return f"ps:{stamp}" if result.returncode == 0 and stamp else None


def _process_alive(pid: int, identity: str) -> bool:
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    current = _process_identity(pid)
    return current is None or current == identity


def _clean_stale(state: Path, ledger: dict[str, Any]) -> dict[str, dict[str, Any]]:
    raw = ledger.get("reservations")
    if not isinstance(raw, dict):
        raise ResourceError("TLC resource ledger has invalid reservations")
    live: dict[str, dict[str, Any]] = {}
    for token, value in raw.items():
        if not isinstance(token, str) or not isinstance(value, dict):
            raise ResourceError("TLC resource ledger contains a malformed reservation")
        pid = value.get("pid")
        identity = value.get("identity")
        memory = value.get("memory")
        workers = value.get("workers")
        agent = value.get("agent")
        if (
            not isinstance(pid, int)
            or not isinstance(identity, str)
            or not isinstance(memory, int)
            or memory < 0
            or not isinstance(workers, int)
            or workers < 1
            or not isinstance(agent, str)
        ):
            raise ResourceError("TLC resource ledger contains a malformed reservation")
        # PIDs and process start times are namespace-local diagnostics. The
        # owner-held flock is the only shared liveness authority.
        if _reservation_is_live(state, token):
            live[token] = value
    _clean_unreferenced_locks(state, set(raw))
    ledger["reservations"] = live
    return live


def _new_policy(
    scope: str,
    memory_raw: str,
    worker_raw: str | None,
    snapshot: MemorySnapshot | None,
) -> dict[str, Any]:
    try:
        configured_memory = parse_memory_limit(memory_raw)
        worker_limit = parse_worker_limit(worker_raw) if worker_raw is not None else None
    except ValueError as exc:
        raise ResourceError(str(exc)) from exc
    if configured_memory is None:
        measured = snapshot or memory_snapshot()
        limit = measured.available * AUTO_MEMORY_PERCENT // 100
        limit -= limit % MIB
        if limit < MIB:
            raise ResourceError("automatic TLC memory budget is below 1 MiB; set an explicit limit")
        memory: dict[str, Any] = {
            "mode": "auto",
            "limit": limit,
            "configured": "auto",
            "snapshot": {
                "total": measured.total,
                "available": measured.available,
                "other": max(0, measured.total - measured.available),
                "source": measured.source,
            },
        }
    else:
        memory = {
            "mode": "configured",
            "limit": configured_memory,
            "configured": memory_raw,
        }
    return {
        "version": LEDGER_VERSION,
        "scope": scope,
        "created": int(time.time()),
        "memory": memory,
        "worker_limit": worker_limit,
        "reservations": {},
    }


def _validate_policy(ledger: dict[str, Any], scope: str, memory_raw: str, worker_raw: str | None) -> None:
    if ledger.get("scope") != scope:
        raise ResourceError("TLC resource ledger scope mismatch")
    memory = ledger.get("memory")
    if not isinstance(memory, dict):
        raise ResourceError("TLC resource ledger has an invalid memory policy")
    stored_limit = memory.get("limit")
    if not isinstance(stored_limit, int):
        raise ResourceError("TLC resource ledger has an invalid memory policy")
    try:
        requested_memory = parse_memory_limit(memory_raw)
        requested_workers = parse_worker_limit(worker_raw) if worker_raw is not None else None
    except ValueError as exc:
        raise ResourceError(str(exc)) from exc
    stored_mode = memory.get("mode")
    same_memory = (requested_memory is None and stored_mode == "auto") or (
        requested_memory is not None and stored_mode == "configured" and requested_memory == stored_limit
    )
    if not same_memory:
        raise ResourceError(
            f"this Specula run already uses a {format_bytes(stored_limit)} TLC memory budget; "
            "the budget cannot change inside the run"
        )
    if ledger.get("worker_limit") != requested_workers:
        stored_workers = ledger.get("worker_limit")
        label = "unbounded" if stored_workers is None else str(stored_workers)
        raise ResourceError(
            f"this Specula run already uses TLC worker limit {label}; the limit cannot change inside the run"
        )


def _render_report(
    ledger: dict[str, Any],
    live: dict[str, dict[str, Any]],
    *,
    scope: str,
    agent: str,
    heap: int,
    offheap: int,
    workers: int,
    workers_label: str,
    admitted: bool,
    reasons: list[str],
) -> str:
    memory = ledger["memory"]
    memory_limit = int(memory["limit"])
    active_memory = sum(int(entry["memory"]) for entry in live.values())
    agent_memory = sum(int(entry["memory"]) for entry in live.values() if entry["agent"] == agent)
    active_workers = sum(int(entry["workers"]) for entry in live.values())
    agent_workers = sum(int(entry["workers"]) for entry in live.values() if entry["agent"] == agent)
    request_memory = heap + offheap
    remaining_before = max(0, memory_limit - active_memory)
    remaining_after = max(0, remaining_before - request_memory)
    scope_label = Path(scope).name or scope
    lines = [f"TLC resource budget (Specula run {scope_label}):"]
    if memory["mode"] == "auto":
        measured = memory.get("snapshot")
        if not isinstance(measured, dict):
            raise ResourceError("TLC resource ledger has an invalid automatic memory snapshot")
        lines += [
            f"  memory source: auto ({AUTO_MEMORY_PERCENT}% of effective available memory at first TLC start)",
            f"  effective memory at start: {format_bytes(int(measured['total']))} total, "
            f"{format_bytes(int(measured['available']))} available",
            f"  other/system use at start: {format_bytes(int(measured['other']))}",
        ]
    else:
        lines += [
            f"  memory source: user config ({memory['configured']})",
            "  external memory use: not included in this configured run bound",
        ]
    lines += [
        f"  memory limit: {format_bytes(memory_limit)}",
        f"  active TLC reserved before request: {format_bytes(active_memory)} "
        f"(this agent: {format_bytes(agent_memory)})",
        f"  this request: {format_bytes(request_memory)} "
        f"(heap {format_bytes(heap)} + off-heap {format_bytes(offheap)})",
        f"  remaining before request: {format_bytes(remaining_before)}",
    ]
    if admitted:
        lines.append(f"  remaining after admission: {format_bytes(remaining_after)}")
    worker_limit = ledger.get("worker_limit")
    worker_bound = "unbounded (report only)" if worker_limit is None else str(worker_limit)
    lines += [
        f"  worker limit: {worker_bound}",
        f"  active TLC workers before request: {active_workers} (this agent: {agent_workers})",
        f"  this request workers: {workers} ({workers_label})",
    ]
    if isinstance(worker_limit, int):
        worker_remaining_before = max(0, worker_limit - active_workers)
        lines.append(f"  remaining workers before request: {worker_remaining_before}")
        if admitted:
            lines.append(f"  remaining workers after admission: {max(0, worker_remaining_before - workers)}")
    if workers_label == "auto":
        lines.append("  worker note: auto is per TLC; concurrent auto runs can oversubscribe CPUs")
    if admitted:
        lines.append("  result: admitted")
    else:
        lines.append(f"  result: rejected; {'; '.join(reasons)}")
        lines.append("  action: reduce -m/-M or -w, wait for an active TLC to finish, or change the run config")
    return "\n".join(lines)


def acquire(
    *,
    heap: int,
    offheap: int,
    workers: int,
    workers_label: str,
    owner_lock: OwnerLock,
    lease_file: Path,
    owner_pid: int | None = None,
    scope: str | None = None,
    agent: str | None = None,
    memory_limit_raw: str | None = None,
    worker_limit_raw: str | None = None,
    snapshot: MemorySnapshot | None = None,
    precommit: Callable[[], bool] | None = None,
) -> Admission:
    if heap < 1 or offheap < 1:
        raise ResourceError("TLC heap and off-heap memory must both be positive")
    if workers < 1:
        raise ResourceError("TLC workers must be a positive integer")
    resolved_scope = scope or _scope()
    resolved_agent = agent or _agent_scope(resolved_scope)
    memory_raw = memory_limit_raw if memory_limit_raw is not None else (os.environ.get(MEMORY_LIMIT_ENV) or "auto")
    worker_raw = worker_limit_raw if worker_limit_raw is not None else (os.environ.get(WORKER_LIMIT_ENV) or None)
    state = _state_dir(resolved_scope)
    _validate_owner_lock(owner_lock, state)
    ledger_path = state / "ledger.json"
    diagnostic_pid = owner_pid if owner_pid is not None else os.getpid()
    identity = _process_identity(diagnostic_pid) or "unavailable"

    with _locked(state):
        if precommit is not None and not precommit():
            raise ResourceError("TLC owner was cancelled before admission")
        _validate_owner_lock(owner_lock, state)
        ledger = _load_ledger(ledger_path)
        if ledger is None:
            ledger = _new_policy(resolved_scope, memory_raw, worker_raw, snapshot)
        else:
            _validate_policy(ledger, resolved_scope, memory_raw, worker_raw)
        live = _clean_stale(state, ledger)
        memory_policy = ledger["memory"]
        memory_limit = int(memory_policy["limit"])
        worker_limit = ledger.get("worker_limit")
        active_memory = sum(int(entry["memory"]) for entry in live.values())
        active_workers = sum(int(entry["workers"]) for entry in live.values())
        request_memory = heap + offheap
        reasons: list[str] = []
        if active_memory + request_memory > memory_limit:
            reasons.append(
                f"aggregate memory would be {format_bytes(active_memory + request_memory)}, "
                f"above {format_bytes(memory_limit)}"
            )
        if isinstance(worker_limit, int) and active_workers + workers > worker_limit:
            reasons.append(f"aggregate workers would be {active_workers + workers}, above {worker_limit}")
        admitted = not reasons
        report = _render_report(
            ledger,
            live,
            scope=resolved_scope,
            agent=resolved_agent,
            heap=heap,
            offheap=offheap,
            workers=workers,
            workers_label=workers_label,
            admitted=admitted,
            reasons=reasons,
        )
        if not admitted:
            _atomic_json(ledger_path, ledger)
            return Admission(False, report)

        token = owner_lock.token
        if token in live:
            raise ResourceError("TLC reservation owner lock is already admitted")
        live[token] = {
            "pid": diagnostic_pid,
            "identity": identity,
            "memory": request_memory,
            "heap": heap,
            "offheap": offheap,
            "workers": workers,
            "workers_label": workers_label,
            "agent": resolved_agent,
            "created": int(time.time()),
        }
        ledger["reservations"] = live
        _atomic_json(ledger_path, ledger)
        try:
            _atomic_json(lease_file, {"state": str(state), "token": token})
        except BaseException:
            live.pop(token, None)
            ledger["reservations"] = live
            _atomic_json(ledger_path, ledger)
            raise
        return Admission(True, report)


def release(lease_file: Path) -> None:
    try:
        value = json.loads(lease_file.read_text())
    except FileNotFoundError:
        return
    except (OSError, json.JSONDecodeError) as exc:
        raise ResourceError(f"cannot read TLC resource lease {lease_file}: {exc}") from exc
    if (
        not isinstance(value, dict)
        or not isinstance(value.get("state"), str)
        or not isinstance(value.get("token"), str)
    ):
        raise ResourceError(f"invalid TLC resource lease: {lease_file}")
    state = Path(value["state"])
    token = value["token"]
    ledger_path = state / "ledger.json"
    if state.is_dir():
        with _locked(state):
            ledger = _load_ledger(ledger_path)
            if ledger is not None:
                live = _clean_stale(state, ledger)
                if token in live:
                    raise ResourceError("cannot release TLC resources while the owner is still running")
                ledger["reservations"] = live
                _atomic_json(ledger_path, ledger)
    with contextlib.suppress(FileNotFoundError):
        lease_file.unlink()


def _publish_owner_status(status_file: Path, report_file: Path, status: str, report: str) -> None:
    """Publish the report first and the status commit marker last."""
    _atomic_text(report_file, f"{report.rstrip()}\n")
    _atomic_text(status_file, f"{status}\n")


def run_owner(
    *,
    heap: int,
    offheap: int,
    workers: int,
    workers_label: str,
    lease_file: Path,
    status_file: Path,
    report_file: Path,
    start_file: Path,
    stop_file: Path,
    parent_pid: int,
    command: list[str],
) -> int:
    """Reserve, wait for the wrapper handoff, then exec TLC with a live lock."""
    owner_lock: OwnerLock | None = None
    admitted = False
    try:
        if not command:
            raise ResourceError("TLC owner command is empty")
        parent_identity = _process_identity(parent_pid)
        if parent_identity is None or not _process_alive(parent_pid, parent_identity):
            raise ResourceError(f"cannot start TLC for non-running wrapper process {parent_pid}")

        def wrapper_active() -> bool:
            return not stop_file.exists() and _process_alive(parent_pid, parent_identity)

        if not wrapper_active():
            raise ResourceError("TLC owner was cancelled before admission")
        resolved_scope = _scope()
        owner_lock = _open_owner_lock(resolved_scope)
        result = acquire(
            heap=heap,
            offheap=offheap,
            workers=workers,
            workers_label=workers_label,
            owner_lock=owner_lock,
            lease_file=lease_file,
            owner_pid=os.getpid(),
            scope=resolved_scope,
            precommit=wrapper_active,
        )
        if not result.admitted:
            _publish_owner_status(status_file, report_file, "rejected", result.report)
            return 2
        admitted = True
        _publish_owner_status(status_file, report_file, "admitted", result.report)

        deadline = time.monotonic() + OWNER_START_TIMEOUT_SECONDS
        while time.monotonic() < deadline:
            if start_file.exists():
                descriptor = _validate_owner_lock(owner_lock, owner_lock.state)
                os.set_inheritable(descriptor, True)
                os.execvpe(command[0], command, os.environ.copy())
            if not wrapper_active():
                raise ResourceError("TLC owner was cancelled before Java started")
            time.sleep(OWNER_POLL_SECONDS)
        raise ResourceError("TLC owner timed out waiting for the wrapper start signal")
    except (ResourceError, ValueError, OSError) as exc:
        message = f"TLC resource budget error: {exc}"
        with contextlib.suppress(OSError):
            _publish_owner_status(status_file, report_file, "error", message)
        print(message, file=sys.stderr)
        return 2
    finally:
        if owner_lock is not None:
            if admitted:
                owner_lock.close()
                try:
                    release(lease_file)
                except (ResourceError, OSError) as exc:
                    print(f"Warning: could not release TLC resource reservation: {exc}", file=sys.stderr)
            else:
                owner_lock.discard()


def enforce_timeout(owner_pid: int, seconds: int, status_file: Path) -> bool:
    """Terminate the original owner at its deadline; return whether signalled."""
    if seconds < 1:
        raise ResourceError("TLC timeout must be a positive number of seconds")
    identity = _process_identity(owner_pid)
    if identity is None:
        raise ResourceError(f"cannot identify TLC timeout owner {owner_pid}")

    pidfd: int | None = None
    if hasattr(os, "pidfd_open"):
        with contextlib.suppress(OSError):
            pidfd = os.pidfd_open(owner_pid)
    if pidfd is not None and _process_identity(owner_pid) != identity:
        os.close(pidfd)
        raise ResourceError(f"TLC timeout owner {owner_pid} exited during watchdog startup")
    try:
        try:
            status_file.write_text("ready\n")
        except OSError as exc:
            raise ResourceError(f"cannot publish TLC timeout watchdog readiness: {exc}") from exc
        time.sleep(seconds)
        if pidfd is not None and hasattr(signal, "pidfd_send_signal"):
            with contextlib.suppress(OSError):
                status_file.write_text("timed-out\n")
            try:
                signal.pidfd_send_signal(pidfd, signal.SIGTERM)
            except ProcessLookupError:
                with contextlib.suppress(OSError):
                    status_file.write_text("owner-exited\n")
                return False
            return True

        # Without pidfd, fail safe unless the process identity is known and
        # still matches. Ledger cleanup treats an unavailable identity as live,
        # but a watchdog must never signal an unrelated reused PID.
        try:
            os.kill(owner_pid, 0)
        except (ProcessLookupError, PermissionError):
            return False
        if _process_identity(owner_pid) != identity:
            return False
        with contextlib.suppress(OSError):
            status_file.write_text("timed-out\n")
        if _process_identity(owner_pid) != identity:
            with contextlib.suppress(OSError):
                status_file.write_text("owner-exited\n")
            return False
        try:
            os.kill(owner_pid, signal.SIGTERM)
        except ProcessLookupError:
            with contextlib.suppress(OSError):
                status_file.write_text("owner-exited\n")
            return False
        return True
    finally:
        if pidfd is not None:
            os.close(pidfd)


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    owner_parser = commands.add_parser("owner")
    owner_parser.add_argument("--heap", required=True)
    owner_parser.add_argument("--offheap", required=True)
    owner_parser.add_argument("--workers", required=True, type=int)
    owner_parser.add_argument("--workers-label", required=True)
    owner_parser.add_argument("--lease-file", required=True, type=Path)
    owner_parser.add_argument("--status-file", required=True, type=Path)
    owner_parser.add_argument("--report-file", required=True, type=Path)
    owner_parser.add_argument("--start-file", required=True, type=Path)
    owner_parser.add_argument("--stop-file", required=True, type=Path)
    owner_parser.add_argument("--parent-pid", required=True, type=int)
    owner_parser.add_argument("owner_command", nargs=argparse.REMAINDER)
    release_parser = commands.add_parser("release")
    release_parser.add_argument("--lease-file", required=True, type=Path)
    watchdog_parser = commands.add_parser("watchdog")
    watchdog_parser.add_argument("--pid", required=True, type=int)
    watchdog_parser.add_argument("--seconds", required=True, type=int)
    watchdog_parser.add_argument("--status-file", required=True, type=Path)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = _build_parser().parse_args(argv)
    try:
        if args.command == "release":
            release(args.lease_file)
            return 0
        if args.command == "watchdog":
            timed_out = enforce_timeout(args.pid, args.seconds, args.status_file)
            return 124 if timed_out else 0
        owner_command = list(args.owner_command)
        if owner_command and owner_command[0] == "--":
            owner_command.pop(0)
        return run_owner(
            heap=parse_memory_size(args.heap),
            offheap=parse_memory_size(args.offheap),
            workers=args.workers,
            workers_label=args.workers_label,
            lease_file=args.lease_file,
            status_file=args.status_file,
            report_file=args.report_file,
            start_file=args.start_file,
            stop_file=args.stop_file,
            parent_pid=args.parent_pid,
            command=owner_command,
        )
    except (ResourceError, ValueError, OSError) as exc:
        message = f"TLC resource budget error: {exc}"
        if args.command == "owner":
            with contextlib.suppress(OSError):
                _publish_owner_status(args.status_file, args.report_file, "error", message)
        print(message, file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
