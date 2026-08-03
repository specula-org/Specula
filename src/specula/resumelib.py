"""Durable ownership for unfinished agent conversations in an isolated run.

Native ``*.resume.json`` files bind an adapter invocation to an exact provider
session.  They intentionally outlive successful calls, so they cannot also say
whether a logical turn is unfinished.  This module supplies that lifecycle bit:
one active record per resumable call and a short-lived accepted-call marker so
a partially completed multi-target phase does not repeat finished work.

The owning phase removes accepted markers when the whole phase settles.  No
general pipeline cursor or scheduler state is persisted here.
"""

from __future__ import annotations

import contextlib
import hashlib
import json
import os
import stat
import tempfile
import threading
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from .adapters.utils import run_lock as adapter_run_lock

RESUME_DIRNAME = ".specula-resume"
CONFIG_FILENAME = "config.json"
ACTIVE_DIRNAME = "active"
COMPLETED_DIRNAME = "completed"
SCHEMA_VERSION = 1

INVOCATION_ENV = "SPECULA_INVOCATION_ID"
MANUAL_ENV = "SPECULA_MANUAL_RESUME"
FRESH_ENV = "SPECULA_FRESH_CONTEXT"
RUN_LOCK_FD_ENV = adapter_run_lock.RUN_LOCK_FD_ENV


class ResumeError(RuntimeError):
    """A manual resume cannot safely continue the recorded conversation."""


@dataclass(frozen=True)
class ResumeClaim:
    """Result of claiming one logical turn for an adapter invocation."""

    attempt: int
    manual: bool
    resumable: bool
    rate_limit_attempt: int = 1
    policy_attempt: int = 0
    transient_attempt: int = 0
    invocation_attempt: int = 0
    retry_reason: str = "fresh"


_lock = threading.RLock()


def _run_dir() -> Path | None:
    raw = os.environ.get("SPECULA_RUN_DIR")
    return Path(raw).expanduser().absolute() if raw else None


def resume_dir(run_dir: Path) -> Path:
    return run_dir / RESUME_DIRNAME


def config_path(run_dir: Path) -> Path:
    return resume_dir(run_dir) / CONFIG_FILENAME


def active_dir(run_dir: Path) -> Path:
    return resume_dir(run_dir) / ACTIVE_DIRNAME


def completed_dir(run_dir: Path) -> Path:
    return resume_dir(run_dir) / COMPLETED_DIRNAME


def _require_directory(path: Path, label: str) -> None:
    try:
        info = path.lstat()
    except OSError as exc:
        raise ResumeError(f"cannot inspect {label} {path}: {exc}") from exc
    if not stat.S_ISDIR(info.st_mode):
        raise ResumeError(f"{label} is not a real directory: {path}")


def ensure_storage(run_dir: Path) -> None:
    """Create and verify the dispatcher-owned resume directories."""
    root = resume_dir(run_dir)
    try:
        root.mkdir(mode=0o700, parents=False, exist_ok=True)
    except OSError as exc:
        raise ResumeError(f"cannot create resume directory {root}: {exc}") from exc
    _require_directory(root, "resume directory")
    for path, label in (
        (active_dir(run_dir), "active conversation directory"),
        (completed_dir(run_dir), "completed call directory"),
    ):
        try:
            path.mkdir(mode=0o700, exist_ok=True)
        except OSError as exc:
            raise ResumeError(f"cannot create {label} {path}: {exc}") from exc
        _require_directory(path, label)


def _atomic_write(path: Path, data: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = json.dumps(data, indent=2, sort_keys=True) + "\n"
    fd, raw_tmp = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    tmp = Path(raw_tmp)
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(tmp, path)
    finally:
        with contextlib.suppress(FileNotFoundError):
            tmp.unlink()


def _clear_native_state(path: Path) -> None:
    """Remove a previous logical turn's provider session before publication."""
    try:
        path.unlink()
    except FileNotFoundError:
        return
    except OSError as exc:
        raise ResumeError(f"cannot clear stale native session state {path}: {exc}") from exc
    try:
        path.lstat()
    except FileNotFoundError:
        return
    except OSError as exc:
        raise ResumeError(f"cannot verify cleared native session state {path}: {exc}") from exc
    raise ResumeError(f"stale native session state still exists after removal: {path}")


def inherited_run_lock_fds() -> tuple[int, ...]:
    """Return the validated run-lock lease inherited from the dispatcher."""
    try:
        return adapter_run_lock.inherited_run_lock_fds()
    except adapter_run_lock.RunLockError as exc:
        raise ResumeError(str(exc)) from exc


def _read_object(path: Path, label: str) -> dict[str, Any]:
    try:
        info = path.lstat()
        if not stat.S_ISREG(info.st_mode):
            raise ResumeError(f"{label} is not a regular file: {path}")
        value: object = json.loads(path.read_text())
    except FileNotFoundError as exc:
        raise ResumeError(f"missing {label}: {path}") from exc
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise ResumeError(f"cannot read {label} {path}: {exc}") from exc
    if not isinstance(value, dict):
        raise ResumeError(f"invalid {label}: expected a JSON object in {path}")
    return value


def initialize_run(run_dir: Path, *, reset: bool = False) -> None:
    """Create the version marker, optionally abandoning all unfinished turns."""
    with _lock:
        ensure_storage(run_dir)
        marker = config_path(run_dir)
        if marker.exists() or marker.is_symlink():
            data = _read_object(marker, "resume config")
            if data.get("version") != SCHEMA_VERSION:
                raise ResumeError(f"unsupported resume config version in {marker}")
        else:
            _atomic_write(marker, {"version": SCHEMA_VERSION})
        if reset:
            for directory in (active_dir(run_dir), completed_dir(run_dir)):
                for path in directory.iterdir():
                    if path.name.endswith(".json") or path.is_symlink():
                        try:
                            path.unlink()
                        except OSError as exc:
                            raise ResumeError(f"cannot abandon saved agent state {path}: {exc}") from exc


def require_supported_run(run_dir: Path) -> None:
    data = _read_object(config_path(run_dir), "resume config")
    if data.get("version") != SCHEMA_VERSION:
        raise ResumeError(f"unsupported resume config version in {config_path(run_dir)}")
    if not isinstance(data.get("configuration"), dict):
        raise ResumeError(
            "this run was created without manual conversation checkpoints; pass --fresh-context to continue"
        )


def save_configuration(run_dir: Path, configuration: dict[str, Any]) -> None:
    with _lock:
        marker = _read_object(config_path(run_dir), "resume config")
        if marker.get("version") != SCHEMA_VERSION:
            raise ResumeError(f"unsupported resume config version in {config_path(run_dir)}")
        marker["configuration"] = configuration
        _atomic_write(config_path(run_dir), marker)


def load_configuration(run_dir: Path) -> dict[str, Any]:
    marker = _read_object(config_path(run_dir), "resume config")
    if marker.get("version") != SCHEMA_VERSION or not isinstance(marker.get("configuration"), dict):
        raise ResumeError(f"invalid resume configuration in {config_path(run_dir)}")
    return dict(marker["configuration"])


def _logical_id(logical: tuple[str, ...]) -> str:
    encoded = json.dumps(list(logical), ensure_ascii=False, separators=(",", ":")).encode()
    return hashlib.sha256(encoded).hexdigest()


def _entry_path(run_dir: Path, logical: tuple[str, ...]) -> Path:
    return active_dir(run_dir) / f"{_logical_id(logical)}.json"


def _binding(
    *,
    phase: str,
    target: str,
    kind: str,
    adapter: Path,
    model: str | None,
    effort: str | None,
    claude_alias: str,
    cwd: Path | None,
    resume_state: Path,
    prompt_file: Path,
    log_file: Path,
    finding_id: str | None,
) -> dict[str, Any]:
    return {
        "phase": phase,
        "target": target,
        "kind": kind,
        "finding_id": finding_id,
        "adapter": adapter.stem,
        "model": model,
        "effort": effort,
        "claude_alias": claude_alias,
        "cwd": str(cwd.absolute()) if cwd is not None else None,
        "resume_state": str(resume_state.absolute()),
        "prompt_file": str(prompt_file.absolute()),
        "log_file": str(log_file.absolute()),
    }


def enabled() -> bool:
    run_dir = _run_dir()
    if run_dir is None or not os.environ.get(INVOCATION_ENV):
        return False
    root = resume_dir(run_dir)
    if not root.exists() and not root.is_symlink():
        return False
    ensure_storage(run_dir)
    try:
        info = config_path(run_dir).lstat()
    except FileNotFoundError:
        return False
    except OSError as exc:
        raise ResumeError(f"cannot inspect resume config {config_path(run_dir)}: {exc}") from exc
    if not stat.S_ISREG(info.st_mode):
        raise ResumeError(f"resume config is not a regular file: {config_path(run_dir)}")
    return True


def manual_mode() -> bool:
    return enabled() and os.environ.get(MANUAL_ENV) == "1"


def fresh_mode() -> bool:
    return enabled() and os.environ.get(FRESH_ENV) == "1"


def _validate_entry(entry: dict[str, Any], path: Path, label: str) -> None:
    logical = entry.get("logical")
    if (
        entry.get("version") != SCHEMA_VERSION
        or not isinstance(logical, list)
        or not logical
        or not all(isinstance(part, str) and part for part in logical)
    ):
        raise ResumeError(f"invalid {label} record: {path}")
    for field in ("phase", "target", "kind", "adapter", "claude_alias", "resume_state", "prompt_file", "log_file"):
        if not isinstance(entry.get(field), str) or not entry[field]:
            raise ResumeError(f"invalid {label} {field} in {path}")
    for field in ("model", "effort", "cwd", "finding_id"):
        if entry.get(field) is not None and not isinstance(entry[field], str):
            raise ResumeError(f"invalid {label} {field} in {path}")
    if not isinstance(entry.get("owner"), str) or not entry["owner"]:
        raise ResumeError(f"invalid {label} owner in {path}")
    for field in ("attempt", "started_ns", "updated_ns"):
        value = entry.get(field)
        if not isinstance(value, int) or isinstance(value, bool) or value < 1:
            raise ResumeError(f"invalid {label} {field} in {path}")
    for field, minimum in (
        ("rate_limit_attempt", 1),
        ("policy_attempt", 0),
        ("transient_attempt", 0),
        ("invocation_attempt", 0),
    ):
        value = entry.get(field, minimum)
        if not isinstance(value, int) or isinstance(value, bool) or value < minimum:
            raise ResumeError(f"invalid {label} {field} in {path}")
    retry_reason = entry.get("retry_reason", "fresh")
    if retry_reason not in {"fresh", "manual", "policy", "transient", "rate_limit"}:
        raise ResumeError(f"invalid {label} retry_reason in {path}")


def _claim(entry: dict[str, Any], *, attempt: int, manual: bool, resumable: bool) -> ResumeClaim:
    return ResumeClaim(
        attempt=attempt,
        manual=manual,
        resumable=resumable,
        rate_limit_attempt=entry.get("rate_limit_attempt", 1),
        policy_attempt=entry.get("policy_attempt", 0),
        transient_attempt=entry.get("transient_attempt", 0),
        invocation_attempt=entry.get("invocation_attempt", 0),
        retry_reason=entry.get("retry_reason", "fresh"),
    )


def _require_owner(entry: dict[str, Any], path: Path, action: str) -> None:
    invocation = os.environ.get(INVOCATION_ENV)
    if entry.get("owner") != invocation:
        raise ResumeError(
            f"cannot {action} conversation {tuple(entry.get('logical', []))!r}: checkpoint ownership changed in {path}"
        )


def _entries(directory: Path, label: str) -> list[dict[str, Any]]:
    _require_directory(directory, f"{label} directory")
    entries: list[dict[str, Any]] = []
    for path in sorted(directory.glob("*.json")):
        entry = _read_object(path, label)
        _validate_entry(entry, path, label)
        logical = tuple(entry["logical"])
        if path.name != f"{_logical_id(logical)}.json":
            raise ResumeError(f"invalid {label} filename for {logical!r}: {path}")
        entry["_path"] = str(path)
        entries.append(entry)
    return sorted(entries, key=lambda item: (item["started_ns"], str(item["_path"])))


def active_entries(run_dir: Path | None = None) -> list[dict[str, Any]]:
    root = run_dir or _run_dir()
    if root is None:
        return []
    storage = resume_dir(root)
    if not storage.exists() and not storage.is_symlink():
        return []
    with _lock:
        ensure_storage(root)
        return _entries(active_dir(root), "active conversation")


def completed_entries(run_dir: Path | None = None) -> list[dict[str, Any]]:
    root = run_dir or _run_dir()
    if root is None:
        return []
    storage = resume_dir(root)
    if not storage.exists() and not storage.is_symlink():
        return []
    with _lock:
        ensure_storage(root)
        return _entries(completed_dir(root), "completed call")


def unfinished_entries(*, phase: str | None = None, target: str | None = None) -> list[dict[str, Any]]:
    entries = active_entries()
    if phase is not None:
        entries = [entry for entry in entries if entry.get("phase") == phase]
    if target is not None:
        entries = [entry for entry in entries if entry.get("target") == target]
    return entries


def previous_entries(*, phase: str | None = None, target: str | None = None) -> list[dict[str, Any]]:
    invocation = os.environ.get(INVOCATION_ENV)
    return [entry for entry in unfinished_entries(phase=phase, target=target) if entry.get("owner") != invocation]


def ensure_phase(phase: str) -> None:
    """Refuse to start a different phase while an old conversation is pending."""
    if not manual_mode():
        return
    old = previous_entries()
    if not old:
        return
    phases = {str(entry.get("phase")) for entry in old}
    if phases != {phase}:
        waiting = ", ".join(sorted(phases))
        raise ResumeError(
            f"this run has unfinished conversation(s) in {waiting}; "
            "resume that recorded phase, or pass --fresh-context to start over"
        )


def prepare_turn(
    logical: tuple[str, ...],
    *,
    phase: str,
    target: str,
    kind: str,
    adapter: Path,
    model: str | None,
    effort: str | None,
    claude_alias: str,
    cwd: Path | None,
    resume_state: Path,
    prompt_file: Path,
    log_file: Path,
    finding_id: str | None = None,
) -> ResumeClaim:
    """Register a fresh turn or claim its exact unfinished predecessor."""
    if not enabled():
        return ResumeClaim(attempt=1, manual=False, resumable=False)
    run_dir = _run_dir()
    assert run_dir is not None
    invocation = os.environ[INVOCATION_ENV]
    path = _entry_path(run_dir, logical)
    expected = _binding(
        phase=phase,
        target=target,
        kind=kind,
        adapter=adapter,
        model=model,
        effort=effort,
        claude_alias=claude_alias,
        cwd=cwd,
        resume_state=resume_state,
        prompt_file=prompt_file,
        log_file=log_file,
        finding_id=finding_id,
    )
    with _lock:
        if path.exists() or path.is_symlink():
            entry = _read_object(path, "active conversation")
            if entry.get("version") != SCHEMA_VERSION or entry.get("logical") != list(logical):
                raise ResumeError(f"active conversation identity mismatch in {path}")
            for field, value in expected.items():
                if entry.get(field) != value:
                    raise ResumeError(
                        f"cannot resume {target} {phase}: recorded {field}={entry.get(field)!r}, "
                        f"current value is {value!r}; pass --fresh-context to start over"
                    )
            previous_owner = entry.get("owner")
            manual = previous_owner != invocation
            if manual and not manual_mode():
                raise ResumeError(f"unfinished conversation {logical!r} requires specula run --run-id")
            if manual:
                try:
                    state_info = resume_state.lstat()
                except OSError as exc:
                    raise ResumeError(
                        f"cannot resume {target} {phase}: native session state is unavailable at {resume_state}; "
                        "pass --fresh-context to start over"
                    ) from exc
                if not stat.S_ISREG(state_info.st_mode):
                    raise ResumeError(f"unsafe native session state for {target} {phase}: {resume_state}")
            _validate_entry(entry, path, "active conversation")
            attempt = entry["attempt"] + 1
            entry.update(expected)
            entry.update({"owner": invocation, "attempt": attempt, "updated_ns": time.time_ns()})
            _atomic_write(path, entry)
            return _claim(
                entry,
                attempt=attempt,
                manual=manual,
                resumable=resume_state.is_file(),
            )

        for entry in active_entries(run_dir):
            if entry.get("resume_state") == expected["resume_state"]:
                raise ResumeError(
                    f"native session state path already belongs to unfinished conversation {entry['logical']!r}"
                )
        # A native state file outlives the adapter call that created it.  For a
        # new logical turn, remove that stale binding before making the active
        # checkpoint visible.  A crash can now leave neither record, or an
        # active record with no session yet, but never a new record that points
        # at an old completed provider session.
        _clear_native_state(resume_state)
        now = time.time_ns()
        entry = {
            "version": SCHEMA_VERSION,
            "logical": list(logical),
            **expected,
            "owner": invocation,
            "attempt": 1,
            "started_ns": now,
            "updated_ns": now,
        }
        _atomic_write(path, entry)
        return ResumeClaim(attempt=1, manual=False, resumable=False)


def update_turn(logical: tuple[str, ...], **updates: Any) -> None:
    if not enabled():
        return
    run_dir = _run_dir()
    assert run_dir is not None
    path = _entry_path(run_dir, logical)
    with _lock:
        allowed = {
            "rate_limit_attempt",
            "policy_attempt",
            "transient_attempt",
            "invocation_attempt",
            "retry_reason",
        }
        if set(updates) - allowed:
            raise ResumeError(f"unsupported conversation cursor update for {logical!r}")
        entry = _read_object(path, "active conversation")
        if entry.get("logical") != list(logical):
            raise ResumeError(f"active conversation identity mismatch in {path}")
        _validate_entry(entry, path, "active conversation")
        _require_owner(entry, path, "update")
        entry.update(updates)
        entry["updated_ns"] = time.time_ns()
        _validate_entry(entry, path, "active conversation")
        _atomic_write(path, entry)


def complete_turn(logical: tuple[str, ...], *, allow_previous_owner: bool = False) -> None:
    if not enabled():
        return
    run_dir = _run_dir()
    assert run_dir is not None
    path = _entry_path(run_dir, logical)
    with _lock:
        if not path.exists() and not path.is_symlink():
            return
        entry = _read_object(path, "active conversation")
        _validate_entry(entry, path, "active conversation")
        if entry.get("logical") != list(logical):
            raise ResumeError(f"active conversation identity mismatch in {path}")
        if not (allow_previous_owner and manual_mode()):
            _require_owner(entry, path, "complete")
        try:
            path.unlink()
        except OSError as exc:
            raise ResumeError(f"cannot complete conversation {logical!r}: {exc}") from exc


def reconcile_completed(logical: tuple[str, ...]) -> None:
    """Close mark_completed's safe write-before-unlink crash window."""
    if not enabled():
        return
    run_dir = _run_dir()
    assert run_dir is not None
    active_path = _entry_path(run_dir, logical)
    done_path = completed_dir(run_dir) / active_path.name
    with _lock:
        done = _read_object(done_path, "completed call")
        _validate_entry(done, done_path, "completed call")
        if done.get("logical") != list(logical):
            raise ResumeError(f"completed call identity mismatch in {done_path}")
        if not active_path.exists() and not active_path.is_symlink():
            return
        active = _read_object(active_path, "active conversation")
        _validate_entry(active, active_path, "active conversation")
        if active.get("logical") != list(logical):
            raise ResumeError(f"active conversation identity mismatch in {active_path}")
        comparable_active = {key: value for key, value in active.items() if key != "updated_ns"}
        comparable_done = {key: value for key, value in done.items() if key != "updated_ns"}
        if comparable_active != comparable_done or done["updated_ns"] < active["updated_ns"]:
            raise ResumeError(f"completed call does not match active conversation {logical!r}")
        try:
            active_path.unlink()
        except OSError as exc:
            raise ResumeError(f"cannot reconcile completed call {logical!r}: {exc}") from exc


def mark_completed(logical: tuple[str, ...]) -> None:
    """Remember an accepted call so a partial multi-target resume skips it."""
    if not enabled():
        return
    run_dir = _run_dir()
    assert run_dir is not None
    active_path = _entry_path(run_dir, logical)
    done_path = completed_dir(run_dir) / active_path.name
    with _lock:
        if active_path.exists() or active_path.is_symlink():
            entry = _read_object(active_path, "active conversation")
            _validate_entry(entry, active_path, "active conversation")
            if entry["logical"] != list(logical):
                raise ResumeError(f"active conversation identity mismatch in {active_path}")
            _require_owner(entry, active_path, "complete")
            entry["updated_ns"] = time.time_ns()
            _atomic_write(done_path, entry)
            try:
                active_path.unlink()
            except OSError as exc:
                raise ResumeError(f"cannot complete call {logical!r}: {exc}") from exc
            return
        if done_path.exists() or done_path.is_symlink():
            entry = _read_object(done_path, "completed call")
            _validate_entry(entry, done_path, "completed call")
            if entry["logical"] != list(logical):
                raise ResumeError(f"completed call identity mismatch in {done_path}")
            return
        raise ResumeError(f"missing active conversation for accepted call {logical!r}")


def completed_logicals(prefix: tuple[str, ...] = ()) -> set[tuple[str, ...]]:
    result: set[tuple[str, ...]] = set()
    for entry in completed_entries():
        logical = tuple(str(part) for part in entry["logical"])
        if logical[: len(prefix)] == prefix:
            result.add(logical)
    return result


def clear_completed(prefix: tuple[str, ...] = ()) -> None:
    for entry in completed_entries():
        logical = tuple(str(part) for part in entry["logical"])
        if logical[: len(prefix)] != prefix:
            continue
        run_dir = _run_dir()
        if run_dir is None:
            return
        path = completed_dir(run_dir) / f"{_logical_id(logical)}.json"
        if not manual_mode():
            _require_owner(entry, path, "clear completed")
        try:
            path.unlink()
        except FileNotFoundError:
            continue
        except OSError as exc:
            raise ResumeError(f"cannot clear completed call {logical!r}: {exc}") from exc


def complete_prefix(prefix: tuple[str, ...]) -> None:
    for entry in active_entries():
        logical = tuple(str(part) for part in entry["logical"])
        if logical[: len(prefix)] == prefix:
            complete_turn(logical, allow_previous_owner=True)


def has_prefix(prefix: tuple[str, ...]) -> bool:
    return any(tuple(str(part) for part in entry["logical"])[: len(prefix)] == prefix for entry in active_entries())
