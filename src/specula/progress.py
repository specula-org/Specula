"""Portable progress reporting for Specula agent processes."""

from __future__ import annotations

import contextlib
import os
import stat
import subprocess
import time
from dataclasses import dataclass
from pathlib import Path

from specula.adapters import event_stream


@dataclass(frozen=True)
class ProgressConfig:
    poll_seconds: float = 1.0
    change_report_seconds: float = 5.0
    status_after_seconds: float = 60.0
    status_repeat_seconds: float = 300.0
    quiet_after_seconds: float = 300.0
    quiet_repeat_seconds: float = 300.0


@dataclass
class RunningAgent:
    name: str
    proc: subprocess.Popen[bytes]
    work_dir: Path
    log: Path
    activity_log: Path
    ignored: set[Path]
    snapshot: dict[Path, tuple[int, int]]
    reported_snapshot: dict[Path, tuple[int, int]]
    last_observed_at: float
    log_stamp: tuple[int, int] | None
    activity_stamp: tuple[int, int] | None
    adapter_name: str
    last_change_report_at: float = 0.0
    last_status_report_at: float = 0.0
    last_quiet_report_at: float = 0.0
    last_output_report_at: float = 0.0
    reported_output: bool = False
    reported_sustained_output: bool = False
    activity_offset: int = 0
    activity_buffer: str = ""
    activity_started: bool = False
    last_event: str = ""
    target: str = ""
    attempt: int = 1


def enabled() -> bool:
    return os.environ.get("SPECULA_PROGRESS", "").lower() not in {"0", "false", "no", "off"}


def file_stamp(path: Path) -> tuple[int, int] | None:
    with contextlib.suppress(OSError):
        st = path.stat()  # one stat, not stat() + is_file(): this runs per file per poll
        if stat.S_ISREG(st.st_mode):
            return st.st_mtime_ns, st.st_size
    return None


def workspace_snapshot(work_dir: Path, ignored: set[Path]) -> dict[Path, tuple[int, int]]:
    """Observable deliverables in an agent workspace, keyed by relative path."""
    snapshot: dict[Path, tuple[int, int]] = {}
    if not work_dir.is_dir():
        return snapshot
    try:
        for path in work_dir.rglob("*"):
            with contextlib.suppress(OSError):
                rel = path.relative_to(work_dir)
                if rel in ignored or any(part.startswith(".") for part in rel.parts):
                    continue
                stamp = file_stamp(path)
                if stamp is not None:
                    snapshot[rel] = stamp
    except OSError:
        pass
    return snapshot


def _ts() -> str:
    return time.strftime("%H:%M:%S")


def _elapsed(seconds: float) -> str:
    total = max(0, int(seconds))
    hours, remainder = divmod(total, 3600)
    minutes, secs = divmod(remainder, 60)
    if hours:
        return f"{hours}h{minutes:02}m"
    if minutes:
        return f"{minutes}m{secs:02}s"
    return f"{secs}s"


def _changes(before: dict[Path, tuple[int, int]], after: dict[Path, tuple[int, int]]) -> list[tuple[str, Path]]:
    changes: list[tuple[str, Path]] = []
    for path in sorted(after, key=lambda p: p.as_posix()):
        if path not in before:
            changes.append(("created", path))
        elif before[path] != after[path]:
            changes.append(("updated", path))
    for path in sorted(before.keys() - after.keys(), key=lambda p: p.as_posix()):
        changes.append(("removed", path))
    return changes


def _safe_path(path: Path) -> str:
    """The agent picks these names, and they end up on the user's terminal —
    sanitize them exactly like every other agent-controlled string."""
    return event_stream.summary(path.as_posix(), 120)


def _describe_changes(changes: list[tuple[str, Path]]) -> str:
    if len(changes) == 1:
        action, path = changes[0]
        return f"{action} {_safe_path(path)}"
    paths = ", ".join(_safe_path(path) for _, path in changes[:3])
    more = f" (+{len(changes) - 3} more)" if len(changes) > 3 else ""
    return f"changed {len(changes)} files: {paths}{more}"


def _read_events(agent: RunningAgent, finished: bool) -> list[str]:
    try:
        size = agent.activity_log.stat().st_size
        if not agent.activity_started or size < agent.activity_offset:
            agent.activity_offset = 0
            agent.activity_buffer = ""
            agent.activity_started = True
        with agent.activity_log.open("rb") as stream:
            stream.seek(agent.activity_offset)
            data = stream.read()
        agent.activity_offset += len(data)
    except OSError:
        return []
    if not data and not (finished and agent.activity_buffer):
        return []

    chunks = (agent.activity_buffer + data.decode(errors="replace")).split("\n")
    agent.activity_buffer = chunks.pop()
    if finished and agent.activity_buffer:
        chunks.append(agent.activity_buffer)
        agent.activity_buffer = ""
    return event_stream.parse_events(agent.adapter_name, chunks)


def _report_output_state(agent: RunningAgent, now: float, printed_event: bool, config: ProgressConfig) -> None:
    if printed_event:
        agent.reported_output = True
        agent.reported_sustained_output = False
        agent.last_output_report_at = now
    elif not agent.reported_output:
        print(f"[{_ts()}] {agent.name}: agent output is active")
        agent.reported_output = True
        agent.last_output_report_at = now
    elif (not agent.reported_sustained_output and now - agent.last_output_report_at >= config.status_after_seconds) or (
        agent.reported_sustained_output and now - agent.last_output_report_at >= config.status_repeat_seconds
    ):
        print(f"[{_ts()}] {agent.name}: agent output is still active")
        agent.reported_sustained_output = True
        agent.last_output_report_at = now


def report(running: list[RunningAgent], config: ProgressConfig) -> None:
    now = time.monotonic()
    for agent in running:
        finished = agent.proc.poll() is not None
        snapshot = workspace_snapshot(agent.work_dir, agent.ignored)
        observed_changes = _changes(agent.snapshot, snapshot)
        agent.snapshot = snapshot

        activity_stamp = file_stamp(agent.activity_log)
        activity_changed = activity_stamp != agent.activity_stamp
        printed_event = False
        if activity_changed or (finished and agent.activity_buffer):
            agent.activity_stamp = activity_stamp
            agent.last_observed_at = now
            for event in _read_events(agent, finished):
                if not event or event == agent.last_event:
                    continue
                print(f"[{_ts()}] {agent.name}: {event}")
                agent.last_event = event
                printed_event = True

        log_stamp = file_stamp(agent.log)
        log_changed = log_stamp != agent.log_stamp
        if log_changed:
            agent.log_stamp = log_stamp
            agent.last_observed_at = now

        if not finished and (activity_changed or log_changed or printed_event):
            _report_output_state(agent, now, printed_event, config)
        if observed_changes:
            agent.last_observed_at = now

        reportable_changes = _changes(agent.reported_snapshot, snapshot)
        if reportable_changes and (
            not agent.last_change_report_at
            or now - agent.last_change_report_at >= config.change_report_seconds
            or finished
        ):
            print(f"[{_ts()}] {agent.name}: {_describe_changes(reportable_changes)}")
            agent.reported_snapshot = snapshot
            agent.last_change_report_at = now

        if not finished:
            quiet_for = now - agent.last_observed_at
            if quiet_for >= config.quiet_after_seconds:
                if not agent.last_quiet_report_at or now - agent.last_quiet_report_at >= config.quiet_repeat_seconds:
                    print(f"[{_ts()}] {agent.name}: quiet for {_elapsed(quiet_for)}; process is still alive")
                    agent.last_quiet_report_at = now
            elif quiet_for >= config.status_after_seconds:
                if not agent.last_status_report_at or now - agent.last_status_report_at >= config.status_repeat_seconds:
                    print(
                        f"[{_ts()}] {agent.name}: no observable activity for "
                        f"{_elapsed(quiet_for)}; process is still alive"
                    )
                    agent.last_status_report_at = now
