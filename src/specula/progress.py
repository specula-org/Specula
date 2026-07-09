"""Portable progress reporting for Specula agent processes."""

from __future__ import annotations

import contextlib
import json
import os
import re
import subprocess
import time
from dataclasses import dataclass
from pathlib import Path

_ESCAPE_RE = re.compile(r"\x1b(?:\][^\x07]*(?:\x07|\x1b\\)|\[[0-?]*[ -/]*[@-~])")
_CONTROL_RE = re.compile(r"[\x00-\x1f\x7f-\x9f]")
_SUMMARY_LIMIT = 180


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


def enabled() -> bool:
    return os.environ.get("SPECULA_PROGRESS", "").lower() not in {"0", "false", "no", "off"}


def file_stamp(path: Path) -> tuple[int, int] | None:
    with contextlib.suppress(OSError):
        stat = path.stat()
        if path.is_file():
            return stat.st_mtime_ns, stat.st_size
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


def _summary(text: str, limit: int = _SUMMARY_LIMIT) -> str:
    """One terminal-safe line from agent-controlled text."""
    text = _ESCAPE_RE.sub("", text)
    text = _CONTROL_RE.sub(" ", text)
    summary = " ".join(text.split())
    if len(summary) > limit:
        return summary[: limit - 3].rstrip() + "..."
    return summary


def _changes(
    before: dict[Path, tuple[int, int]], after: dict[Path, tuple[int, int]]
) -> list[tuple[str, Path]]:
    changes: list[tuple[str, Path]] = []
    for path in sorted(after, key=lambda p: p.as_posix()):
        if path not in before:
            changes.append(("created", path))
        elif before[path] != after[path]:
            changes.append(("updated", path))
    for path in sorted(before.keys() - after.keys(), key=lambda p: p.as_posix()):
        changes.append(("removed", path))
    return changes


def _describe_changes(changes: list[tuple[str, Path]]) -> str:
    if len(changes) == 1:
        action, path = changes[0]
        return f"{action} {path.as_posix()}"
    paths = ", ".join(path.as_posix() for _, path in changes[:3])
    more = f" (+{len(changes) - 3} more)" if len(changes) > 3 else ""
    return f"changed {len(changes)} files: {paths}{more}"


def _string_arg(arguments: object, *keys: str) -> str:
    if not isinstance(arguments, dict):
        return ""
    for key in keys:
        value = arguments.get(key)
        if isinstance(value, str) and value.strip():
            return value
    return ""


def _tool_summary(name: str, arguments: object) -> str:
    lowered = name.casefold()
    command = _string_arg(arguments, "command", "cmd")
    path = _string_arg(arguments, "file_path", "path")
    pattern = _string_arg(arguments, "pattern", "query")
    description = _string_arg(arguments, "description", "intent", "prompt")
    if lowered in {"bash", "shell", "powershell", "command_execution"} and command:
        command = command.removeprefix("/bin/bash -lc ").removeprefix("/bin/sh -lc ")
        if len(command) >= 2 and command[0] == command[-1] and command[0] in {'"', "'"}:
            command = command[1:-1]
        return f"running {_summary(command, 160)}"
    if lowered in {"read", "view", "read_file"} and path:
        return f"reading {_summary(path)}"
    if lowered in {"edit", "write", "write_file", "notebookedit"} and path:
        return f"editing {_summary(path)}"
    if lowered in {"grep", "glob", "search", "websearch", "web_search"} and pattern:
        return f"searching for {_summary(pattern)}"
    if lowered in {"task", "spawnagent", "spawn_agent"}:
        detail = f": {_summary(description)}" if description else ""
        return f"spawning subagent{detail}"
    if lowered in {"taskoutput", "wait"}:
        return "waiting for subagents"
    detail = f": {_summary(description)}" if description else ""
    return f"using {name}{detail}"


def _claude_events(record: object) -> list[str]:
    if not isinstance(record, dict) or record.get("type") != "assistant":
        return []
    message = record.get("message")
    content = message.get("content") if isinstance(message, dict) else None
    if not isinstance(content, list):
        return []
    events: list[str] = []
    for block in content:
        if not isinstance(block, dict):
            continue
        text = block.get("text")
        name = block.get("name")
        if block.get("type") == "text" and isinstance(text, str):
            events.append(_summary(text))
        elif block.get("type") == "tool_use" and isinstance(name, str):
            events.append(_tool_summary(name, block.get("input")))
    return events


def _copilot_events(record: object) -> list[str]:
    if not isinstance(record, dict):
        return []
    data = record.get("data")
    if not isinstance(data, dict):
        return []
    content = data.get("content")
    tool_name = data.get("toolName")
    if record.get("type") == "assistant.message" and isinstance(content, str):
        return [_summary(content)]
    if record.get("type") == "tool.execution_start" and isinstance(tool_name, str):
        if tool_name == "report_intent":
            return []
        return [_tool_summary(tool_name, data.get("arguments"))]
    return []


def _codex_events(record: object) -> list[str]:
    if not isinstance(record, dict) or record.get("type") not in {"item.started", "item.completed"}:
        return []
    item = record.get("item")
    if not isinstance(item, dict):
        return []
    item_type = item.get("type")
    if record.get("type") == "item.completed" and item_type == "agent_message":
        text = item.get("text")
        return [_summary(text)] if isinstance(text, str) else []
    if record.get("type") != "item.started" or not isinstance(item_type, str):
        return []
    if item_type == "command_execution":
        return [_tool_summary(item_type, {"command": item.get("command")})]
    if item_type in {"mcp_tool_call", "web_search"}:
        name = item.get("tool") or item_type
        return [_tool_summary(str(name), item.get("arguments"))]
    return []


def _parse_events(adapter_name: str, lines: list[str]) -> list[str]:
    parsers = {
        "claude-code": _claude_events,
        "codex": _codex_events,
        "copilot-cli": _copilot_events,
    }
    parser = parsers.get(adapter_name)
    if parser is None:
        return []
    events: list[str] = []
    for line in lines:
        try:
            record = json.loads(line)
        except (TypeError, ValueError):
            summary = _summary(line)
            if summary and any(
                term in summary.casefold() for term in ("error", "failed", "require", "invalid", "unknown")
            ):
                events.append(f"adapter error: {summary}")
            continue
        events.extend(parser(record))
    return events


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
    return _parse_events(agent.adapter_name, chunks)


def _report_output_state(agent: RunningAgent, now: float, printed_event: bool, config: ProgressConfig) -> None:
    if printed_event:
        agent.reported_output = True
        agent.reported_sustained_output = False
        agent.last_output_report_at = now
    elif not agent.reported_output:
        print(f"[{_ts()}] {agent.name}: agent output is active")
        agent.reported_output = True
        agent.last_output_report_at = now
    elif (
        not agent.reported_sustained_output
        and now - agent.last_output_report_at >= config.status_after_seconds
    ) or (
        agent.reported_sustained_output
        and now - agent.last_output_report_at >= config.status_repeat_seconds
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

        if activity_changed or log_changed or printed_event:
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
