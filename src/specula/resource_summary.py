"""Per-target human summaries and lightweight resource accounting.

Each target owns its resource records and summary state. Completed records
contain immutable usage snapshots; interrupted records only mark that target as
incomplete. The final report embeds an agent-written findings fragment only
after the run completes. Missing or partial resource data never blocks the pipeline.
"""

from __future__ import annotations

import hashlib
import html
import json
import math
import os
import re
import secrets
import stat
import sys
import threading
import time
from collections.abc import Iterable, Mapping
from contextlib import suppress
from dataclasses import dataclass, field
from pathlib import Path, PurePosixPath, PureWindowsPath

STATE_FILENAME = ".resource-summary-state.json"
SUMMARY_FILENAME = "summary.md"
FINDINGS_SUMMARY_FILENAME = ".summary-findings.md"
INVOCATION_DIRNAME = ".resource-summary-invocations"
RESOURCE_INVOCATION_ENV = "SPECULA_RESOURCE_INVOCATION"
RESOURCE_ROOT_ENV = "SPECULA_RESOURCE_ROOT"
RESOURCE_PHASE_ENV = "SPECULA_RESOURCE_PHASE"

_INVOCATION_ID_RE = re.compile(r"^[0-9a-f]{32}$")
_USAGE_ATTEMPT_RE = re.compile(r"^(?P<stem>.+)\.attempt-(?P<attempt>[1-9][0-9]*)\.json$")
_LINK_MARKUP_RES = (
    re.compile(r"!?\[[^\]\n]+\]\([^\)\n]+\)"),
    re.compile(r"!?\[[^\]\n]+\]\[[^\]\n]*\]"),
    re.compile(r"(?m)^\s*\[[^\]\n]+\]:\s*\S+"),
    re.compile(r"(?i)<\s*(?:a|img)\b[^>]*(?:href|src)\s*="),
    re.compile(r"(?i)<[^<>\n]+\.(?:md|html?)(?:#[^<>\n]*)?>"),
)


@dataclass(frozen=True)
class PhaseDefinition:
    key: str
    label: str
    static_sources: tuple[str, ...]


PHASES = (
    PhaseDefinition("phase1", "Phase 1", ("agent.usage.json", "review-analysis.usage.json")),
    PhaseDefinition("phase2", "Phase 2", ("spec-gen.usage.json", "spec/review-specgen.usage.json")),
    PhaseDefinition("phase2_5", "Phase 2.5", ("harness-gen.usage.json",)),
    PhaseDefinition(
        "phase3",
        "Phase 3",
        ("spec-validation.usage.json", "spec/review-validation.usage.json"),
    ),
    PhaseDefinition(
        "phase4a",
        "Phase 4a",
        ("bug-confirmation.usage.json", "spec-repair.usage.json", "spec/.consolidate.usage.json"),
    ),
    PhaseDefinition("phase4b", "Phase 4b", ("bug-classification.usage.json",)),
)
PHASE_BY_KEY = {phase.key: phase for phase in PHASES}

_TURN_USAGE_RE = re.compile(r"^turn[0-9]{2}_(?:A|B|A-repair)\.usage\.json$")
_FINDING_ID_RE = re.compile(r"^[A-Za-z0-9._-]+$")
_IMPACT_FINDING_STATUSES = frozenset({"REPRODUCED", "MASKED", "ENV_LIMITED"})
_REPORT_STATUSES = (
    "PENDING REPAIR",
    "FALSE POSITIVE",
    "NEEDS MORE INFO",
    "ENV_LIMITED",
    "REPRODUCED",
    "INCOMPLETE",
    "DEFERRED",
    "DROPPED",
    "MASKED",
)
CLASSIFICATION_SKIPPED_LIMIT = "Final findings reporting was skipped."


@dataclass
class PhaseState:
    runtime_seconds: float = 0.0
    runtime_observed: bool = False
    runtime_incomplete: bool = False
    total_tokens: int = 0
    cached_input_tokens: int = 0
    tokens_observed: bool = False
    cost_usd: float = 0.0
    cost_observed: bool = False
    usage_incomplete: bool = False

    def to_object(self) -> dict[str, object]:
        return {
            "runtime_seconds": self.runtime_seconds,
            "runtime_observed": self.runtime_observed,
            "runtime_incomplete": self.runtime_incomplete,
            "total_tokens": self.total_tokens,
            "cached_input_tokens": self.cached_input_tokens,
            "tokens_observed": self.tokens_observed,
            "cost_usd": self.cost_usd,
            "cost_observed": self.cost_observed,
            "usage_incomplete": self.usage_incomplete,
        }

    @classmethod
    def from_object(cls, value: object) -> PhaseState:
        data = _string_mapping(value)
        if data is None:
            return cls(runtime_incomplete=True, usage_incomplete=True)
        runtime = _nonnegative_float(data.get("runtime_seconds"))
        tokens = _nonnegative_int(data.get("total_tokens"))
        cached = _nonnegative_int(data.get("cached_input_tokens"))
        cost = _nonnegative_float(data.get("cost_usd"))
        valid_tokens = tokens is not None and cached is not None and cached <= tokens
        return cls(
            runtime_seconds=runtime or 0.0,
            runtime_observed=data.get("runtime_observed") is True and runtime is not None,
            runtime_incomplete=data.get("runtime_incomplete") is True or runtime is None,
            total_tokens=tokens if valid_tokens and tokens is not None else 0,
            cached_input_tokens=cached if valid_tokens and cached is not None else 0,
            tokens_observed=data.get("tokens_observed") is True and valid_tokens,
            cost_usd=cost or 0.0,
            cost_observed=data.get("cost_observed") is True and cost is not None,
            usage_incomplete=data.get("usage_incomplete") is True or not valid_tokens or cost is None,
        )


@dataclass
class SessionState:
    total_tokens: int | None = None
    cached_input_tokens: int | None = None
    cost_usd: float | None = None

    def to_object(self) -> dict[str, object]:
        return {
            "total_tokens": self.total_tokens,
            "cached_input_tokens": self.cached_input_tokens,
            "cost_usd": self.cost_usd,
        }

    @classmethod
    def from_object(cls, value: object) -> SessionState:
        data = _string_mapping(value)
        if data is None:
            return cls()
        tokens = _optional_nonnegative_int(data.get("total_tokens"))
        cached = _optional_nonnegative_int(data.get("cached_input_tokens"))
        if tokens is not None and cached is not None and cached > tokens:
            tokens = None
            cached = None
        return cls(
            total_tokens=tokens,
            cached_input_tokens=cached,
            cost_usd=_optional_nonnegative_float(data.get("cost_usd")),
        )


@dataclass(frozen=True)
class RunDetails:
    """Small set of deterministic run metadata shown in the summary."""

    original_source_commit: str | None = None
    attempt_source_commit: str | None = None
    agent: str | None = None
    model: str | None = None
    reasoning_effort: str | None = None

    def to_object(self) -> dict[str, object]:
        return {
            "original_source_commit": self.original_source_commit,
            "attempt_source_commit": self.attempt_source_commit,
            "agent": self.agent,
            "model": self.model,
            "reasoning_effort": self.reasoning_effort,
        }

    @classmethod
    def from_object(cls, value: object) -> RunDetails:
        data = _string_mapping(value) or {}
        return cls(
            original_source_commit=_optional_string(data.get("original_source_commit")),
            attempt_source_commit=_optional_string(data.get("attempt_source_commit")),
            agent=_optional_string(data.get("agent")),
            model=_optional_string(data.get("model")),
            reasoning_effort=_optional_string(data.get("reasoning_effort")),
        )


@dataclass
class TargetState:
    target: str
    run_complete: bool = False
    history_incomplete: bool = False
    phases: dict[str, PhaseState] = field(default_factory=lambda: {phase.key: PhaseState() for phase in PHASES})
    invocation_signatures: dict[str, str] = field(default_factory=dict)
    sessions: dict[str, SessionState] = field(default_factory=dict)
    maximum_parallelism: str = "-"
    tlc_memory_limit: str = "-"
    tlc_worker_limit: str = "-"
    run_details: RunDetails = field(default_factory=RunDetails)
    validation_limits: tuple[str, ...] = ()
    findings_summary_enabled: bool = True

    def to_object(self) -> dict[str, object]:
        return {
            "version": 1,
            "target": self.target,
            "run_complete": self.run_complete,
            "history_incomplete": self.history_incomplete,
            "phases": {key: phase.to_object() for key, phase in self.phases.items()},
            "invocation_signatures": self.invocation_signatures,
            "sessions": {key: session.to_object() for key, session in self.sessions.items()},
            "configuration": {
                "maximum_parallelism": self.maximum_parallelism,
                "tlc_memory_limit": self.tlc_memory_limit,
                "tlc_worker_limit": self.tlc_worker_limit,
            },
            "run_details": self.run_details.to_object(),
            "validation_limits": list(self.validation_limits),
            "findings_summary_enabled": self.findings_summary_enabled,
        }

    @classmethod
    def from_object(cls, value: object, expected_target: str) -> TargetState | None:
        data = _string_mapping(value)
        if data is None or data.get("version") != 1 or data.get("target") != expected_target:
            return None
        invocation_signatures = _invocation_signature_mapping(data.get("invocation_signatures", {}))
        if invocation_signatures is None:
            return None
        phases_data = _string_mapping(data.get("phases")) or {}
        phases = {phase.key: PhaseState.from_object(phases_data.get(phase.key)) for phase in PHASES}
        configuration = _string_mapping(data.get("configuration")) or {}
        return cls(
            target=expected_target,
            run_complete=data.get("run_complete") is True,
            history_incomplete=data.get("history_incomplete") is True,
            phases=phases,
            invocation_signatures=invocation_signatures,
            sessions=_session_mapping(data.get("sessions")),
            maximum_parallelism=_optional_string(configuration.get("maximum_parallelism")) or "-",
            tlc_memory_limit=_optional_string(configuration.get("tlc_memory_limit")) or "-",
            tlc_worker_limit=_optional_string(configuration.get("tlc_worker_limit")) or "-",
            run_details=RunDetails.from_object(data.get("run_details")),
            validation_limits=_string_tuple(data.get("validation_limits")),
            findings_summary_enabled=data.get("findings_summary_enabled") is not False,
        )


@dataclass(frozen=True)
class UsageRecord:
    agent: str
    session_id: str | None
    total_tokens: int | None
    cached_input_tokens: int | None
    cost_usd: float | None
    complete: bool


class ResourceInvocationRecorder:
    """Write one active or completed record inside each started target."""

    def __init__(self, root: Path, phase: str, invocation_id: str) -> None:
        self._root = Path(os.path.abspath(root))
        if phase not in PHASE_BY_KEY or _INVOCATION_ID_RE.fullmatch(invocation_id) is None:
            raise ValueError("invalid resource invocation identity")
        self._phase = phase
        self._invocation_id = invocation_id
        self._lock = threading.Lock()
        self._started: dict[str, float] = {}
        self._elapsed: dict[str, float] = {}
        self._work_dirs: dict[str, Path] = {}
        self._usage_paths: dict[str, list[str]] = {}
        self._continued_usage: dict[str, set[str]] = {}
        self._usage_failed: set[str] = set()
        self._finished: set[str] = set()

    @classmethod
    def from_environment(cls) -> ResourceInvocationRecorder | None:
        raw_root = os.environ.get(RESOURCE_ROOT_ENV)
        invocation_id = os.environ.get(RESOURCE_INVOCATION_ENV)
        phase = os.environ.get(RESOURCE_PHASE_ENV)
        if (
            raw_root is None
            or invocation_id is None
            or phase not in PHASE_BY_KEY
            or _INVOCATION_ID_RE.fullmatch(invocation_id) is None
        ):
            return None
        try:
            return cls(Path(raw_root), phase, invocation_id)
        except (OSError, UnicodeError, ValueError):
            return None

    def start_target(self, name: str, work_dir: Path) -> None:
        with self._lock:
            absolute_work_dir = Path(os.path.abspath(work_dir))
            existing_work_dir = self._work_dirs.get(name)
            if existing_work_dir is not None and existing_work_dir != absolute_work_dir:
                raise ValueError(f"resource target started twice with conflicting state: {name}")
            if name in self._finished:
                return
            if name in self._started:
                return
            if existing_work_dir is None:
                _prepare_work_dir(self._root, absolute_work_dir)
                path = self._record_path(absolute_work_dir)
                _prepare_work_dir(absolute_work_dir, path.parent)
                self._work_dirs[name] = absolute_work_dir
                self._elapsed[name] = 0.0
                self._usage_paths[name] = []
                self._continued_usage[name] = set()
            self._started[name] = time.monotonic()
            self._publish(
                name,
                {
                    "version": 1,
                    "invocation_id": self._invocation_id,
                    "phase": self._phase,
                    "target": name,
                    "status": "active",
                },
            )

    def note_agent(
        self,
        work_dir: Path,
        usage_path: Path,
        *,
        attempt: int = 1,
        archived_usage_path: Path | None = None,
    ) -> None:
        if isinstance(attempt, bool) or not isinstance(attempt, int) or attempt < 1:
            raise ValueError("resource agent attempt must be a positive integer")
        absolute_work_dir = Path(os.path.abspath(work_dir))
        absolute_usage = Path(os.path.abspath(usage_path))
        absolute_archive = Path(os.path.abspath(archived_usage_path)) if archived_usage_path is not None else None
        with self._lock:
            for name, expected_work_dir in self._work_dirs.items():
                if name not in self._started or expected_work_dir != absolute_work_dir:
                    continue
                try:
                    usage_relative = _relative_path(expected_work_dir, absolute_usage)
                    if not _allowed_usage_path(self._phase, usage_relative):
                        raise ValueError(f"unexpected resource usage path: {usage_relative}")
                    previous_index = next(
                        (
                            index
                            for index in range(len(self._usage_paths[name]) - 1, -1, -1)
                            if self._usage_paths[name][index] == usage_relative
                        ),
                        None,
                    )
                    if attempt > 1 and previous_index is None:
                        logical_relative = _canonical_usage_path(self._phase, usage_relative)
                        assert logical_relative is not None
                        self._continued_usage[name].add(logical_relative)
                    if previous_index is not None:
                        expected_archive = absolute_usage.with_name(
                            f"{absolute_usage.stem}.attempt-{attempt - 1}{absolute_usage.suffix}"
                        )
                        if attempt > 1 and absolute_archive == expected_archive:
                            archive_relative = _relative_path(expected_work_dir, expected_archive)
                            if _canonical_usage_path(self._phase, archive_relative) == usage_relative:
                                self._usage_paths[name][previous_index] = archive_relative
                            else:
                                self._usage_failed.add(name)
                        else:
                            self._usage_failed.add(name)
                    _clear_stale_usage(expected_work_dir, absolute_usage)
                except (OSError, UnicodeError, ValueError):
                    self._usage_failed.add(name)
                    raise
                self._usage_paths[name].append(usage_relative)
                return
            raise ValueError(f"resource target is not active: {absolute_work_dir}")

    def pause_target(self, name: str) -> None:
        """Stop the current timing segment while a target waits to retry."""
        with self._lock:
            self._pause_target(name)

    def finish_target(self, name: str) -> None:
        with self._lock:
            work_dir = self._work_dirs.get(name)
            if work_dir is None or name in self._finished:
                return
            self._pause_target(name)
            snapshots, usage_complete = _snapshot_usage(
                work_dir,
                self._phase,
                self._usage_paths.get(name, []),
                self._continued_usage.get(name, set()),
            )
            usage_complete = usage_complete and name not in self._usage_failed
            document: dict[str, object] = {
                "version": 1,
                "invocation_id": self._invocation_id,
                "phase": self._phase,
                "target": name,
                "status": "completed",
                "elapsed_seconds": self._elapsed[name],
                "usage_complete": usage_complete,
                "usage": snapshots,
            }
            if self._continued_usage[name]:
                document["continued_usage"] = sorted(self._continued_usage[name])
            self._publish(name, document)
            self._finished.add(name)

    def _pause_target(self, name: str) -> None:
        started_at = self._started.pop(name, None)
        if started_at is None:
            return
        self._elapsed[name] = math.fsum((self._elapsed[name], max(0.0, time.monotonic() - started_at)))

    def _record_path(self, work_dir: Path) -> Path:
        return work_dir / INVOCATION_DIRNAME / f"{self._invocation_id}.json"

    def _publish(self, name: str, document: dict[str, object]) -> None:
        work_dir = self._work_dirs[name]
        content = json.dumps(document, indent=2, sort_keys=True) + "\n"
        _atomic_write(work_dir, self._record_path(work_dir), content)


class ResourceSummaryTracker:
    """Maintain resource checkpoints and summaries for a pipeline's targets."""

    def __init__(
        self,
        targets: Mapping[str, Path],
        output_root: Path,
        maximum_parallelism: str,
        tlc_memory_limit: str,
        tlc_worker_limit: str,
        run_details: RunDetails | Mapping[str, RunDetails] | None = None,
        validation_limits: Iterable[str] = (),
        findings_summary_enabled: bool = True,
    ) -> None:
        self._targets = {name: Path(os.path.abspath(path)) for name, path in targets.items()}
        self._output_root = Path(os.path.abspath(output_root))
        self._maximum_parallelism = maximum_parallelism
        self._tlc_memory_limit = tlc_memory_limit
        self._tlc_worker_limit = tlc_worker_limit
        if isinstance(run_details, Mapping):
            self._run_details = {name: run_details.get(name, RunDetails()) for name in self._targets}
        else:
            common_details = run_details or RunDetails()
            self._run_details = {name: common_details for name in self._targets}
        self._validation_limits = tuple(
            limit for limit in validation_limits if isinstance(limit, str) and limit.strip()
        )
        self._findings_summary_enabled = findings_summary_enabled
        self._states: dict[str, TargetState] = {}

    def initialize(self, resume: bool, *, restart_names: Iterable[str] = ()) -> None:
        """Create fresh state, or consume only durable target-local records."""
        restarted = set(restart_names)
        for name, work_dir in self._targets.items():
            try:
                _prepare_work_dir(self._output_root, work_dir)
                state = self._load_state(name, work_dir) if resume else None
                if state is None:
                    prior_evidence = resume and self._has_prior_resource_evidence(name, work_dir)
                    state = TargetState(target=name, history_incomplete=prior_evidence)
                    incoming = self._run_details[name]
                    state.run_details = RunDetails(
                        original_source_commit=(
                            incoming.original_source_commit
                            or (None if prior_evidence else incoming.attempt_source_commit)
                        ),
                        attempt_source_commit=incoming.attempt_source_commit,
                        agent=incoming.agent,
                        model=incoming.model,
                        reasoning_effort=incoming.reasoning_effort,
                    )
                if resume:
                    self._consume_pending_records(name, work_dir, state)
                if name in restarted:
                    state.run_complete = False
                    incoming = self._run_details[name]
                    state.run_details = RunDetails(
                        original_source_commit=(
                            state.run_details.original_source_commit or incoming.original_source_commit
                        ),
                        attempt_source_commit=incoming.attempt_source_commit,
                        agent=incoming.agent,
                        model=incoming.model,
                        reasoning_effort=incoming.reasoning_effort,
                    )
                elif resume and state.run_details == RunDetails():
                    incoming = self._run_details[name]
                    state.run_details = RunDetails(
                        original_source_commit=incoming.original_source_commit,
                        agent=incoming.agent,
                        model=incoming.model,
                        reasoning_effort=incoming.reasoning_effort,
                    )
                state.maximum_parallelism = self._maximum_parallelism
                state.tlc_memory_limit = self._tlc_memory_limit
                state.tlc_worker_limit = self._tlc_worker_limit
                state.validation_limits = self._validation_limits
                state.findings_summary_enabled = self._findings_summary_enabled
                self._states[name] = state
                self._publish(name)
            except (OSError, UnicodeError, ValueError) as exc:
                self._warn(name, str(exc))

    def capture_invocation(
        self,
        phase: str,
        names: Iterable[str],
        invocation_id: str,
    ) -> None:
        """Capture one completed local record without charging siblings."""
        if not self._valid_phase(phase) or _INVOCATION_ID_RE.fullmatch(invocation_id) is None:
            return
        for name in self._selected(names):
            work_dir = self._targets[name]
            state = self._states[name]
            try:
                record = self._load_invocation(name, work_dir, invocation_id)
                if record is None:
                    continue
                if record["phase"] != phase:
                    raise ValueError("resource record phase does not match its launcher")
                self._consume_record(state, invocation_id, record)
                self._publish(name)
            except (OSError, UnicodeError, ValueError) as exc:
                self._mark_incomplete(state, phase)
                self._warn(name, str(exc))
                self._publish(name)

    def complete_run(self, names: Iterable[str] | None = None) -> None:
        """Mark normal pipeline completion; metric gaps remain visibly partial."""
        selected = list(self._states) if names is None else self._selected(names)
        for name in selected:
            state = self._states[name]
            state.run_complete = True
            self._publish(name)

    def refresh(self) -> None:
        """Regenerate every user-facing summary from its in-memory state."""
        for name in self._states:
            self._publish(name)

    def _load_state(self, name: str, work_dir: Path) -> TargetState | None:
        path = work_dir / STATE_FILENAME
        if not path.exists():
            return None
        raw = _read_safe_file(work_dir, path)
        try:
            document: object = json.loads(raw)
        except json.JSONDecodeError:
            return None
        return TargetState.from_object(document, name)

    def _consume_pending_records(self, name: str, work_dir: Path, state: TargetState) -> None:
        records, invalid = self._invocation_records(name, work_dir)
        if invalid:
            state.history_incomplete = True
            state.run_complete = False
            self._warn(name, "one or more local resource records could not be read")
        for invocation_id, record in records:
            self._consume_record(state, invocation_id, record)

    def _invocation_records(
        self,
        name: str,
        work_dir: Path,
    ) -> tuple[list[tuple[str, dict[str, object]]], bool]:
        directory = work_dir / INVOCATION_DIRNAME
        try:
            directory.lstat()
        except FileNotFoundError:
            return [], False
        except OSError:
            return [], True
        if not _safe_directory(work_dir, directory):
            return [], True
        try:
            entries = sorted(directory.iterdir(), key=lambda path: path.name)
        except OSError:
            return [], True
        records: list[tuple[str, dict[str, object]]] = []
        invalid = False
        for path in entries:
            match = re.fullmatch(r"([0-9a-f]{32})\.json", path.name)
            if match is None:
                continue
            invocation_id = match.group(1)
            try:
                record = self._load_invocation(name, work_dir, invocation_id)
            except (OSError, UnicodeError, ValueError):
                invalid = True
                continue
            if record is not None:
                records.append((invocation_id, record))
        return records, invalid

    def _has_prior_resource_evidence(self, name: str, work_dir: Path) -> bool:
        del name
        for filename in (STATE_FILENAME, SUMMARY_FILENAME, INVOCATION_DIRNAME):
            try:
                (work_dir / filename).lstat()
            except FileNotFoundError:
                continue
            except OSError:
                return True
            else:
                return True
        if any(
            _safe_regular_file(work_dir, work_dir / relative) for phase in PHASES for relative in phase.static_sources
        ):
            return True
        return bool(_confirmation_files(work_dir, _TURN_USAGE_RE))

    def _load_invocation(
        self,
        name: str,
        work_dir: Path,
        invocation_id: str,
    ) -> dict[str, object] | None:
        path = work_dir / INVOCATION_DIRNAME / f"{invocation_id}.json"
        try:
            path.lstat()
        except FileNotFoundError:
            return None
        except OSError as exc:
            raise OSError(f"cannot inspect resource record: {path}") from exc
        try:
            document: object = json.loads(_read_safe_file(work_dir, path))
        except json.JSONDecodeError as exc:
            raise ValueError(f"invalid resource record JSON: {path}") from exc
        record = _resource_record(document, name, invocation_id)
        if record is None:
            raise ValueError(f"invalid resource record: {path}")
        return record

    def _consume_record(
        self,
        state: TargetState,
        invocation_id: str,
        record: dict[str, object],
    ) -> None:
        phase = record["phase"]
        assert isinstance(phase, str)
        signature = _object_signature(record)
        previous = state.invocation_signatures.get(invocation_id)
        if previous is not None:
            if previous != signature:
                self._mark_incomplete(state, phase)
                state.invocation_signatures[invocation_id] = signature
            return
        state.run_complete = False
        if record["status"] == "active":
            self._mark_incomplete(state, phase)
        else:
            self._account_completed_record(state, phase, record)
        state.invocation_signatures[invocation_id] = signature

    @staticmethod
    def _mark_incomplete(state: TargetState, phase: str) -> None:
        state.phases[phase].runtime_incomplete = True
        state.phases[phase].usage_incomplete = True
        state.history_incomplete = True
        state.run_complete = False

    def _account_completed_record(
        self,
        state: TargetState,
        phase: str,
        record: dict[str, object],
    ) -> None:
        phase_state = state.phases[phase]
        elapsed = _nonnegative_float(record.get("elapsed_seconds"))
        assert elapsed is not None
        phase_state.runtime_seconds = math.fsum((phase_state.runtime_seconds, elapsed))
        phase_state.runtime_observed = True
        usage = _record_usage(phase, record)
        assert usage is not None
        continued_usage = _record_continued_usage(phase, record)
        assert continued_usage is not None
        if record.get("usage_complete") is not True:
            phase_state.usage_incomplete = True
        usage, retry_complete = _select_retry_usage(phase, usage, continued_usage)
        if not retry_complete:
            phase_state.usage_incomplete = True
        for relative, snapshot in usage:
            self._accumulate_record(state, phase, relative, snapshot)
        if not usage and record.get("usage_complete") is True and retry_complete:
            phase_state.tokens_observed = True
            phase_state.cost_observed = True

    @staticmethod
    def _accumulate_record(
        state: TargetState,
        phase: str,
        relative: str,
        record: UsageRecord,
    ) -> None:
        phase_state = state.phases[phase]
        if not record.complete:
            phase_state.usage_incomplete = True

        cumulative_codex = record.agent == "codex" and record.session_id is not None
        if not cumulative_codex:
            if record.total_tokens is not None and record.cached_input_tokens is not None:
                phase_state.total_tokens += record.total_tokens
                phase_state.cached_input_tokens += record.cached_input_tokens
                phase_state.tokens_observed = True
            if record.cost_usd is not None:
                phase_state.cost_usd = math.fsum((phase_state.cost_usd, record.cost_usd))
                phase_state.cost_observed = True
            return

        logical_relative = _canonical_usage_path(phase, relative)
        assert logical_relative is not None
        identity_seed = f"{phase}\0{logical_relative}\0{record.agent}\0{record.session_id}"
        identity = hashlib.sha256(identity_seed.encode("utf-8", errors="replace")).hexdigest()
        previous = state.sessions.get(identity, SessionState())

        if record.total_tokens is not None and record.cached_input_tokens is not None:
            if previous.total_tokens is None and previous.cached_input_tokens is None:
                phase_state.total_tokens += record.total_tokens
                phase_state.cached_input_tokens += record.cached_input_tokens
                previous.total_tokens = record.total_tokens
                previous.cached_input_tokens = record.cached_input_tokens
            elif (
                previous.total_tokens is None
                or previous.cached_input_tokens is None
                or record.total_tokens < previous.total_tokens
                or record.cached_input_tokens < previous.cached_input_tokens
            ):
                phase_state.usage_incomplete = True
            else:
                phase_state.total_tokens += record.total_tokens - previous.total_tokens
                phase_state.cached_input_tokens += record.cached_input_tokens - previous.cached_input_tokens
                previous.total_tokens = record.total_tokens
                previous.cached_input_tokens = record.cached_input_tokens
            phase_state.tokens_observed = True

        if record.cost_usd is not None:
            if previous.cost_usd is None:
                phase_state.cost_usd = math.fsum((phase_state.cost_usd, record.cost_usd))
                previous.cost_usd = record.cost_usd
            elif record.cost_usd + 1e-12 < previous.cost_usd:
                phase_state.usage_incomplete = True
            else:
                phase_state.cost_usd = math.fsum((phase_state.cost_usd, record.cost_usd - previous.cost_usd))
                previous.cost_usd = record.cost_usd
            phase_state.cost_observed = True

        state.sessions[identity] = previous

    def _publish(self, name: str) -> None:
        state = self._states[name]
        work_dir = self._targets[name]
        try:
            state_content = json.dumps(state.to_object(), indent=2, sort_keys=True) + "\n"
            _atomic_write(work_dir, work_dir / STATE_FILENAME, state_content)
        except (OSError, UnicodeError, ValueError) as exc:
            self._warn(name, f"state write failed: {exc}")
        try:
            _atomic_write(
                work_dir,
                work_dir / SUMMARY_FILENAME,
                render_summary(
                    state,
                    work_dir=work_dir,
                ),
            )
        except (OSError, UnicodeError, ValueError) as exc:
            self._warn(name, f"summary write failed: {exc}")

    def _selected(self, names: Iterable[str]) -> list[str]:
        selected: list[str] = []
        for name in dict.fromkeys(names):
            if name not in self._states:
                self._warn(name, "target is not initialized")
                continue
            selected.append(name)
        return selected

    @staticmethod
    def _valid_phase(phase: str) -> bool:
        if phase in PHASE_BY_KEY:
            return True
        print(f"WARNING: resource summary: unknown phase {phase!r}", file=sys.stderr)
        return False

    @staticmethod
    def _warn(name: str, message: str) -> None:
        print(f"WARNING: resource summary for {name}: {message}", file=sys.stderr)


def invalidate_summary(work_dir: Path, output_root: Path) -> None:
    """Remove one human-facing summary before starting work that makes it stale."""
    root = Path(os.path.abspath(output_root))
    target = Path(os.path.abspath(work_dir))
    _prepare_work_dir(root, target)
    path = target / SUMMARY_FILENAME
    try:
        metadata = path.lstat()
    except FileNotFoundError:
        return
    if not (stat.S_ISREG(metadata.st_mode) or stat.S_ISLNK(metadata.st_mode)):
        raise OSError(f"resource summary destination is not removable: {path}")
    try:
        path.unlink()
    except FileNotFoundError:
        return
    except OSError as exc:
        raise OSError(f"cannot invalidate resource summary: {path}") from exc
    try:
        path.lstat()
    except FileNotFoundError:
        return
    raise OSError(f"resource summary remained after invalidation: {path}")


def publish_findings_summary(target_name: str, work_dir: Path, output_root: Path) -> None:
    """Rebuild one summary after standalone final reporting succeeds."""
    root = Path(os.path.abspath(output_root))
    target = Path(os.path.abspath(work_dir))
    invalidate_summary(target, root)
    state_path = target / STATE_FILENAME
    try:
        state_path.lstat()
    except FileNotFoundError:
        state = TargetState(target=target_name)
    else:
        document: object
        try:
            document = json.loads(_read_safe_file(target, state_path))
        except json.JSONDecodeError as exc:
            raise ValueError(f"invalid resource summary state: {state_path}") from exc
        loaded_state = TargetState.from_object(document, target_name)
        if loaded_state is None:
            raise ValueError(f"invalid resource summary state: {state_path}")
        state = loaded_state
    state.findings_summary_enabled = True
    state.validation_limits = tuple(limit for limit in state.validation_limits if limit != CLASSIFICATION_SKIPPED_LIMIT)
    _atomic_write(target, state_path, json.dumps(state.to_object(), indent=2, sort_keys=True) + "\n")
    _atomic_write(target, target / SUMMARY_FILENAME, render_summary(state, work_dir=target))


def render_summary(
    state: TargetState,
    *,
    work_dir: Path | None = None,
) -> str:
    """Render the target's human-facing entry point without inferring findings."""
    details = state.run_details
    limits = state.validation_limits
    findings = _findings_summary(state, work_dir, state.findings_summary_enabled)

    lines = [
        "# Specula Summary",
        "",
        "## Result",
        "",
        f"- Run status: **{'Complete' if state.run_complete else 'Incomplete'}**",
        "",
    ]
    if findings is None:
        lines += [
            "## Findings",
            "",
            "The findings summary is unavailable because final reporting did not complete.",
            "",
            "## Validation limits",
            "",
            "- The final findings summary is unavailable.",
        ]
    else:
        lines.append(findings)
    if limits:
        lines += ["", "## Run coverage", "", *[f"- {_markdown_text(limit)}" for limit in limits]]

    agent = _markdown_optional(details.agent)
    model = _markdown_optional(details.model)
    lines += [
        "",
        "## Run details",
        "",
        "| Item | Value |",
        "|---|---|",
        f"| Target | {_markdown_text(state.target)} |",
        f"| Original source commit | {_markdown_optional(details.original_source_commit)} |",
        f"| Current attempt source commit | {_markdown_optional(details.attempt_source_commit)} |",
        f"| Agent / model | {agent} / {model} |",
        f"| Reasoning effort | {_markdown_optional(details.reasoning_effort)} |",
        "",
        "## Detailed reports",
        "",
        *_report_links(work_dir),
        "",
        "## Resource usage",
        "",
        "| Phase | Runtime | Tokens | Estimated cost |",
        "|---|---:|---:|---:|",
    ]
    total_runtime = 0.0
    total_runtime_observed = False
    total_tokens = 0
    total_cached = 0
    total_tokens_observed = False
    total_cost = 0.0
    total_cost_observed = False
    incomplete = not state.run_complete or state.history_incomplete
    for definition in PHASES:
        phase = state.phases[definition.key]
        runtime_available = phase.runtime_observed and not phase.runtime_incomplete
        runtime = _format_runtime(phase.runtime_seconds) if runtime_available else "-"
        tokens = (
            f"{_format_count(phase.total_tokens)} total ({_format_count(phase.cached_input_tokens)} cached)"
            if phase.tokens_observed
            else "-"
        )
        cost = _format_cost(phase.cost_usd) if phase.cost_observed else "-"
        lines.append(f"| {definition.label} | {runtime} | {tokens} | {cost} |")
        if runtime_available:
            total_runtime = math.fsum((total_runtime, phase.runtime_seconds))
            total_runtime_observed = True
        if phase.tokens_observed:
            total_tokens += phase.total_tokens
            total_cached += phase.cached_input_tokens
            total_tokens_observed = True
        if phase.cost_observed:
            total_cost = math.fsum((total_cost, phase.cost_usd))
            total_cost_observed = True
        incomplete = incomplete or any(
            (
                not phase.runtime_observed,
                not phase.tokens_observed,
                not phase.cost_observed,
                phase.runtime_incomplete,
                phase.usage_incomplete,
            )
        )
    total_label = "**Total (incomplete)**" if incomplete else "**Total**"
    runtime_total = _format_runtime(total_runtime) if total_runtime_observed else "-"
    token_total = (
        f"{_format_count(total_tokens)} total ({_format_count(total_cached)} cached)" if total_tokens_observed else "-"
    )
    cost_total = _format_cost(total_cost) if total_cost_observed else "-"
    lines += [
        f"| {total_label} | {runtime_total} | {token_total} | {cost_total} |",
        "",
        f"- Configured maximum parallelism: {_markdown_text(state.maximum_parallelism)}",
        (
            f"- Configured TLC limits: {_markdown_text(state.tlc_memory_limit)} memory; "
            f"{_markdown_text(state.tlc_worker_limit)} workers"
        ),
        "",
    ]
    return "\n".join(lines)


def _findings_summary(state: TargetState, work_dir: Path | None, enabled: bool) -> str | None:
    if not state.run_complete or not enabled or work_dir is None:
        return None
    try:
        content = _read_safe_file(work_dir, work_dir / FINDINGS_SUMMARY_FILENAME)
        confirmed = _read_safe_file(work_dir, work_dir / "confirmed-bugs.md")
    except (OSError, UnicodeError):
        return None
    return content if content.strip() and findings_fragment_issue(content, confirmed) is None else None


def findings_fragment_issue(content: str, confirmed_bugs: str | None = None) -> str | None:
    """Return a small structural/display-contract violation, without interpreting findings."""
    findings = list(re.finditer(r"(?m)^## Findings\s*$", content))
    limits = list(re.finditer(r"(?m)^## Validation limits\s*$", content))
    if len(findings) != 1 or len(limits) != 1:
        return "must contain one Findings section and one Validation limits section"
    if not content[: findings[0].start()].strip() or limits[0].start() <= findings[0].start():
        return "must begin with a conclusion followed by Findings and Validation limits"
    findings_body = content[findings[0].end() : limits[0].start()]
    limits_body = content[limits[0].end() :]
    if not findings_body.strip() or not limits_body.strip():
        return "contains an empty Findings or Validation limits section"
    headings = re.findall(r"(?m)^#{1,6}\s+.+$", content)
    if headings != ["## Findings", "## Validation limits"]:
        return "contains an unexpected heading"
    if re.search(r"(?i)\b(?:https?://|www\.)", content) or any(pattern.search(content) for pattern in _LINK_MARKUP_RES):
        return "contains a URL or link markup"
    if confirmed_bugs is not None:
        expected = _confirmation_finding_statuses(confirmed_bugs)
        if expected is None:
            return "cannot parse finding IDs and statuses from confirmed-bugs.md"
        actual = _fragment_finding_statuses(content, findings[0].end(), limits[0].start())
        if actual is None:
            return "cannot parse finding IDs and statuses"
        if actual != expected:
            return "finding IDs or statuses do not match confirmed-bugs.md"
    return None


def _confirmation_finding_statuses(content: str) -> dict[str, str] | None:
    lines = content.splitlines()
    headers = [
        index
        for index, line in enumerate(lines)
        if line.strip() == "| Entry | Finding | Status | Counts as final bug? |"
    ]
    if len(headers) != 1 or headers[0] + 1 >= len(lines):
        return None
    separator = [cell.strip() for cell in lines[headers[0] + 1].strip().strip("|").split("|")]
    if len(separator) != 4 or any(re.fullmatch(r":?-{3,}:?", cell) is None for cell in separator):
        return None
    statuses: dict[str, str] = {}
    seen: set[str] = set()
    for line in lines[headers[0] + 2 :]:
        if not line.strip():
            break
        if not line.lstrip().startswith("|"):
            return None
        cells = [cell.strip() for cell in line.strip().strip("|").split("|")]
        if len(cells) != 4 or not cells[0].isdigit():
            return None
        finding_id = cells[1]
        if _FINDING_ID_RE.fullmatch(finding_id) is None or finding_id in {".", ".."} or finding_id in seen:
            return None
        seen.add(finding_id)
        status = next(
            (
                candidate
                for candidate in _REPORT_STATUSES
                if cells[2] == candidate or cells[2].startswith(f"{candidate} (")
            ),
            None,
        )
        if status is None:
            return None
        if status in _IMPACT_FINDING_STATUSES:
            statuses[finding_id] = status
    return statuses


def _fragment_finding_statuses(content: str, start: int, end: int) -> dict[str, str] | None:
    statuses: dict[str, str] = {}
    section = content[start:end]
    status_fields = len(re.findall(r"\bStatus\s*:", section))
    bullets = list(re.finditer(r"(?m)^[ ]{0,3}[-+*][ \t]+", section))
    for index, bullet in enumerate(bullets):
        stop = bullets[index + 1].start() if index + 1 < len(bullets) else len(section)
        block = section[bullet.end() : stop].strip()
        if not block.startswith("**"):
            if re.search(r"\bStatus\s*:", block):
                return None
            continue
        title_end = block.find("**", 2)
        if title_end < 0:
            return None
        title = block[2:title_end].strip()
        finding_match = re.match(
            r"^`?(?P<id>[A-Za-z0-9._-]+)`?(?=[\s—:])",
            title,
        )
        remainder = block[title_end + 2 :]
        status_match = re.match(
            r"\s*(?:—|-|:)?\s*Status\s*:\s*`?(REPRODUCED|MASKED|ENV_LIMITED)`?(?=[.\s]|$)",
            remainder,
            flags=re.DOTALL,
        )
        if status_match is None or finding_match is None:
            return None
        if re.search(r"\bStatus\s*:", remainder[status_match.end() :]):
            return None
        finding_id = finding_match.group("id")
        if finding_id in {".", ".."} or finding_id in statuses:
            return None
        statuses[finding_id] = status_match.group(1)
    return statuses if status_fields == len(statuses) else None


def _report_links(work_dir: Path | None) -> list[str]:
    reports = (
        ("Confirmation report", "confirmed-bugs.md"),
        ("Severity report", "bug-severity.md"),
    )
    lines: list[str] = []
    for label, filename in reports:
        if work_dir is not None and _safe_regular_file(work_dir, work_dir / filename):
            lines.append(f"- [{label}]({filename})")
        else:
            lines.append(f"- {label}: -")
    return lines


def _snapshot_usage(
    work_dir: Path,
    phase: str,
    usage_paths: list[str],
    continued_usage: set[str],
) -> tuple[list[dict[str, object]], bool]:
    parsed: list[tuple[str, UsageRecord]] = []
    unique = list(dict.fromkeys(usage_paths))
    complete = len(unique) == len(usage_paths)
    for relative in unique:
        if not _valid_checkpoint_relative(relative) or not _allowed_usage_path(phase, relative):
            complete = False
            continue
        record = _parse_usage_file(work_dir, _checkpoint_path(work_dir, relative))
        if record is None:
            complete = False
            continue
        parsed.append((relative, record))
        complete = complete and record.complete
    _, retry_complete = _select_retry_usage(phase, parsed, continued_usage)
    snapshots: list[dict[str, object]] = [
        {
            "path": relative,
            "agent": record.agent,
            "session_id": record.session_id,
            "total_tokens": record.total_tokens,
            "cached_input_tokens": record.cached_input_tokens,
            "cost_usd": record.cost_usd,
            "complete": record.complete,
        }
        for relative, record in parsed
    ]
    return snapshots, complete and retry_complete


def _select_retry_usage(
    phase: str,
    usage: list[tuple[str, UsageRecord]],
    continued_usage: set[str],
) -> tuple[list[tuple[str, UsageRecord]], bool]:
    """Keep retry snapshots only when their adapter semantics are known."""
    groups: dict[str, list[tuple[str, UsageRecord]]] = {}
    for relative, record in usage:
        logical_relative = _canonical_usage_path(phase, relative)
        assert logical_relative is not None
        groups.setdefault(logical_relative, []).append((relative, record))

    selected: set[str] = set()
    complete = continued_usage.issubset(groups)
    for logical_relative, snapshots in groups.items():
        continued = logical_relative in continued_usage
        retry = continued or any(relative != logical_relative for relative, _record in snapshots)
        agents = {record.agent for _relative, record in snapshots}
        # Claude reports each invocation separately. Codex snapshots are cumulative
        # within a session and are reduced to deltas by _accumulate_record.
        precise = agents == {"claude-code"} or (
            agents == {"codex"} and all(record.session_id is not None for _relative, record in snapshots)
        )
        if not retry or precise:
            selected.update(relative for relative, _record in snapshots)
            continue

        complete = False
        if continued:
            continue
        current = next((relative for relative, _record in snapshots if relative == logical_relative), None)
        if current is None:
            current = max(snapshots, key=lambda item: _usage_attempt(item[0]))[0]
        selected.add(current)

    return [(relative, record) for relative, record in usage if relative in selected], complete


def _resource_record(value: object, target: str, invocation_id: str) -> dict[str, object] | None:
    record = _string_mapping(value)
    if record is None:
        return None
    phase = _optional_string(record.get("phase"))
    status = record.get("status")
    if (
        record.get("version") != 1
        or record.get("invocation_id") != invocation_id
        or record.get("target") != target
        or phase not in PHASE_BY_KEY
        or status not in {"active", "completed"}
    ):
        return None
    if status == "active":
        return record
    if (
        _nonnegative_float(record.get("elapsed_seconds")) is None
        or not isinstance(record.get("usage_complete"), bool)
        or _record_usage(phase, record) is None
        or _record_continued_usage(phase, record) is None
    ):
        return None
    return record


def _record_usage(phase: str, record: dict[str, object]) -> list[tuple[str, UsageRecord]] | None:
    raw_usage = record.get("usage")
    if not isinstance(raw_usage, list):
        return None
    result: list[tuple[str, UsageRecord]] = []
    seen: set[str] = set()
    for value in raw_usage:
        snapshot = _usage_snapshot(phase, value)
        if snapshot is None or snapshot[0] in seen:
            return None
        seen.add(snapshot[0])
        result.append(snapshot)
    return result


def _record_continued_usage(phase: str, record: dict[str, object]) -> set[str] | None:
    raw_paths = record.get("continued_usage", [])
    if not isinstance(raw_paths, list):
        return None
    paths: set[str] = set()
    for value in raw_paths:
        if (
            not isinstance(value, str)
            or not _valid_checkpoint_relative(value)
            or _canonical_usage_path(phase, value) != value
            or value in paths
        ):
            return None
        paths.add(value)
    return paths


def _usage_snapshot(phase: str, value: object) -> tuple[str, UsageRecord] | None:
    data = _string_mapping(value)
    if data is None:
        return None
    relative = _optional_string(data.get("path"))
    agent = _optional_string(data.get("agent"))
    raw_session = data.get("session_id")
    session_id = _optional_string(raw_session)
    tokens = _optional_nonnegative_int(data.get("total_tokens"))
    cached = _optional_nonnegative_int(data.get("cached_input_tokens"))
    cost = _optional_nonnegative_float(data.get("cost_usd"))
    if (
        relative is None
        or not _valid_checkpoint_relative(relative)
        or not _allowed_usage_path(phase, relative)
        or agent is None
        or (raw_session is not None and session_id is None)
        or (tokens is None) != (cached is None)
        or (tokens is not None and cached is not None and cached > tokens)
        or not isinstance(data.get("complete"), bool)
    ):
        return None
    return (
        relative,
        UsageRecord(
            agent=agent,
            session_id=session_id,
            total_tokens=tokens,
            cached_input_tokens=cached,
            cost_usd=cost,
            complete=data["complete"] is True,
        ),
    )


def _parse_usage_file(root: Path, path: Path) -> UsageRecord | None:
    try:
        raw = _read_safe_file(root, path)
        document: object = json.loads(raw)
    except (OSError, UnicodeError, json.JSONDecodeError):
        return None
    payload = _string_mapping(document)
    if payload is None or payload.get("error") is not None:
        return None
    usage = _string_mapping(payload.get("usage"))
    if usage is not None and (
        _optional_string(payload.get("agent")) is not None or "total_tokens" in usage or "cached_input_tokens" in usage
    ):
        return _normalized_usage(payload, usage)
    return _claude_usage(payload)


def _normalized_usage(payload: dict[str, object], usage: dict[str, object]) -> UsageRecord:
    tokens = _nonnegative_int(usage.get("total_tokens"))
    cached = _nonnegative_int(usage.get("cached_input_tokens"))
    if tokens is None or cached is None or cached > tokens:
        tokens = None
        cached = None
    cost = _nonnegative_float(payload.get("total_cost_usd"))
    agent = _optional_string(payload.get("agent")) or "normalized"
    complete = tokens is not None and cached is not None and cost is not None
    if payload.get("usage_complete") is False:
        complete = False
    return UsageRecord(
        agent=agent,
        session_id=_optional_string(payload.get("session_id")),
        total_tokens=tokens,
        cached_input_tokens=cached,
        cost_usd=cost,
        complete=complete,
    )


def _claude_usage(payload: dict[str, object]) -> UsageRecord:
    tokens: tuple[int, int] | None = None
    model_usage = _string_mapping(payload.get("model_usage"))
    invalid_model_usage = False
    if model_usage:
        totals = [0, 0]
        valid = True
        for value in model_usage.values():
            model = _string_mapping(value)
            if model is None:
                valid = False
                break
            values = (
                _nonnegative_int(model.get("inputTokens")),
                _nonnegative_int(model.get("cacheCreationInputTokens")),
                _nonnegative_int(model.get("cacheReadInputTokens")),
                _nonnegative_int(model.get("outputTokens")),
            )
            if any(item is None for item in values):
                valid = False
                break
            input_tokens, cache_write, cached, output = values
            assert input_tokens is not None and cache_write is not None and cached is not None and output is not None
            totals[0] += input_tokens + cache_write + cached + output
            totals[1] += cached
        if valid:
            tokens = (totals[0], totals[1])
        else:
            invalid_model_usage = True
    if tokens is None:
        usage = _string_mapping(payload.get("usage"))
        if usage is not None:
            values = (
                _nonnegative_int(usage.get("input_tokens")),
                _nonnegative_int(usage.get("cache_creation_input_tokens")),
                _nonnegative_int(usage.get("cache_read_input_tokens")),
                _nonnegative_int(usage.get("output_tokens")),
            )
            if all(item is not None for item in values):
                input_tokens, cache_write, cached, output = values
                assert (
                    input_tokens is not None and cache_write is not None and cached is not None and output is not None
                )
                tokens = (input_tokens + cache_write + cached + output, cached)
    cost = _nonnegative_float(payload.get("total_cost_usd"))
    return UsageRecord(
        agent="claude-code",
        session_id=_optional_string(payload.get("session_id")),
        total_tokens=tokens[0] if tokens is not None else None,
        cached_input_tokens=tokens[1] if tokens is not None else None,
        cost_usd=cost,
        complete=tokens is not None and cost is not None and not invalid_model_usage,
    )


def _confirmation_files(work_dir: Path, pattern: re.Pattern[str]) -> list[Path]:
    root = work_dir / "confirmation"
    if not _safe_directory(work_dir, root):
        return []
    paths: list[Path] = []
    try:
        finding_dirs = sorted(root.iterdir(), key=lambda path: path.name)
    except OSError:
        return []
    for finding_dir in finding_dirs:
        if finding_dir.name.startswith(".") or not _safe_directory(work_dir, finding_dir):
            continue
        try:
            entries = sorted(finding_dir.iterdir(), key=lambda path: path.name)
        except OSError:
            continue
        paths.extend(path for path in entries if pattern.fullmatch(path.name) is not None)
    return paths


def _prepare_work_dir(output_root: Path, work_dir: Path) -> None:
    root = Path(os.path.abspath(output_root))
    destination = Path(os.path.abspath(work_dir))
    try:
        relative = destination.relative_to(root)
    except ValueError as exc:
        raise OSError(f"target output escapes its layout root: {work_dir}") from exc
    if root.is_symlink() or not root.is_dir():
        raise OSError(f"unsafe output root: {output_root}")
    current = root
    for part in relative.parts:
        current /= part
        try:
            metadata = current.lstat()
        except FileNotFoundError:
            try:
                current.mkdir()
            except FileExistsError:
                metadata = current.lstat()
            else:
                metadata = current.lstat()
        if stat.S_ISLNK(metadata.st_mode) or not stat.S_ISDIR(metadata.st_mode):
            raise OSError(f"unsafe target output directory: {work_dir}")


def _safe_directory(root: Path, path: Path) -> bool:
    try:
        relative = _safe_relative_path(root, path, allow_root=True)
    except ValueError:
        return False
    current = root
    try:
        if current.is_symlink() or not current.is_dir():
            return False
        for part in relative.parts:
            current /= part
            metadata = current.lstat()
            if stat.S_ISLNK(metadata.st_mode) or not stat.S_ISDIR(metadata.st_mode):
                return False
    except (FileNotFoundError, OSError, UnicodeError):
        return False
    return True


def _safe_regular_file(root: Path, path: Path) -> bool:
    try:
        relative = _safe_relative_path(root, path, allow_root=False)
    except ValueError:
        return False
    current = root
    try:
        if current.is_symlink() or not current.is_dir():
            return False
        for index, part in enumerate(relative.parts):
            current /= part
            metadata = current.lstat()
            if stat.S_ISLNK(metadata.st_mode):
                return False
            if index + 1 < len(relative.parts) and not stat.S_ISDIR(metadata.st_mode):
                return False
        return stat.S_ISREG(current.lstat().st_mode)
    except (FileNotFoundError, OSError, UnicodeError):
        return False


def _read_safe_file(root: Path, path: Path) -> str:
    if not _safe_regular_file(root, path):
        raise OSError(f"unsafe or missing file: {path}")
    flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0)
    descriptor = os.open(path, flags)
    try:
        with os.fdopen(descriptor, "r", encoding="utf-8", errors="strict") as stream:
            return stream.read()
    except BaseException:
        with suppress(OSError):
            os.close(descriptor)
        raise


def _clear_stale_usage(root: Path, path: Path) -> None:
    try:
        path.lstat()
    except FileNotFoundError:
        return
    if not _safe_directory(root, path.parent):
        raise OSError(f"unsafe resource usage directory: {path.parent}")
    try:
        path.unlink()
    except FileNotFoundError:
        pass
    except OSError as exc:
        raise OSError(f"cannot clear stale resource usage: {path}") from exc


def _atomic_write(root: Path, path: Path, content: str) -> None:
    if not _safe_directory(root, path.parent):
        raise OSError(f"unsafe resource summary destination: {path}")
    try:
        destination = path.lstat()
    except FileNotFoundError:
        destination = None
    if destination is not None and (stat.S_ISLNK(destination.st_mode) or not stat.S_ISREG(destination.st_mode)):
        raise OSError(f"resource summary destination is not a regular file: {path}")
    if _safe_regular_file(root, path):
        try:
            if _read_safe_file(root, path) == content:
                return
        except (OSError, UnicodeError):
            pass
    temporary = path.parent / f".{path.name}.{os.getpid()}.{secrets.token_hex(8)}.tmp"
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_NOFOLLOW", 0)
    descriptor = os.open(temporary, flags, 0o666)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8") as stream:
            stream.write(content)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
    finally:
        with suppress(FileNotFoundError):
            temporary.unlink()


def _relative_path(root: Path, path: Path) -> str:
    relative = _safe_relative_path(root, path, allow_root=False)
    return relative.as_posix()


def _safe_relative_path(root: Path, path: Path, *, allow_root: bool) -> Path:
    relative = path.relative_to(root)
    if not relative.parts:
        if allow_root:
            return relative
        raise ValueError("path must name an entry below the root")
    if any(part in {"", ".", ".."} for part in relative.parts):
        raise ValueError("path is not a canonical child of the root")
    return relative


def _checkpoint_path(root: Path, relative: str) -> Path:
    if not _valid_checkpoint_relative(relative):
        raise ValueError(f"unsafe checkpoint path: {relative!r}")
    return root.joinpath(*PurePosixPath(relative).parts)


def _valid_checkpoint_relative(value: str) -> bool:
    if not value or "\x00" in value or "\\" in value:
        return False
    posix = PurePosixPath(value)
    windows = PureWindowsPath(value)
    return (
        not posix.is_absolute()
        and not windows.is_absolute()
        and not windows.drive
        and bool(posix.parts)
        and posix.as_posix() == value
        and all(part not in {"", ".", ".."} for part in posix.parts)
    )


def _string_mapping(value: object) -> dict[str, object] | None:
    if not isinstance(value, dict):
        return None
    result: dict[str, object] = {}
    for key, item in value.items():
        if isinstance(key, str):
            result[key] = item
    return result


def _invocation_signature_mapping(value: object) -> dict[str, str] | None:
    data = _string_mapping(value)
    if data is None:
        return None
    if any(
        _INVOCATION_ID_RE.fullmatch(key) is None
        or not isinstance(item, str)
        or re.fullmatch(r"[0-9a-f]{64}", item) is None
        for key, item in data.items()
    ):
        return None
    return {key: item for key, item in data.items() if isinstance(item, str)}


def _object_signature(value: object) -> str:
    encoded = json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode()
    return hashlib.sha256(encoded).hexdigest()


def _canonical_usage_path(phase: str, relative: str) -> str | None:
    if _allowed_canonical_usage_path(phase, relative):
        return relative
    parts = PurePosixPath(relative).parts
    if not parts:
        return None
    match = _USAGE_ATTEMPT_RE.fullmatch(parts[-1])
    if match is None:
        return None
    canonical = PurePosixPath(*parts[:-1], f"{match.group('stem')}.json").as_posix()
    return canonical if _allowed_canonical_usage_path(phase, canonical) else None


def _usage_attempt(relative: str) -> int:
    match = _USAGE_ATTEMPT_RE.fullmatch(PurePosixPath(relative).name)
    return int(match.group("attempt")) if match is not None else 0


def _allowed_canonical_usage_path(phase: str, relative: str) -> bool:
    if relative in PHASE_BY_KEY[phase].static_sources:
        return True
    parts = PurePosixPath(relative).parts
    return (
        phase == "phase4a"
        and len(parts) == 3
        and parts[0] == "confirmation"
        and not parts[1].startswith(".")
        and _TURN_USAGE_RE.fullmatch(parts[2]) is not None
    )


def _allowed_usage_path(phase: str, relative: str) -> bool:
    return _canonical_usage_path(phase, relative) is not None


def _session_mapping(value: object) -> dict[str, SessionState]:
    data = _string_mapping(value) or {}
    return {key: SessionState.from_object(item) for key, item in data.items()}


def _string_tuple(value: object) -> tuple[str, ...]:
    if not isinstance(value, list):
        return ()
    return tuple(item for item in value if isinstance(item, str) and item.strip())


def _optional_string(value: object) -> str | None:
    return value if isinstance(value, str) and value else None


def _nonnegative_int(value: object) -> int | None:
    if isinstance(value, bool) or not isinstance(value, int) or value < 0:
        return None
    return value


def _optional_nonnegative_int(value: object) -> int | None:
    return None if value is None else _nonnegative_int(value)


def _nonnegative_float(value: object) -> float | None:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return None
    result = float(value)
    return result if result >= 0 and math.isfinite(result) else None


def _optional_nonnegative_float(value: object) -> float | None:
    return None if value is None else _nonnegative_float(value)


def _format_runtime(seconds: float) -> str:
    total = max(0, int(round(seconds)))
    hours, remainder = divmod(total, 3600)
    minutes, secs = divmod(remainder, 60)
    if hours:
        return f"{hours}h {minutes}m"
    if minutes:
        return f"{minutes}m {secs}s"
    return f"{secs}s"


def _format_count(value: int) -> str:
    if value >= 1_000_000_000:
        return f"{value / 1_000_000_000:.1f}B"
    if value >= 1_000_000:
        return f"{value / 1_000_000:.1f}M"
    if value >= 1_000:
        return f"{value / 1_000:.1f}K"
    return str(value)


def _format_cost(value: float) -> str:
    if 0 < value < 0.01:
        return f"${value:.4f}"
    return f"${value:.2f}"


def _markdown_text(value: str) -> str:
    one_line = " ".join(value.splitlines()).strip()
    return html.escape(one_line, quote=False).replace("\\", "\\\\").replace("|", "\\|") or "-"


def _markdown_optional(value: str | None) -> str:
    return _markdown_text(value) if value else "-"
