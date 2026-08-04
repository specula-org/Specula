"""Lightweight, per-target resource summaries for full pipeline runs.

The tracker records target-active wall time, adapter usage sidecars, and
configured concurrency/TLC limits. Its JSON state and launcher manifests are
internal checkpoints; ``summary.md`` is the only user-facing output. Missing or
partial data never blocks the pipeline.
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
INVOCATION_DIRNAME = ".resource-summary-invocations"
RESOURCE_MANIFEST_ENV = "SPECULA_RESOURCE_MANIFEST"
RESOURCE_ROOT_ENV = "SPECULA_RESOURCE_ROOT"
RESOURCE_PHASE_ENV = "SPECULA_RESOURCE_PHASE"

_INVOCATION_ID_RE = re.compile(r"^[0-9a-f]{32}$")


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
_TURN_ATTEMPT_RE = re.compile(r"^turn[0-9]{2}_(?:A|B|A-repair)\.usage\.attempt-[1-9][0-9]*\.json$")
_ATTEMPT_SUFFIX_RE = re.compile(r"^(?P<stem>.+\.usage)\.attempt-[1-9][0-9]*\.json$")


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


@dataclass
class TargetState:
    target: str
    run_complete: bool = False
    history_incomplete: bool = False
    active_phase: str | None = None
    active_segment_id: str | None = None
    phases: dict[str, PhaseState] = field(default_factory=lambda: {phase.key: PhaseState() for phase in PHASES})
    source_signatures: dict[str, dict[str, str]] = field(default_factory=lambda: {phase.key: {} for phase in PHASES})
    attempt_signatures: dict[str, dict[str, str]] = field(default_factory=lambda: {phase.key: {} for phase in PHASES})
    invocation_signatures: dict[str, str] = field(default_factory=dict)
    sessions: dict[str, SessionState] = field(default_factory=dict)
    maximum_parallelism: str = "-"
    tlc_memory_limit: str = "-"
    tlc_worker_limit: str = "-"

    def to_object(self) -> dict[str, object]:
        active: dict[str, object] | None = None
        if self.active_phase is not None:
            active = {"phase": self.active_phase, "segment_id": self.active_segment_id}
        return {
            "version": 1,
            "target": self.target,
            "run_complete": self.run_complete,
            "history_incomplete": self.history_incomplete,
            "active_runtime": active,
            "phases": {key: phase.to_object() for key, phase in self.phases.items()},
            "source_signatures": self.source_signatures,
            "attempt_signatures": self.attempt_signatures,
            "invocation_signatures": self.invocation_signatures,
            "sessions": {key: session.to_object() for key, session in self.sessions.items()},
            "configuration": {
                "maximum_parallelism": self.maximum_parallelism,
                "tlc_memory_limit": self.tlc_memory_limit,
                "tlc_worker_limit": self.tlc_worker_limit,
            },
        }

    @classmethod
    def from_object(cls, value: object, expected_target: str) -> TargetState | None:
        data = _string_mapping(value)
        if data is None or data.get("version") != 1 or data.get("target") != expected_target:
            return None
        source_signatures = _signature_mapping(data.get("source_signatures"), attempts=False)
        attempt_signatures = _signature_mapping(data.get("attempt_signatures"), attempts=True)
        invocation_signatures = _invocation_signature_mapping(data.get("invocation_signatures", {}))
        if source_signatures is None or attempt_signatures is None or invocation_signatures is None:
            return None
        phases_data = _string_mapping(data.get("phases")) or {}
        phases = {phase.key: PhaseState.from_object(phases_data.get(phase.key)) for phase in PHASES}
        active_data = _string_mapping(data.get("active_runtime"))
        active_phase = _optional_string(active_data.get("phase")) if active_data is not None else None
        if active_phase not in PHASE_BY_KEY:
            active_phase = None
        configuration = _string_mapping(data.get("configuration")) or {}
        return cls(
            target=expected_target,
            run_complete=data.get("run_complete") is True,
            history_incomplete=data.get("history_incomplete") is True,
            active_phase=active_phase,
            active_segment_id=(_optional_string(active_data.get("segment_id")) if active_data is not None else None),
            phases=phases,
            source_signatures=source_signatures,
            attempt_signatures=attempt_signatures,
            invocation_signatures=invocation_signatures,
            sessions=_session_mapping(data.get("sessions")),
            maximum_parallelism=_optional_string(configuration.get("maximum_parallelism")) or "-",
            tlc_memory_limit=_optional_string(configuration.get("tlc_memory_limit")) or "-",
            tlc_worker_limit=_optional_string(configuration.get("tlc_worker_limit")) or "-",
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
    """Write one private launcher manifest for target-local accounting."""

    def __init__(self, root: Path, path: Path, phase: str, invocation_id: str) -> None:
        self._root = Path(os.path.abspath(root))
        self._path = Path(os.path.abspath(path))
        expected_path = self._root / INVOCATION_DIRNAME / f"{invocation_id}.json"
        if (
            phase not in PHASE_BY_KEY
            or _INVOCATION_ID_RE.fullmatch(invocation_id) is None
            or self._path != expected_path
        ):
            raise ValueError("resource manifest path does not match its invocation")
        self._phase = phase
        self._invocation_id = invocation_id
        self._lock = threading.Lock()
        self._started: dict[str, float] = {}
        self._document: dict[str, object] = {
            "version": 1,
            "invocation_id": invocation_id,
            "phase": phase,
            "complete": False,
            "targets": {},
        }
        _prepare_work_dir(self._root, self._path.parent)
        self._publish()

    @classmethod
    def from_environment(cls) -> ResourceInvocationRecorder | None:
        raw_root = os.environ.get(RESOURCE_ROOT_ENV)
        raw_path = os.environ.get(RESOURCE_MANIFEST_ENV)
        phase = os.environ.get(RESOURCE_PHASE_ENV)
        if raw_root is None or raw_path is None or phase not in PHASE_BY_KEY:
            return None
        path = Path(raw_path)
        invocation_id = path.stem
        if not path.is_absolute() or _INVOCATION_ID_RE.fullmatch(invocation_id) is None:
            return None
        try:
            return cls(Path(raw_root), path, phase, invocation_id)
        except (OSError, UnicodeError, ValueError):
            return None

    def start_target(self, name: str, work_dir: Path) -> None:
        with self._lock:
            if name in self._started:
                return
            relative = _relative_path(self._root, Path(os.path.abspath(work_dir)))
            targets = self._targets()
            existing = targets.get(name)
            if existing is not None:
                raise ValueError(f"resource target started twice with conflicting state: {name}")
            targets[name] = {
                "work_dir": relative,
                "finished": False,
                "elapsed_seconds": None,
                "succeeded": None,
                "usage_paths": [],
            }
            self._started[name] = time.monotonic()
            self._publish()

    def reuse_target(self, name: str, work_dir: Path) -> None:
        """Record a target already completed by an earlier invocation."""
        with self._lock:
            targets = self._targets()
            if name in self._started or name in targets:
                raise ValueError(f"resource target reused with conflicting state: {name}")
            targets[name] = {
                "work_dir": _relative_path(self._root, Path(os.path.abspath(work_dir))),
                "finished": True,
                "elapsed_seconds": 0.0,
                "succeeded": True,
                "usage_paths": [],
            }
            self._publish()

    def note_agent(self, work_dir: Path, usage_path: Path) -> None:
        absolute_work_dir = Path(os.path.abspath(work_dir))
        absolute_usage = Path(os.path.abspath(usage_path))
        with self._lock:
            targets = self._targets()
            for name, raw in targets.items():
                target = _string_mapping(raw)
                if target is None:
                    continue
                relative_work_dir = _optional_string(target.get("work_dir"))
                if relative_work_dir is None:
                    continue
                expected_work_dir = _checkpoint_path(self._root, relative_work_dir)
                if expected_work_dir != absolute_work_dir:
                    continue
                usage_relative = _relative_path(expected_work_dir, absolute_usage)
                paths = target.get("usage_paths")
                if not isinstance(paths, list):
                    raise ValueError(f"invalid resource usage list for {name}")
                paths.append(usage_relative)
                return

    def finish_target(self, name: str, succeeded: bool) -> None:
        with self._lock:
            started_at = self._started.pop(name, None)
            target = _string_mapping(self._targets().get(name))
            if started_at is None or target is None:
                return
            target["finished"] = True
            target["elapsed_seconds"] = max(0.0, time.monotonic() - started_at)
            target["succeeded"] = succeeded
            self._targets()[name] = target
            self._publish()

    def fail_target(self, name: str) -> None:
        with self._lock:
            target = _string_mapping(self._targets().get(name))
            if target is None:
                return
            target["succeeded"] = False
            self._targets()[name] = target
            self._publish()

    def finalize(self, succeeded: bool, *, outcomes_complete: bool = True) -> None:
        with self._lock:
            now = time.monotonic()
            for name, started_at in list(self._started.items()):
                target = _string_mapping(self._targets().get(name))
                if target is None:
                    continue
                target["finished"] = True
                target["elapsed_seconds"] = max(0.0, now - started_at)
                target["succeeded"] = False
                self._targets()[name] = target
            self._started.clear()
            if not outcomes_complete:
                for name, raw in list(self._targets().items()):
                    target = _string_mapping(raw)
                    if target is not None and target.get("succeeded") is True:
                        target["succeeded"] = False
                        self._targets()[name] = target
            self._document["complete"] = True
            self._document["succeeded"] = succeeded
            self._publish()

    def _targets(self) -> dict[str, object]:
        targets = self._document["targets"]
        if not isinstance(targets, dict):
            raise ValueError("invalid resource manifest target mapping")
        return targets

    def _publish(self) -> None:
        content = json.dumps(self._document, indent=2, sort_keys=True) + "\n"
        _atomic_write(self._root, self._path, content)


class ResourceSummaryTracker:
    """Maintain resource checkpoints and summaries for a pipeline's targets."""

    def __init__(
        self,
        targets: Mapping[str, Path],
        output_root: Path,
        maximum_parallelism: str,
        tlc_memory_limit: str,
        tlc_worker_limit: str,
    ) -> None:
        self._targets = {name: Path(os.path.abspath(path)) for name, path in targets.items()}
        self._output_root = Path(os.path.abspath(output_root))
        self._maximum_parallelism = maximum_parallelism
        self._tlc_memory_limit = tlc_memory_limit
        self._tlc_worker_limit = tlc_worker_limit
        self._states: dict[str, TargetState] = {}

    def initialize(self, resume: bool) -> None:
        """Create fresh state, or restore an existing run without guessing gaps."""
        invalid_invocations = self._invalid_invocation_scope() if resume else {}
        for name, work_dir in self._targets.items():
            try:
                _prepare_work_dir(self._output_root, work_dir)
                state = self._load_state(name, work_dir) if resume else None
                if state is None:
                    prior_evidence = resume and self._has_prior_resource_evidence(name, work_dir)
                    state = TargetState(
                        target=name,
                        history_incomplete=prior_evidence,
                    )
                    if prior_evidence:
                        for phase in PHASES:
                            self._capture_target_usage(work_dir, state, phase.key)
                    else:
                        self._baseline_sources(work_dir, state)
                    self._baseline_invocations(name, work_dir, state)
                else:
                    if state.active_phase is not None:
                        state.phases[state.active_phase].runtime_incomplete = True
                        state.phases[state.active_phase].usage_incomplete = True
                        state.history_incomplete = True
                        state.active_phase = None
                        state.active_segment_id = None
                    trusted_rewrites = self._pending_trusted_rewrites(name, work_dir, state)
                    changed_by_phase = {
                        phase.key: self._capture_target_usage(
                            work_dir,
                            state,
                            phase.key,
                            trusted_rewrites=trusted_rewrites[phase.key],
                        )
                        for phase in PHASES
                    }
                    unexplained = {phase: set(paths) for phase, paths in changed_by_phase.items()}
                    self._capture_pending_invocations(name, work_dir, state, changed_by_phase, unexplained)
                    if any(unexplained.values()):
                        state.history_incomplete = True
                if invalid_invocations is None:
                    state.history_incomplete = True
                else:
                    for phase_key in invalid_invocations.get(name, set()):
                        state.phases[phase_key].runtime_incomplete = True
                        state.phases[phase_key].usage_incomplete = True
                        state.history_incomplete = True
                state.run_complete = False
                state.maximum_parallelism = self._maximum_parallelism
                state.tlc_memory_limit = self._tlc_memory_limit
                state.tlc_worker_limit = self._tlc_worker_limit
                self._states[name] = state
                self._publish(name)
            except (OSError, UnicodeError, ValueError) as exc:
                self._warn(name, str(exc))

    def start_phase(self, phase: str, names: Iterable[str]) -> None:
        """Durably mark a grouped phase active before it can consume resources."""
        if not self._valid_phase(phase):
            return
        segment_id = secrets.token_hex(16)
        for name in self._selected(names):
            state = self._states[name]
            if state.active_phase is not None:
                state.phases[state.active_phase].runtime_incomplete = True
                state.phases[state.active_phase].usage_incomplete = True
                state.history_incomplete = True
            state.active_phase = phase
            state.active_segment_id = segment_id
            state.run_complete = False
            self._publish(name)

    def capture_usage(self, phase: str, names: Iterable[str], *, require_change: bool = False) -> None:
        """Capture canonical usage files changed since the preceding capture."""
        if not self._valid_phase(phase):
            return
        for name in self._selected(names):
            work_dir = self._targets[name]
            state = self._states[name]
            try:
                changed = self._capture_target_usage(work_dir, state, phase)
                if require_change and not changed:
                    state.phases[phase].usage_incomplete = True
                self._publish(name)
            except (OSError, UnicodeError, ValueError) as exc:
                state.phases[phase].usage_incomplete = True
                self._warn(name, str(exc))
                self._publish(name)

    def capture_invocation(
        self,
        phase: str,
        names: Iterable[str],
        invocation_id: str,
        *,
        launcher_succeeded: bool,
    ) -> None:
        """Capture one launcher manifest without charging sibling targets."""
        if not self._valid_phase(phase) or _INVOCATION_ID_RE.fullmatch(invocation_id) is None:
            return
        selected = self._selected(names)
        manifest = self._load_invocation(invocation_id)
        for name in selected:
            work_dir = self._targets[name]
            state = self._states[name]
            try:
                target = self._manifest_target(manifest, phase, name, work_dir)
                expected: set[str] = set()
                repeated = False
                if target is not None:
                    expected, repeated = _manifest_usage_paths(phase, target)
                changed = self._capture_target_usage(
                    work_dir,
                    state,
                    phase,
                    trusted_rewrites=expected if not repeated else set(),
                )
                if manifest is None:
                    state.phases[phase].runtime_incomplete = True
                    state.phases[phase].usage_incomplete = True
                    self._publish(name)
                    continue
                if target is None:
                    if launcher_succeeded or changed:
                        state.phases[phase].runtime_incomplete = True
                        state.phases[phase].usage_incomplete = True
                    self._publish(name)
                    continue
                self._account_invocation_target(
                    state,
                    phase,
                    invocation_id,
                    target,
                    changed,
                )
                self._publish(name)
            except (OSError, UnicodeError, ValueError) as exc:
                state.phases[phase].runtime_incomplete = True
                state.phases[phase].usage_incomplete = True
                self._warn(name, str(exc))
                self._publish(name)

    def finish_phase(
        self,
        phase: str,
        names: Iterable[str],
        elapsed_seconds: float,
        succeeded: bool,
    ) -> None:
        """Add a known wall-time segment and clear its durable active marker."""
        if not self._valid_phase(phase):
            return
        elapsed = _nonnegative_float(elapsed_seconds)
        for name in self._selected(names):
            state = self._states[name]
            phase_state = state.phases[phase]
            if state.active_phase != phase:
                phase_state.runtime_incomplete = True
                state.history_incomplete = True
            if elapsed is None:
                phase_state.runtime_incomplete = True
                state.history_incomplete = True
            else:
                phase_state.runtime_seconds = math.fsum((phase_state.runtime_seconds, elapsed))
                phase_state.runtime_observed = True
            if not phase_state.tokens_observed or not phase_state.cost_observed:
                phase_state.usage_incomplete = True
            state.active_phase = None
            state.active_segment_id = None
            if not succeeded:
                phase_state.usage_incomplete = True
                state.run_complete = False
            self._publish(name)

    def skip_phase(self, phase: str, names: Iterable[str]) -> None:
        """Refresh a skipped phase without manufacturing zero-valued usage."""
        if not self._valid_phase(phase):
            return
        for name in self._selected(names):
            state = self._states[name]
            if state.active_phase == phase:
                state.phases[phase].runtime_incomplete = True
                state.phases[phase].usage_incomplete = True
                state.history_incomplete = True
                state.active_phase = None
                state.active_segment_id = None
            self._publish(name)

    def complete_run(self) -> None:
        """Mark normal pipeline completion; metric gaps remain visibly partial."""
        for name in self._states:
            state = self._states[name]
            if state.active_phase is not None:
                state.phases[state.active_phase].runtime_incomplete = True
                state.phases[state.active_phase].usage_incomplete = True
                state.history_incomplete = True
                state.active_phase = None
                state.active_segment_id = None
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

    def _baseline_sources(self, work_dir: Path, state: TargetState) -> None:
        for phase in PHASES:
            sources = self._canonical_sources(work_dir, phase.key, state)
            attempts = self._attempt_sources(work_dir, phase.key, state)
            state.source_signatures[phase.key] = _existing_signatures(work_dir, sources)
            state.attempt_signatures[phase.key] = _existing_signatures(work_dir, attempts)

    def _baseline_invocations(self, name: str, work_dir: Path, state: TargetState) -> None:
        for invocation_id, manifest in self._invocation_manifests():
            phase = manifest["phase"]
            assert isinstance(phase, str)
            try:
                target = self._manifest_target(manifest, None, name, work_dir)
            except ValueError:
                state.history_incomplete = True
                continue
            if target is not None:
                state.invocation_signatures[invocation_id] = _invocation_target_signature(phase, target)

    def _pending_trusted_rewrites(
        self,
        name: str,
        work_dir: Path,
        state: TargetState,
    ) -> dict[str, set[str]]:
        claims: dict[str, dict[str, int]] = {phase.key: {} for phase in PHASES}
        for invocation_id, manifest in self._invocation_manifests():
            if invocation_id in state.invocation_signatures:
                continue
            phase = manifest["phase"]
            assert isinstance(phase, str)
            try:
                target = self._manifest_target(manifest, phase, name, work_dir)
                if target is None:
                    continue
                expected, repeated = _manifest_usage_paths(phase, target)
                for relative in expected:
                    increment = 2 if repeated else 1
                    claims[phase][relative] = claims[phase].get(relative, 0) + increment
            except ValueError:
                continue
        return {phase: {relative for relative, count in paths.items() if count == 1} for phase, paths in claims.items()}

    def _capture_pending_invocations(
        self,
        name: str,
        work_dir: Path,
        state: TargetState,
        changed_by_phase: dict[str, set[str]],
        unexplained: dict[str, set[str]],
    ) -> None:
        claimed_paths: dict[str, set[str]] = {phase.key: set() for phase in PHASES}
        seen_invocations: set[str] = set()
        for invocation_id, manifest in self._invocation_manifests():
            phase = manifest.get("phase")
            if not isinstance(phase, str) or phase not in PHASE_BY_KEY:
                continue
            try:
                target = self._manifest_target(manifest, phase, name, work_dir)
                if target is not None:
                    seen_invocations.add(invocation_id)
                    expected, repeated = _manifest_usage_paths(phase, target)
                    if invocation_id in state.invocation_signatures:
                        self._account_invocation_target(
                            state,
                            phase,
                            invocation_id,
                            target,
                            changed_by_phase[phase],
                        )
                        continue
                    ambiguous = bool(expected & claimed_paths[phase])
                    if ambiguous:
                        state.history_incomplete = True
                    self._account_invocation_target(
                        state,
                        phase,
                        invocation_id,
                        target,
                        changed_by_phase[phase],
                        usage_ambiguous=ambiguous,
                    )
                    if not repeated and not ambiguous and expected.issubset(changed_by_phase[phase]):
                        unexplained[phase].difference_update(expected)
                    claimed_paths[phase].update(expected)
            except ValueError:
                state.phases[phase].runtime_incomplete = True
                state.phases[phase].usage_incomplete = True
                state.history_incomplete = True
        if set(state.invocation_signatures) - seen_invocations:
            state.history_incomplete = True

    def _has_prior_resource_evidence(self, name: str, work_dir: Path) -> bool:
        for filename in (STATE_FILENAME, SUMMARY_FILENAME):
            try:
                (work_dir / filename).lstat()
            except FileNotFoundError:
                continue
            except OSError:
                return True
            else:
                return True
        probe = TargetState(target="baseline")
        if any(
            _file_signature(work_dir, path) is not None
            for phase in PHASES
            for path in (
                *self._canonical_sources(work_dir, phase.key, probe),
                *self._attempt_sources(work_dir, phase.key, probe),
            )
        ):
            return True
        for _, manifest in self._invocation_manifests():
            try:
                if self._manifest_target(manifest, None, name, work_dir) is not None:
                    return True
            except ValueError:
                return True
        return False

    def _capture_target_usage(
        self,
        work_dir: Path,
        state: TargetState,
        phase: str,
        *,
        trusted_rewrites: set[str] | None = None,
    ) -> set[str]:
        changed: set[str] = set()
        known_sources = state.source_signatures.setdefault(phase, {})
        source_paths = {
            _relative_path(work_dir, path): path for path in self._canonical_sources(work_dir, phase, state)
        }
        for relative in known_sources:
            source_paths.setdefault(relative, _checkpoint_path(work_dir, relative))
        for relative, path in source_paths.items():
            signature = _file_signature(work_dir, path)
            previous = known_sources.get(relative, "missing")
            if signature is None:
                known_sources[relative] = "missing"
                continue
            if signature == previous:
                continue
            known_sources[relative] = signature
            changed.add(relative)
            record = _parse_usage_file(work_dir, path)
            if record is None:
                state.phases[phase].usage_incomplete = True
                continue
            self._accumulate_record(
                state,
                phase,
                relative,
                rewritten=previous != "missing",
                trusted_rewrite=relative in (trusted_rewrites or set()),
                record=record,
            )

        known_attempts = state.attempt_signatures.setdefault(phase, {})
        attempt_paths = {_relative_path(work_dir, path): path for path in self._attempt_sources(work_dir, phase, state)}
        for relative in known_attempts:
            attempt_paths.setdefault(relative, _checkpoint_path(work_dir, relative))
        for relative, path in attempt_paths.items():
            signature = _file_signature(work_dir, path)
            previous = known_attempts.get(relative, "missing")
            if signature is None:
                known_attempts[relative] = "missing"
                continue
            if signature != previous:
                known_attempts[relative] = signature
                state.phases[phase].usage_incomplete = True
                changed.add(relative)
        return changed

    def _load_invocation(self, invocation_id: str, *, allow_incomplete: bool = False) -> dict[str, object] | None:
        path = self._output_root / INVOCATION_DIRNAME / f"{invocation_id}.json"
        try:
            raw = _read_safe_file(self._output_root, path)
            document: object = json.loads(raw)
        except (OSError, UnicodeError, json.JSONDecodeError):
            return None
        manifest = _string_mapping(document)
        if manifest is None:
            return None
        if (
            manifest.get("version") != 1
            or manifest.get("invocation_id") != invocation_id
            or manifest.get("phase") not in PHASE_BY_KEY
            or not isinstance(manifest.get("targets"), dict)
            or (
                not allow_incomplete
                and (manifest.get("complete") is not True or not isinstance(manifest.get("succeeded"), bool))
            )
        ):
            return None
        return manifest

    def _invalid_invocation_scope(self) -> dict[str, set[str]] | None:
        directory = self._output_root / INVOCATION_DIRNAME
        try:
            directory.lstat()
        except FileNotFoundError:
            return {}
        except OSError:
            return None
        if not _safe_directory(self._output_root, directory):
            return None
        try:
            entries = list(directory.iterdir())
        except OSError:
            return None
        affected: dict[str, set[str]] = {}
        for path in entries:
            match = re.fullmatch(r"([0-9a-f]{32})\.json", path.name)
            if match is None:
                continue
            invocation_id = match.group(1)
            manifest = self._load_invocation(invocation_id, allow_incomplete=True)
            if manifest is None:
                return None
            if manifest.get("complete") is True and isinstance(manifest.get("succeeded"), bool):
                continue
            phase = manifest["phase"]
            targets = manifest["targets"]
            assert isinstance(phase, str)
            assert isinstance(targets, dict)
            for name in targets:
                affected.setdefault(str(name), set()).add(phase)
        return affected

    def _invocation_manifests(self) -> list[tuple[str, dict[str, object]]]:
        directory = self._output_root / INVOCATION_DIRNAME
        if not _safe_directory(self._output_root, directory):
            return []
        manifests: list[tuple[str, dict[str, object]]] = []
        try:
            entries = sorted(directory.iterdir(), key=lambda path: path.name)
        except OSError:
            return []
        for path in entries:
            match = re.fullmatch(r"([0-9a-f]{32})\.json", path.name)
            if match is None:
                continue
            invocation_id = match.group(1)
            manifest = self._load_invocation(invocation_id)
            if manifest is not None:
                manifests.append((invocation_id, manifest))
        return manifests

    def _manifest_target(
        self,
        manifest: dict[str, object] | None,
        phase: str | None,
        name: str,
        work_dir: Path,
    ) -> dict[str, object] | None:
        if manifest is None or (phase is not None and manifest.get("phase") != phase):
            return None
        targets = _string_mapping(manifest.get("targets"))
        if targets is None or name not in targets:
            return None
        target = _string_mapping(targets[name])
        if target is None:
            raise ValueError(f"resource manifest has an invalid target record for {name}")
        relative_work_dir = _optional_string(target.get("work_dir"))
        if relative_work_dir is None:
            raise ValueError(f"resource manifest has no work directory for {name}")
        if _checkpoint_path(self._output_root, relative_work_dir) != Path(os.path.abspath(work_dir)):
            raise ValueError(f"resource manifest work directory does not match {name}")
        return target

    def _account_invocation_target(
        self,
        state: TargetState,
        phase: str,
        invocation_id: str,
        target: dict[str, object],
        changed: set[str],
        *,
        usage_ambiguous: bool = False,
    ) -> None:
        signature = _invocation_target_signature(phase, target)
        previous = state.invocation_signatures.get(invocation_id)
        if previous is not None:
            if previous != signature:
                state.phases[phase].runtime_incomplete = True
                state.phases[phase].usage_incomplete = True
                state.history_incomplete = True
            return

        expected, repeated = _manifest_usage_paths(phase, target)

        phase_state = state.phases[phase]
        finished = target.get("finished") is True
        elapsed = _nonnegative_float(target.get("elapsed_seconds"))
        succeeded = target.get("succeeded") is True
        if finished and elapsed is not None:
            phase_state.runtime_seconds = math.fsum((phase_state.runtime_seconds, elapsed))
            phase_state.runtime_observed = True
        else:
            phase_state.runtime_incomplete = True
            state.history_incomplete = True
        if not succeeded:
            phase_state.usage_incomplete = True
        if repeated or usage_ambiguous or not expected.issubset(changed):
            phase_state.usage_incomplete = True
        if succeeded and not expected and not phase_state.usage_incomplete:
            phase_state.tokens_observed = True
            phase_state.cost_observed = True
        state.invocation_signatures[invocation_id] = signature

    @staticmethod
    def _accumulate_record(
        state: TargetState,
        phase: str,
        relative: str,
        *,
        rewritten: bool,
        trusted_rewrite: bool = False,
        record: UsageRecord,
    ) -> None:
        phase_state = state.phases[phase]
        if not record.complete:
            phase_state.usage_incomplete = True

        cumulative_codex = record.agent == "codex" and record.session_id is not None
        if not cumulative_codex:
            if rewritten and not trusted_rewrite:
                phase_state.usage_incomplete = True
            if record.total_tokens is not None and record.cached_input_tokens is not None:
                phase_state.total_tokens += record.total_tokens
                phase_state.cached_input_tokens += record.cached_input_tokens
                phase_state.tokens_observed = True
            if record.cost_usd is not None:
                phase_state.cost_usd = math.fsum((phase_state.cost_usd, record.cost_usd))
                phase_state.cost_observed = True
            return

        identity_seed = f"{phase}\0{relative}\0{record.agent}\0{record.session_id}"
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

    def _canonical_sources(self, work_dir: Path, phase: str, state: TargetState) -> list[Path]:
        definition = PHASE_BY_KEY[phase]
        paths = [work_dir / relative for relative in definition.static_sources]
        if phase == "phase4a":
            paths.extend(_confirmation_files(work_dir, _TURN_USAGE_RE))
        for relative in state.source_signatures.get(phase, {}):
            candidate = _checkpoint_path(work_dir, relative)
            if candidate not in paths:
                paths.append(candidate)
        return paths

    def _attempt_sources(self, work_dir: Path, phase: str, state: TargetState) -> list[Path]:
        definition = PHASE_BY_KEY[phase]
        paths: list[Path] = []
        for relative in definition.static_sources:
            canonical = work_dir / relative
            parent = canonical.parent
            if _safe_directory(work_dir, parent):
                pattern = f"{canonical.stem}.attempt-*{canonical.suffix}"
                with suppress(OSError):
                    paths.extend(path for path in parent.glob(pattern) if _valid_attempt_for(canonical, path))
        if phase == "phase4a":
            paths.extend(_confirmation_files(work_dir, _TURN_ATTEMPT_RE))
        for relative in state.attempt_signatures.get(phase, {}):
            candidate = _checkpoint_path(work_dir, relative)
            if candidate not in paths:
                paths.append(candidate)
        return paths

    def _publish(self, name: str) -> None:
        state = self._states[name]
        work_dir = self._targets[name]
        try:
            state_content = json.dumps(state.to_object(), indent=2, sort_keys=True) + "\n"
            _atomic_write(work_dir, work_dir / STATE_FILENAME, state_content)
        except (OSError, UnicodeError, ValueError) as exc:
            self._warn(name, f"state write failed: {exc}")
        try:
            _atomic_write(work_dir, work_dir / SUMMARY_FILENAME, render_summary(state))
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


def render_summary(state: TargetState) -> str:
    """Render the intentionally small first-version summary."""
    lines = [
        "# Specula Summary",
        "",
        "## Resource Usage",
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
    incomplete = not state.run_complete or state.history_incomplete or state.active_phase is not None
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


def _valid_attempt_for(canonical: Path, candidate: Path) -> bool:
    match = _ATTEMPT_SUFFIX_RE.fullmatch(candidate.name)
    return match is not None and match.group("stem") == canonical.stem


def _existing_signatures(root: Path, paths: Iterable[Path]) -> dict[str, str]:
    found: dict[str, str] = {}
    for path in paths:
        signature = _file_signature(root, path)
        if signature is not None:
            found[_relative_path(root, path)] = signature
    return found


def _file_signature(root: Path, path: Path) -> str | None:
    if not _safe_regular_file(root, path):
        return None
    try:
        metadata = path.stat(follow_symlinks=False)
        content = _read_safe_file(root, path).encode("utf-8", errors="surrogatepass")
    except (OSError, UnicodeError):
        return None
    digest = hashlib.sha256(content).hexdigest()
    return f"{metadata.st_mtime_ns}:{metadata.st_size}:{digest}"


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


def _signature_mapping(value: object, *, attempts: bool) -> dict[str, dict[str, str]] | None:
    outer = _string_mapping(value)
    if outer is None:
        return None
    result: dict[str, dict[str, str]] = {phase.key: {} for phase in PHASES}
    for phase in PHASES:
        inner = _string_mapping(outer.get(phase.key))
        if inner is None:
            return None
        allowed = _allowed_attempt_path if attempts else _allowed_usage_path
        if any(
            not _valid_checkpoint_relative(key) or not allowed(phase.key, key) or not isinstance(item, str)
            for key, item in inner.items()
        ):
            return None
        result[phase.key] = {key: item for key, item in inner.items() if isinstance(item, str)}
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


def _invocation_target_signature(phase: str, target: dict[str, object]) -> str:
    return _object_signature({"phase": phase, "target": target})


def _allowed_usage_path(phase: str, relative: str) -> bool:
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


def _allowed_attempt_path(phase: str, relative: str) -> bool:
    candidate = PurePosixPath(relative)
    for source in PHASE_BY_KEY[phase].static_sources:
        canonical = PurePosixPath(source)
        if candidate.parent == canonical.parent:
            match = _ATTEMPT_SUFFIX_RE.fullmatch(candidate.name)
            if match is not None and match.group("stem") == canonical.stem:
                return True
    parts = candidate.parts
    return (
        phase == "phase4a"
        and len(parts) == 3
        and parts[0] == "confirmation"
        and not parts[1].startswith(".")
        and _TURN_ATTEMPT_RE.fullmatch(parts[2]) is not None
    )


def _manifest_usage_paths(phase: str, target: dict[str, object]) -> tuple[set[str], bool]:
    usage_paths = target.get("usage_paths")
    if not isinstance(usage_paths, list) or any(not isinstance(item, str) for item in usage_paths):
        raise ValueError("resource manifest has an invalid usage path list")
    expected: set[str] = set()
    for item in usage_paths:
        assert isinstance(item, str)
        if not _valid_checkpoint_relative(item) or not _allowed_usage_path(phase, item):
            raise ValueError(f"resource manifest has an unsafe usage path: {item!r}")
        expected.add(item)
    return expected, len(expected) != len(usage_paths)


def _session_mapping(value: object) -> dict[str, SessionState]:
    data = _string_mapping(value) or {}
    return {key: SessionState.from_object(item) for key, item in data.items()}


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
