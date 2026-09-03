"""Parallel per-finding bug confirmation (Phase 4), with an optional debate.

The default Phase-4 mode: instead of one agent confirming every finding in one
context (the legacy single-agent path, still reachable via ``--legacy-confirm``),
this fans out one Reproducer agent per finding, in parallel. With debate enabled
(``--debate``), a confirmation is then stress-tested by an adversarial Challenger
to consensus. Roles, debate rules, and the verdict vocabulary follow the
bug-confirmation skill (``guide.md`` + the challenge/defend prompts); this module
is the dispatcher (the group-chat manager): it owns turn order, the shared
``debate.md``, the round cap, VERDICT comparison, serial RR-NNN allocation, and
aggregation into ``confirmed-bugs.md``.

Every agent turn goes through :func:`specula.phaselib.run_agent_blocking` — the
same adapter path, flags, and stop-gate env as ``Phase._launch``. A finding that
cannot finish — rate limit (adapter exit 75), infrastructure error, or malformed
output — never discards the whole target. It becomes an ``INCOMPLETE`` row in the
report (clearly marked, and NOT persisted as a business verdict — that failure is
never cached), and every *completed* finding is still delivered. This is partial
delivery over total loss: a single blip no longer withholds ``confirmed-bugs.md``.
A later retry skips findings whose fingerprinted terminal verdict and artifacts
are still valid and re-attempts only the INCOMPLETE ones. (Consolidate is the one
prerequisite that still withholds when it yields no candidates: there is simply
nothing to deliver.)
"""

from __future__ import annotations

import contextlib
import hashlib
import json
import os
import re
import secrets
import shutil
import subprocess
import threading
import traceback
from collections.abc import Callable
from concurrent.futures import FIRST_COMPLETED, Future, ThreadPoolExecutor, wait
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from specula import quota, resumelib
from specula.phaselib import (
    DEFAULT_POLICY_RETRIES,
    DEFAULT_TRANSIENT_RESUMES,
    SPECULA_ROOT,
    PolicyRetryState,
    Workspace,
    run_agent_blocking,
)
from specula.prompts import render
from specula.skill_refs import prompt_skill_ids
from specula.snapshotlib import SNAPSHOT_MODE_ENV, clean_git_environment

SKILLS = SPECULA_ROOT / "skills"
PHASE_KEY = "bug_confirmation"

# Framework terminal/loop statuses (skills/bug-confirmation/guide.md).
CANON = [
    "REPRODUCED",
    "ENV_LIMITED",
    "MASKED",
    "FALSE POSITIVE",
    "NEEDS MORE INFO",
    "DROPPED",
    "PENDING REPAIR",
]
# A verdict asserting a real defect — opens a debate so it is stress-tested.
CONFIRM = {"REPRODUCED", "ENV_LIMITED", "MASKED"}
# The "finding" tier: a real code defect that is NOT a confirmed live bug — either
# argued-but-unreproduced (ENV_LIMITED) or real-defect-whose-consequence-is
# currently-masked by a safeguard/downstream mechanism (MASKED). Surfaced
# separately from confirmed bugs (REPRODUCED), never dropped as FALSE POSITIVE.
FINDING = {"ENV_LIMITED", "MASKED"}
# Not a verdict: a finding whose confirmation could not finish (infra error, rate
# limit, malformed output). Recorded so the target still delivers, marked clearly,
# and NOT cached so a retry re-attempts it. Deliberately outside CANON.
INCOMPLETE = "INCOMPLETE"
VALID_SOURCES = {"model-checking", "code-review"}
ID_CHARS = set("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789._-")
_CACHE_VERSION = 3
_CANDIDATE_CACHE = ".candidates-cache.json"

_VERDICT_RE = re.compile(r"^\s*VERDICT:\s*(.+?)\s*$", re.MULTILINE)
_rr_lock = threading.RLock()
_print_lock = threading.Lock()
_log_file: Path | None = None  # when set, _log also tees here (the phase's bug-confirmation.log)


def _dispatcher_git_env(path: str | Path | None = None) -> dict[str, str] | None:
    """Use deterministic Git context for Specula-owned snapshot operations."""
    if not os.environ.get(SNAPSHOT_MODE_ENV):
        return None
    extra: dict[str, str] = {}
    if path is not None:
        ceiling = str(Path(path).resolve().parent)
        if os.pathsep in ceiling:
            raise RuntimeError("private dispatcher path cannot be represented in GIT_CEILING_DIRECTORIES")
        extra["GIT_CEILING_DIRECTORIES"] = ceiling
    return clean_git_environment(extra)


def _set_log_file(path: Path | None) -> None:
    global _log_file
    _log_file = path


class RateLimited(Exception):
    """A turn hit adapter exit 75 (rate limit). An internal control-flow signal:
    run_finding_safe catches it and marks that one finding INCOMPLETE (never a
    per-finding NEEDS MORE INFO, which is terminal and never revisited, and never
    cached — so a retry re-attempts it). It does not withhold the target; the
    completed findings still deliver."""


class ConsolidateFailed(Exception):
    """Consolidate ran (not rate-limited) but produced no valid candidates.json.
    The driver withholds the deliverable and returns a permanent nonzero status."""


class ConfirmationFailed(Exception):
    """Infrastructure or invalid-agent-output failure.

    Unlike a genuine ``NEEDS MORE INFO`` verdict, this is retryable and must not
    be persisted as a business conclusion.
    """


class InvalidAgentOutput(ConfirmationFailed):
    """An agent returned success but violated the dispatcher's stable contract."""


class InvalidRepairRequest(InvalidAgentOutput):
    """A PENDING REPAIR verdict did not include an executable repair request."""


def _log(msg: str) -> None:
    with _print_lock:
        print(msg, flush=True)
        if _log_file is not None:
            with _log_file.open("a") as fh:
                fh.write(msg + "\n")


def parse_verdict(text: str) -> str | None:
    """Last ``VERDICT:`` line, normalized to a canonical status (or None)."""
    matches = _VERDICT_RE.findall(text or "")
    if not matches:
        return None
    raw = matches[-1].strip().upper()
    raw = re.sub(r"\s*\(.*\)\s*$", "", raw)  # drop a trailing "(RR-001)" etc.
    raw = re.sub(r"\s+", " ", raw)
    return raw if raw in CANON else None


@dataclass
class Finding:
    data: dict[str, Any]
    fdir: Path  # per-finding work dir: <wd>/confirmation/<id>/
    # Repair mode continues the same finding evidence instead of starting from
    # an empty confirmation context. Runtime-only: never serialized or hashed.
    repair_context: str = ""

    @property
    def id(self) -> str:
        return str(self.data["id"])


@dataclass(frozen=True)
class _CompletedTurn:
    prompt_digest: str
    cwd: str | None
    verdict: str | None
    text: str
    result_path: Path | None = None
    result_digest: str = ""


@dataclass
class _RepairTurn:
    turn_no: int
    prompt: str
    original: str | None = None
    verdict: str | None = None
    disabled: bool = False


@dataclass
class _FindingLease:
    """Per-finding state retained until a terminal verdict is durably saved."""

    finding_dir: Path
    repo_for_agent: str
    cleanup: Callable[[], None]
    source_repo: str = ""
    state_path: Path | None = None
    initialized: bool = False
    repair_retry_used: bool = False
    completed_turns: dict[tuple[int, str], _CompletedTurn] = field(default_factory=dict)
    turn_cwds: dict[tuple[int, str], Path] = field(default_factory=dict)
    repair_turns: dict[tuple[int, str], _RepairTurn] = field(default_factory=dict)
    no_correction_drafts: dict[tuple[int, str], str] = field(default_factory=dict)
    _run_lock: Any = field(default_factory=threading.RLock, repr=False, compare=False)
    _closed: bool = False


_LEASE_VERSION = 2


def _lease_file(f: Finding) -> Path:
    return f.fdir / ".resume-lease.json"


def _lease_atomic_write(path: Path, value: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(f".{path.name}.{os.getpid()}.{threading.get_ident()}.{secrets.token_hex(4)}")
    try:
        tmp.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
        tmp.replace(path)
    finally:
        with contextlib.suppress(FileNotFoundError):
            tmp.unlink()


def _turn_result_file(cfg: ConfirmConfig, f: Finding, turn_no: int, role: str, text: str) -> Path:
    log = f.fdir / f"turn{turn_no:02d}_{role}.log"
    result = log.with_name(f"{log.stem}.last-message.txt") if cfg.adapter.stem == "codex" else log
    if result.is_file() and result.read_text(errors="replace") == text:
        return result
    # Unit embedders may replace the adapter primitive without creating its
    # normal result file. Keep one uniform durable result in that case.
    result = f.fdir / f"turn{turn_no:02d}_{role}.accepted.txt"
    result.write_text(text)
    return result


def _persist_lease(cfg: ConfirmConfig, f: Finding, lease: _FindingLease) -> None:
    if not resumelib.enabled():
        return
    completed: list[dict[str, Any]] = []
    for (turn_no, role), item in sorted(lease.completed_turns.items()):
        result_path = item.result_path or _turn_result_file(cfg, f, turn_no, role, item.text)
        try:
            relative = result_path.absolute().relative_to(f.fdir.absolute())
        except ValueError as exc:
            raise ConfirmationFailed(f"{f.id}: completed turn result escapes its finding directory") from exc
        body = result_path.read_bytes()
        digest = hashlib.sha256(body).hexdigest()
        completed.append(
            {
                "turn": turn_no,
                "role": role,
                "prompt_digest": item.prompt_digest,
                "cwd": item.cwd,
                "verdict": item.verdict,
                "result": relative.as_posix(),
                "result_digest": digest,
            }
        )
    repair_turns = [
        {
            "previous_turn": previous_turn,
            "previous_role": previous_role,
            "turn": item.turn_no,
            "prompt": item.prompt,
            "original": item.original,
            "verdict": item.verdict,
            "disabled": item.disabled,
        }
        for (previous_turn, previous_role), item in sorted(lease.repair_turns.items())
    ]
    path = _lease_file(f)
    value = {
        "version": _LEASE_VERSION,
        "finding_id": f.id,
        "fingerprint": _verdict_fingerprint(cfg, f),
        "source_repo": lease.source_repo or (str(Path(cfg.repo_dir).absolute()) if cfg.repo_dir else ""),
        "repo_for_agent": lease.repo_for_agent,
        "worktree": bool(cfg.worktree and cfg.repo_dir),
        "initialized": lease.initialized,
        "repair_retry_used": lease.repair_retry_used,
        "completed_turns": completed,
        "turn_cwds": [
            {"turn": turn, "role": role, "path": str(path.absolute())}
            for (turn, role), path in sorted(lease.turn_cwds.items())
        ],
        "repair_turns": repair_turns,
        "no_correction_drafts": [
            {
                "previous_turn": previous_turn,
                "previous_role": previous_role,
                "draft_digest": draft_digest,
            }
            for (previous_turn, previous_role), draft_digest in sorted(lease.no_correction_drafts.items())
        ],
    }
    _lease_atomic_write(path, value)
    lease.state_path = path


def _safe_retained_path(path: Path, root: Path, label: str) -> Path:
    if path.is_symlink():
        raise ConfirmationFailed(f"unsafe retained {label} symlink: {path}")
    try:
        path.resolve().relative_to(root.resolve())
    except (OSError, ValueError) as exc:
        raise ConfirmationFailed(f"retained {label} escapes {root}: {path}") from exc
    return path


def _load_lease(cfg: ConfirmConfig, f: Finding) -> _FindingLease:
    path = _lease_file(f)
    try:
        if path.is_symlink() or not path.is_file():
            raise ConfirmationFailed(f"{f.id}: missing safe Phase 4 resume checkpoint")
        value = json.loads(path.read_text())
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise ConfirmationFailed(f"{f.id}: cannot read Phase 4 resume checkpoint: {exc}") from exc
    if not isinstance(value, dict) or value.get("version") != _LEASE_VERSION or value.get("finding_id") != f.id:
        raise ConfirmationFailed(f"{f.id}: invalid Phase 4 resume checkpoint")
    fingerprint = value.get("fingerprint")
    if not isinstance(fingerprint, str) or fingerprint != _verdict_fingerprint(cfg, f):
        raise ConfirmationFailed(f"{f.id}: Phase 4 inputs changed; pass --fresh-context to start over")

    source_repo = value.get("source_repo")
    repo_for_agent = value.get("repo_for_agent")
    retained_worktree = value.get("worktree")
    initialized = value.get("initialized")
    repair_retry_used = value.get("repair_retry_used")
    if (
        not isinstance(source_repo, str)
        or not isinstance(repo_for_agent, str)
        or not isinstance(retained_worktree, bool)
        or not isinstance(initialized, bool)
        or not isinstance(repair_retry_used, bool)
    ):
        raise ConfirmationFailed(f"{f.id}: invalid Phase 4 resume checkpoint fields")
    current_source = str(Path(cfg.repo_dir).absolute()) if cfg.repo_dir else ""
    if source_repo != current_source:
        raise ConfirmationFailed(f"{f.id}: retained source repository no longer matches")
    if retained_worktree != bool(cfg.worktree and cfg.repo_dir):
        raise ConfirmationFailed(f"{f.id}: retained worktree mode no longer matches")
    if retained_worktree:
        repo_path = _safe_retained_path(Path(repo_for_agent), f.fdir.absolute(), "worktree")
        probe = subprocess.run(
            ["git", "-C", str(repo_path), "rev-parse", "--is-inside-work-tree"],
            env=_dispatcher_git_env(repo_path),
            capture_output=True,
            text=True,
        )
        if probe.returncode != 0 or probe.stdout.strip() != "true":
            raise ConfirmationFailed(f"{f.id}: retained worktree is unavailable")
        cleanup = _retained_worktree_cleanup(Path(source_repo), repo_path, f.id)
    else:
        if repo_for_agent != current_source:
            raise ConfirmationFailed(f"{f.id}: retained repository no longer matches")

        def cleanup() -> None:
            return None

    lease = _FindingLease(
        f.fdir.absolute(),
        repo_for_agent,
        cleanup,
        source_repo=source_repo,
        state_path=path,
    )
    lease.initialized = initialized
    lease.repair_retry_used = repair_retry_used
    raw_cwds = value.get("turn_cwds", [])
    raw_completed = value.get("completed_turns", [])
    raw_repairs = value.get("repair_turns", [])
    raw_no_corrections = value.get("no_correction_drafts")
    if (
        not isinstance(raw_cwds, list)
        or not isinstance(raw_completed, list)
        or not isinstance(raw_repairs, list)
        or not isinstance(raw_no_corrections, list)
    ):
        raise ConfirmationFailed(f"{f.id}: invalid Phase 4 resume checkpoint lists")
    for item in raw_cwds:
        if not isinstance(item, dict):
            raise ConfirmationFailed(f"{f.id}: invalid retained turn cwd")
        turn = item.get("turn")
        role = item.get("role")
        raw_path = item.get("path")
        if (
            not isinstance(turn, int)
            or isinstance(turn, bool)
            or turn < 1
            or role not in {"A", "B", "A-repair"}
            or not isinstance(raw_path, str)
            or not raw_path
        ):
            raise ConfirmationFailed(f"{f.id}: invalid retained turn cwd")
        if (turn, role) in lease.turn_cwds:
            raise ConfirmationFailed(f"{f.id}: duplicate retained turn cwd")
        cwd = _safe_retained_path(Path(raw_path), f.fdir / ".agent-cwd", "turn cwd")
        if not cwd.is_dir():
            raise ConfirmationFailed(f"{f.id}: retained turn cwd is unavailable: {cwd}")
        lease.turn_cwds[(turn, role)] = cwd
    for item in raw_completed:
        if not isinstance(item, dict):
            raise ConfirmationFailed(f"{f.id}: invalid completed turn checkpoint")
        turn = item.get("turn")
        role = item.get("role")
        result = item.get("result")
        digest = item.get("result_digest")
        prompt_digest = item.get("prompt_digest")
        raw_cwd = item.get("cwd")
        verdict = item.get("verdict")
        if (
            not isinstance(turn, int)
            or isinstance(turn, bool)
            or turn < 1
            or role not in {"A", "B", "A-repair"}
            or not isinstance(result, str)
            or not result
            or not isinstance(digest, str)
            or re.fullmatch(r"[0-9a-f]{64}", digest) is None
            or not isinstance(prompt_digest, str)
            or re.fullmatch(r"[0-9a-f]{64}", prompt_digest) is None
            or not isinstance(raw_cwd, str)
            or verdict not in CANON
        ):
            raise ConfirmationFailed(f"{f.id}: invalid completed turn checkpoint")
        key = (turn, role)
        if (
            key in lease.completed_turns
            or key not in lease.turn_cwds
            or str(lease.turn_cwds[key].absolute()) != raw_cwd
        ):
            raise ConfirmationFailed(f"{f.id}: completed turn checkpoint does not match its retained cwd")
        result_path = _safe_retained_path(f.fdir / result, f.fdir, "turn result")
        try:
            body = result_path.read_bytes()
        except OSError as exc:
            raise ConfirmationFailed(f"{f.id}: retained turn result is unavailable: {result_path}") from exc
        if hashlib.sha256(body).hexdigest() != digest:
            raise ConfirmationFailed(f"{f.id}: retained turn result changed: {result_path}")
        text = body.decode(errors="replace")
        lease.completed_turns[(turn, role)] = _CompletedTurn(
            prompt_digest,
            raw_cwd,
            verdict,
            text,
            result_path,
            digest,
        )
    for item in raw_no_corrections:
        if not isinstance(item, dict):
            raise ConfirmationFailed(f"{f.id}: invalid no-correction draft checkpoint")
        previous_turn = item.get("previous_turn")
        previous_role = item.get("previous_role")
        draft_digest = item.get("draft_digest")
        if (
            not isinstance(previous_turn, int)
            or isinstance(previous_turn, bool)
            or previous_turn < 1
            or previous_role not in {"A", "B"}
            or not isinstance(draft_digest, str)
            or re.fullmatch(r"[0-9a-f]{64}", draft_digest) is None
        ):
            raise ConfirmationFailed(f"{f.id}: invalid no-correction draft checkpoint")
        key = (previous_turn, previous_role)
        completed = lease.completed_turns.get(key)
        if key in lease.no_correction_drafts:
            raise ConfirmationFailed(f"{f.id}: duplicate no-correction draft checkpoint")
        if completed is None or completed.verdict != "PENDING REPAIR":
            raise ConfirmationFailed(
                f"{f.id}: no-correction draft checkpoint is not bound to a completed PENDING REPAIR turn"
            )
        lease.no_correction_drafts[key] = draft_digest
    for item in raw_repairs:
        if not isinstance(item, dict):
            raise ConfirmationFailed(f"{f.id}: invalid repair-turn checkpoint")
        previous_turn = item.get("previous_turn")
        previous_role = item.get("previous_role")
        turn = item.get("turn")
        prompt = item.get("prompt")
        original = item.get("original")
        verdict = item.get("verdict")
        disabled = item.get("disabled")
        if (
            not isinstance(previous_turn, int)
            or isinstance(previous_turn, bool)
            or previous_turn < 1
            or previous_role not in {"A", "B"}
            or not isinstance(turn, int)
            or isinstance(turn, bool)
            or turn < 1
            or not isinstance(prompt, str)
            or not prompt
            or (original is not None and not isinstance(original, str))
            or (verdict is not None and verdict not in CANON)
            or not isinstance(disabled, bool)
        ):
            raise ConfirmationFailed(f"{f.id}: invalid repair-turn checkpoint")
        repair_key = (previous_turn, previous_role)
        if repair_key in lease.repair_turns or repair_key in lease.no_correction_drafts:
            raise ConfirmationFailed(f"{f.id}: duplicate repair-turn checkpoint")
        lease.repair_turns[repair_key] = _RepairTurn(
            turn,
            prompt,
            original,
            verdict,
            disabled,
        )
    return lease


def _remove_lease_state(lease: _FindingLease) -> None:
    path = lease.state_path
    if path is not None:
        with contextlib.suppress(FileNotFoundError):
            path.unlink()


def _discard_persisted_lease(cfg: ConfirmConfig, f: Finding) -> None:
    path = _lease_file(f)
    if not path.exists() and not path.is_symlink():
        return
    try:
        lease = _load_lease(cfg, f)
        lease.cleanup()
    except Exception as exc:
        _log(f"  WARNING: {f.id}: could not clean stale resume lease ({exc})")
    finally:
        with contextlib.suppress(FileNotFoundError):
            path.unlink()


@dataclass
class ConfirmConfig:
    name: str
    ws: Workspace
    adapter: Path
    repo_dir: str = ""
    max_parallel: int = 4
    claude_alias: str = "claude"
    worktree: bool = True
    dry_run: bool = False
    prompt_extra: str = ""  # target's .prompt-extra.md, appended to every agent prompt
    resume_prompt_extra: str = ""  # latest guidance, manual continuation only
    # New controls stay after the original fields to preserve positional callers.
    # None = no Specula override; "" = explicit reset to the CLI default.
    model: str | None = None
    effort: str | None = None
    debate: bool = False
    rounds: int = 5
    max_turns: str = "0"
    policy_retries: int = DEFAULT_POLICY_RETRIES
    transient_resumes: int = DEFAULT_TRANSIENT_RESUMES
    # Internal repair-loop mode. The round scopes evidence/RR selection; the
    # durable token identifies the exact Phase-3 result for idempotent retries.
    # Initial Phase 4 leaves both unset and retains its existing behavior.
    repair_round: int | None = None
    repair_token: str | None = None
    # Runtime-only cursors survive this config's automatic rc75 retries. They
    # are deliberately absent from candidate/verdict fingerprints and disk.
    _policy_states: dict[tuple[str, ...], tuple[str, PolicyRetryState]] = field(
        default_factory=dict,
        init=False,
        repr=False,
        compare=False,
    )
    _policy_states_lock: Any = field(default_factory=threading.Lock, init=False, repr=False, compare=False)
    _finding_leases: dict[str, _FindingLease] = field(default_factory=dict, init=False, repr=False, compare=False)
    _finding_lease_pending: dict[str, threading.Event] = field(
        default_factory=dict, init=False, repr=False, compare=False
    )
    _finding_leases_lock: Any = field(default_factory=threading.Lock, init=False, repr=False, compare=False)

    def policy_state(self, key: tuple[str, ...], prompt: str) -> PolicyRetryState:
        """Return the cursor for one stable logical turn in this target run."""
        prompt_digest = hashlib.sha256(prompt.encode()).hexdigest()
        with self._policy_states_lock:
            entry = self._policy_states.get(key)
            if entry is None or entry[0] != prompt_digest:
                state = PolicyRetryState()
                self._policy_states[key] = (prompt_digest, state)
                return state
            return entry[1]

    def clear_policy_states(self, prefix: tuple[str, ...] = ()) -> None:
        """Discard terminal cursors, optionally below one logical-key prefix."""
        with self._policy_states_lock:
            if not prefix:
                self._policy_states.clear()
                return
            for key in [key for key in self._policy_states if key[: len(prefix)] == prefix]:
                del self._policy_states[key]

    def acquire_finding_lease(self, f: Finding) -> _FindingLease:
        """Reuse one finding's worktree and completed turns during rc75 replay."""
        finding_dir = f.fdir.absolute()
        creator = False
        try:
            while True:
                with self._finding_leases_lock:
                    existing = self._finding_leases.get(f.id)
                    if existing is not None:
                        if existing.finding_dir != finding_dir:
                            raise ConfirmationFailed(f"{f.id}: retry lease belongs to a different finding directory")
                        return existing
                    pending = self._finding_lease_pending.get(f.id)
                    if pending is None:
                        pending = threading.Event()
                        self._finding_lease_pending[f.id] = pending
                        creator = True
                if creator:
                    break
                pending.wait()

            resume_prefix = ("confirm", self.name, "finding", f.id)
            if resumelib.has_prefix(resume_prefix) and not resumelib.fresh_mode():
                candidate = _load_lease(self, f)
            else:
                repo_for_agent, cleanup = setup_repo(self, f)
                candidate = _FindingLease(
                    finding_dir,
                    repo_for_agent,
                    cleanup,
                    source_repo=str(Path(self.repo_dir).absolute()) if self.repo_dir else "",
                    state_path=_lease_file(f),
                )
            with self._finding_leases_lock:
                self._finding_leases[f.id] = candidate
            return candidate
        finally:
            if creator:
                with self._finding_leases_lock:
                    pending = self._finding_lease_pending.pop(f.id, None)
                if pending is not None:
                    pending.set()

    def release_finding_lease(
        self,
        finding_id: str,
        *,
        force: bool = False,
        retain_worktree: bool = False,
    ) -> None:
        """Release runtime-only state, optionally retaining the evidence worktree."""
        with self._finding_leases_lock:
            lease = self._finding_leases.pop(finding_id, None)
        if lease is None:
            return
        with lease._run_lock:
            if lease._closed:
                return
            lease._closed = True
            if not force and resumelib.has_prefix(("confirm", self.name, "finding", finding_id)):
                return
            lease.completed_turns.clear()
            lease.turn_cwds.clear()
            lease.repair_turns.clear()
            lease.no_correction_drafts.clear()
            if not retain_worktree:
                try:
                    lease.cleanup()
                except BaseException as exc:
                    message = f"  WARNING: {finding_id}: retry-lease cleanup failed ({exc})"
                    try:
                        _log(message)
                    except OSError:
                        print(message, flush=True)
            _remove_lease_state(lease)

    def clear_retry_runtime(self) -> None:
        """Release every lease/cursor when no immediate reactive replay follows."""
        with self._finding_leases_lock:
            finding_ids = list(self._finding_leases)
        for finding_id in finding_ids:
            self.release_finding_lease(finding_id)
        self.clear_policy_states()


@dataclass
class Outcome:
    finding: Finding
    status: str
    consensus: bool
    rounds: int
    body: str  # initial A evidence plus any later A defenses
    rr: str | None = None  # assigned RR-NNN when status is PENDING REPAIR
    bug_no: int = 0  # 1-based index in confirmed-bugs.md (the "## Entry N:" number)
    # Normalized phase return code for an INCOMPLETE outcome: 75 means the
    # scheduler may retry after rate limiting; 1 means a permanent/format/infra
    # failure. Canonical outcomes leave this at zero.
    failure_code: int = 0


# ── prompt builders ──────────────────────────────────────────────────────────


def _context(cfg: ConfirmConfig, f: Finding, repo_for_agent: str) -> str:
    wd = cfg.ws.work_dir(cfg.name).absolute()
    return render(
        "confirmation/context",
        finding_json=json.dumps(f.data, indent=2, ensure_ascii=False),
        repo=repo_for_agent,
        spec_dir=str(wd / "spec"),
        repro_dir=str(wd / "repro"),
        fdir=str(f.fdir.absolute()),
        finding_id=f.id,
        bug_confirmation_skill=prompt_skill_ids("bug-confirmation"),
        repair_context=f.repair_context,
    )


def prompt_reproduce(cfg: ConfirmConfig, f: Finding, repo: str) -> str:
    return (
        render(
            "confirmation/reproduce",
            finding_id=f.id,
            canon=" / ".join(CANON),
            fdir=str(f.fdir.absolute()),
            context=_context(cfg, f, repo),
        )
        + cfg.prompt_extra
    )


def prompt_challenge(cfg: ConfirmConfig, f: Finding, repo: str, debate: str) -> str:
    return (
        render(
            "confirmation/challenge",
            finding_id=f.id,
            canon=" / ".join(CANON),
            debate=debate,
            context=_context(cfg, f, repo),
        )
        + cfg.prompt_extra
    )


def prompt_defend(cfg: ConfirmConfig, f: Finding, repo: str, debate: str) -> str:
    return (
        render(
            "confirmation/defend",
            finding_id=f.id,
            canon=" / ".join(CANON),
            debate=debate,
            fdir=str(f.fdir.absolute()),
            context=_context(cfg, f, repo),
        )
        + cfg.prompt_extra
    )


def prompt_repair_draft_retry(
    cfg: ConfirmConfig,
    f: Finding,
    repo: str,
    warning: str,
    previous_log: Path,
) -> str:
    return (
        render(
            "confirmation/repair-draft-retry",
            finding_id=f.id,
            fdir=str(f.fdir.absolute()),
            draft=str((f.fdir / "repair-request.body.md").absolute()),
            previous_log=str(previous_log.absolute()),
            warning=warning,
            context=_context(cfg, f, repo),
        )
        + cfg.prompt_extra
    )


# ── one debate turn (blocking, via the shared phaselib primitive) ────────────


def run_turn(
    cfg: ConfirmConfig,
    f: Finding,
    role: str,
    turn_no: int,
    prompt: str,
    *,
    cwd: str | Path | None = None,
    lease: _FindingLease | None = None,
) -> tuple[str | None, str]:
    """Run one agent turn synchronously; return (verdict, response text).

    Raises :class:`RateLimited` on adapter exit 75 — the turn is never silently
    downgraded to a terminal verdict; the caller records an uncached INCOMPLETE
    outcome and returns 75 after writing the partial report so the scheduler retries."""
    prompt_file = f.fdir / f"turn{turn_no:02d}_{role}.prompt.md"
    log = f.fdir / f"turn{turn_no:02d}_{role}.log"
    if cfg.dry_run:
        _log(f"    [{f.id}] [DRY] turn {turn_no} {role} → {log.name}")
        return ("REPRODUCED" if role == "A" and turn_no == 1 else None), ""
    turn_key = (turn_no, role)
    resume_logical = ("confirm", cfg.name, "finding", f.id, str(turn_no), role)
    prompt_digest = hashlib.sha256(prompt.encode()).hexdigest()
    turn_cwd = str(Path(cwd).absolute()) if cwd is not None else None
    if lease is not None:
        completed = lease.completed_turns.get(turn_key)
        if completed is not None:
            if completed.prompt_digest != prompt_digest or completed.cwd != turn_cwd:
                raise ConfirmationFailed(f"{f.id} turn {turn_no} {role}: retry lease no longer matches the turn")
            _log(f"    [{f.id}] turn {turn_no} {role}: completed before rate limit — reuse")
            return completed.verdict, completed.text

    state_key = ("finding", f.id, str(turn_no), role)
    policy_state = cfg.policy_state(state_key, prompt)
    if lease is not None:
        _persist_lease(cfg, f, lease)
    rc, text = run_agent_blocking(
        cfg.adapter,
        prompt,
        prompt_file,
        log,
        phase_key=PHASE_KEY,
        work_dir=cfg.ws.work_dir(cfg.name).absolute(),
        gate_work_dir=f.fdir.absolute(),
        cwd=cwd,
        claude_alias=cfg.claude_alias,
        max_turns=cfg.max_turns,
        model=cfg.model,
        effort=cfg.effort,
        policy_retries=cfg.policy_retries,
        transient_resumes=cfg.transient_resumes,
        policy_state=policy_state,
        resume_logical=resume_logical,
        resume_phase=PHASE_KEY,
        resume_target=cfg.name,
        resume_kind="finding-turn",
        resume_finding_id=f.id,
        manual_prompt_extra=cfg.resume_prompt_extra,
    )
    if rc == 75:
        raise RateLimited(f"{f.id} turn {turn_no} {role}")
    if rc != 0:
        raise ConfirmationFailed(f"{f.id} turn {turn_no} {role}: adapter exited {rc}")
    if not text.strip():
        raise InvalidAgentOutput(f"{f.id} turn {turn_no} {role}: empty agent output")
    verdict = parse_verdict(text)
    return verdict, text


def _accept_turn(
    cfg: ConfirmConfig,
    f: Finding,
    role: str,
    turn_no: int,
    prompt: str,
    cwd: str | Path | None,
    lease: _FindingLease,
    verdict: str | None,
    text: str,
) -> None:
    """Commit a semantically accepted turn before making it non-resumable."""
    turn_cwd = str(Path(cwd).absolute()) if cwd is not None else None
    result_path = _turn_result_file(cfg, f, turn_no, role, text)
    digest = hashlib.sha256(result_path.read_bytes()).hexdigest()
    lease.completed_turns[(turn_no, role)] = _CompletedTurn(
        hashlib.sha256(prompt.encode()).hexdigest(),
        turn_cwd,
        verdict,
        text,
        result_path,
        digest,
    )
    _persist_lease(cfg, f, lease)
    cfg.clear_policy_states(("finding", f.id, str(turn_no), role))


def _fresh_turn_cwd(f: Finding, role: str, turn_no: int, lease: _FindingLease | None = None) -> Path:
    """Create a trusted per-turn cwd outside the untrusted source checkout.

    Agent prompts carry the absolute source-repo path. Keeping adapter startup
    here prevents repository-owned Codex/Claude hooks or sandbox config from
    executing before the agent can inspect them as data.
    """
    root = f.fdir.absolute() / ".agent-cwd"
    if root.is_symlink() or (root.exists() and not root.is_dir()):
        root.unlink()
    root.mkdir(parents=True, exist_ok=True)
    cwd = root / f"turn{turn_no:02d}_{role}"
    turn_key = (turn_no, role)
    if lease is not None and turn_key in lease.turn_cwds:
        expected = lease.turn_cwds[turn_key]
        if expected != cwd or cwd.is_symlink() or not cwd.is_dir():
            raise ConfirmationFailed(f"{f.id}: retained cwd for turn {turn_no} {role} is no longer safe")
        return cwd
    if cwd.is_symlink():
        cwd.unlink()
    elif cwd.exists():
        shutil.rmtree(cwd)
    cwd.mkdir(parents=True)
    try:
        subprocess.run(
            ["git", "init", "--quiet", str(cwd)],
            env=_dispatcher_git_env(cwd),
            check=True,
            capture_output=True,
            text=True,
        )
    except (OSError, subprocess.CalledProcessError) as exc:
        raise ConfirmationFailed(f"{f.id}: could not create trusted per-turn cwd: {exc}") from exc
    if lease is not None:
        lease.turn_cwds[turn_key] = cwd
    return cwd


def _consolidate_cwd(work_dir: Path, *, fresh: bool) -> Path:
    """Return the stable, dispatcher-owned cwd for the consolidate agent."""
    cwd = work_dir.absolute() / ".consolidate-cwd"
    if fresh:
        if cwd.is_symlink():
            cwd.unlink()
        elif cwd.is_dir():
            shutil.rmtree(cwd)
        elif cwd.exists():
            cwd.unlink()
        cwd.mkdir(parents=True)
        try:
            subprocess.run(
                ["git", "init", "--quiet", str(cwd)],
                env=_dispatcher_git_env(cwd),
                check=True,
                capture_output=True,
                text=True,
            )
        except (OSError, subprocess.CalledProcessError) as exc:
            raise ConsolidateFailed(f"could not create trusted consolidate cwd: {exc}") from exc

    git_dir = cwd / ".git"
    if cwd.is_symlink() or not cwd.is_dir() or git_dir.is_symlink() or not git_dir.is_dir():
        raise ConsolidateFailed("consolidate cwd is not safe")
    try:
        probe = subprocess.run(
            ["git", "-C", str(cwd), "rev-parse", "--show-toplevel", "--absolute-git-dir"],
            env=_dispatcher_git_env(cwd),
            check=True,
            capture_output=True,
            text=True,
        )
    except (OSError, subprocess.CalledProcessError) as exc:
        raise ConsolidateFailed(f"could not validate retained consolidate cwd: {exc}") from exc
    paths = probe.stdout.splitlines()
    if len(paths) != 2 or Path(paths[0]).resolve() != cwd.resolve() or Path(paths[1]).resolve() != git_dir.resolve():
        raise ConsolidateFailed("consolidate cwd is not safe")
    return cwd


# ── per-finding git worktree (build isolation) ───────────────────────────────


def _retained_worktree_cleanup(root: Path, wt: Path, finding_id: str) -> Callable[[], None]:
    git_env = _dispatcher_git_env(root)

    def cleanup() -> None:
        result = subprocess.run(
            ["git", "-C", str(root), "worktree", "remove", "--force", str(wt)],
            env=git_env,
            capture_output=True,
            text=True,
        )
        if result.returncode == 0:
            return
        subprocess.run(["git", "-C", str(root), "worktree", "prune"], env=git_env, capture_output=True)
        message = f"{finding_id}: could not remove isolated worktree (left on disk): {result.stderr.strip()[:200]}"
        try:
            _log(f"  WARNING: {message}")
        except OSError:
            print(f"  WARNING: {message}", flush=True)

    return cleanup


def setup_repo(cfg: ConfirmConfig, f: Finding) -> tuple[str, Callable[[], None]]:
    """Return (repo_path_for_agent, cleanup). With worktree (default) each finding
    gets its own detached worktree so parallel builds and source patches do not
    collide. If isolation was requested, never fall back to the shared source
    checkout: a valid Level-3 reproduction may modify it."""
    repo = str(Path(cfg.repo_dir).absolute()) if cfg.repo_dir else ""
    if not cfg.worktree or cfg.dry_run or not repo:
        return repo, lambda: None
    try:
        return _setup_worktree(cfg, f, repo)
    except ConfirmationFailed:
        raise
    except Exception as exc:
        raise ConfirmationFailed(f"{f.id}: worktree isolation failed: {exc}") from exc


def _setup_worktree(cfg: ConfirmConfig, f: Finding, repo: str) -> tuple[str, Callable[[], None]]:
    """Per-finding detached git worktree with the launch dir's local changes copied
    in. Raises on any failure; the finding then remains uncached and retryable."""
    git_env = _dispatcher_git_env(repo)
    probe = subprocess.run(
        ["git", "-C", repo, "rev-parse", "--is-inside-work-tree"],
        env=git_env,
        capture_output=True,
        text=True,
    )
    if probe.returncode != 0 or probe.stdout.strip() != "true":
        raise ConfirmationFailed(f"{f.id}: worktree isolation requested but {repo!r} is not a git checkout")
    root_result = subprocess.run(
        ["git", "-C", repo, "rev-parse", "--show-toplevel"], env=git_env, capture_output=True, text=True
    )
    if root_result.returncode != 0:
        raise ConfirmationFailed(f"{f.id}: could not resolve repository root: {root_result.stderr.strip()}")
    root = Path(root_result.stdout.strip()).resolve()
    status_cmd = ["git", "-C", str(root), "status", "--porcelain", "--untracked-files=all"]
    pathspec = ["--", "."]
    try:
        output_rel = cfg.ws.work_dir(cfg.name).resolve().relative_to(root)
    except ValueError:
        output_rel = None
    if output_rel is not None and output_rel.parts:
        # Ignore only this dispatcher's own output. Every other tracked or
        # untracked change is copied into the isolated worktree below.
        rel = output_rel.as_posix()
        pathspec += [f":(exclude){rel}", f":(exclude){rel}/**"]
    status_cmd += pathspec
    dirty = subprocess.run(status_cmd, env=git_env, capture_output=True, text=True)
    if dirty.returncode != 0:
        raise ConfirmationFailed(f"{f.id}: could not inspect repository state: {dirty.stderr.strip()}")
    patch = subprocess.run(
        ["git", "-C", str(root), "diff", "--binary", "HEAD", *pathspec], env=git_env, capture_output=True
    )
    untracked = subprocess.run(
        ["git", "-C", str(root), "ls-files", "--others", "--exclude-standard", "-z", *pathspec],
        env=git_env,
        capture_output=True,
    )
    if patch.returncode != 0 or untracked.returncode != 0:
        raise ConfirmationFailed(f"{f.id}: could not snapshot local repository changes")
    base_wt = f.fdir.absolute() / "worktree"
    try:
        base_wt.parent.resolve().relative_to(cfg.ws.work_dir(cfg.name).resolve())
    except ValueError as exc:
        raise ConfirmationFailed(f"{f.id}: worktree destination escapes the confirmation output") from exc
    wt = _prepare_worktree_destination(root, git_env, base_wt, f)

    try:
        subprocess.run(
            ["git", "-C", str(root), "worktree", "add", "--detach", "--force", str(wt)],
            env=git_env,
            check=True,
            capture_output=True,
            text=True,
        )
    except subprocess.CalledProcessError as e:
        raise ConfirmationFailed(f"{f.id}: worktree isolation failed: {e.stderr.strip()[:200]}") from e

    try:
        if patch.stdout:
            applied = subprocess.run(
                ["git", "-C", str(wt), "apply", "--binary", "-"],
                env=git_env,
                input=patch.stdout,
                capture_output=True,
            )
            if applied.returncode != 0:
                raise ConfirmationFailed(
                    f"{f.id}: could not apply tracked local changes to isolated worktree: "
                    f"{applied.stderr.decode(errors='replace').strip()[:200]}"
                )
        for raw_name in (name for name in untracked.stdout.split(b"\0") if name):
            relative = Path(os.fsdecode(raw_name))
            source = root / relative
            destination = wt / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            if source.is_symlink():
                destination.symlink_to(os.readlink(source))
            else:
                shutil.copy2(source, destination)
    except Exception:
        subprocess.run(
            ["git", "-C", str(root), "worktree", "remove", "--force", str(wt)],
            env=git_env,
            capture_output=True,
        )
        raise

    if dirty.stdout.strip():
        _log(f"  [{f.id}] copied tracked/untracked local changes into isolated worktree")

    return str(wt), _retained_worktree_cleanup(root, wt, f.id)


def _worktree_candidates(base: Path) -> list[Path]:
    deterministic = [base, *(base.with_name(f"{base.name}-{index}") for index in range(1, 5))]
    randomised = [
        base.with_name(f"{base.name}-{os.getpid()}-{threading.get_ident()}-{secrets.token_hex(4)}") for _ in range(8)
    ]
    return deterministic + randomised


def _remove_stale_worktree(root: Path, git_env: dict[str, str] | None, wt: Path, f: Finding) -> OSError | None:
    if wt.is_symlink():
        raise ConfirmationFailed(f"{f.id}: refusing stale worktree symlink")
    # Target only this dispatcher-owned path. Avoid global `worktree prune`,
    # which can affect unrelated user worktrees.
    subprocess.run(
        ["git", "-C", str(root), "worktree", "remove", "--force", str(wt)],
        env=git_env,
        capture_output=True,
    )
    if not wt.exists():
        return None
    try:
        if wt.is_dir():
            shutil.rmtree(wt)
        else:
            wt.unlink()
    except OSError as exc:
        return exc
    return None


def _prepare_worktree_destination(root: Path, git_env: dict[str, str] | None, base_wt: Path, f: Finding) -> Path:
    base_wt.parent.mkdir(parents=True, exist_ok=True)
    candidates = _worktree_candidates(base_wt)
    failures: list[str] = []
    for index, wt in enumerate(candidates):
        failure = _remove_stale_worktree(root, git_env, wt, f)
        if failure is None:
            if index > 0:
                try:
                    _log(f"  WARNING: {f.id}: using alternate isolated worktree {wt} after stale cleanup failure")
                except OSError:
                    print(
                        f"  WARNING: {f.id}: using alternate isolated worktree {wt} after stale cleanup failure",
                        flush=True,
                    )
            return wt
        failures.append(f"{wt}: {failure}")
        next_wt = candidates[index + 1] if index + 1 < len(candidates) else None
        if next_wt is not None:
            message = f"{f.id}: could not remove stale isolated worktree {wt}: {failure}; trying {next_wt}"
            try:
                _log(f"  WARNING: {message}")
            except OSError:
                print(f"  WARNING: {message}", flush=True)
    raise ConfirmationFailed(
        f"{f.id}: could not prepare an isolated worktree after stale cleanup failures: {failures[0]}"
    )


# ── one finding: reproduce, then optional debate ─────────────────────────────


def _source_kind(f: Finding) -> str:
    source = str(f.data.get("source") or "").strip().lower().replace("_", "-")
    if source in {"model-checking", "mc"} or (not source and f.id.startswith("MC-")):
        return "model-checking"
    if source in {"code-review", "code review", "cr"} or (not source and f.id.startswith("CR-")):
        return "code-review"
    raise InvalidAgentOutput(f"{f.id}: unknown finding source {f.data.get('source')!r}")


def _validate_status_source(f: Finding, status: str) -> None:
    source = _source_kind(f)
    if status == "PENDING REPAIR" and source != "model-checking":
        raise InvalidAgentOutput(f"{f.id}: PENDING REPAIR is only valid for model-checking findings")
    if status == "DROPPED" and source != "code-review":
        raise InvalidAgentOutput(f"{f.id}: {status} is not a valid model-checking disposition")


def _without_verdict_lines(text: str) -> str:
    return "\n".join(line for line in text.splitlines() if not re.match(r"^\s*VERDICT\s*:", line, re.I)).strip()


def _repro_files(cfg: ConfirmConfig, f: Finding) -> list[Path]:
    return [p for p in (cfg.ws.work_dir(cfg.name) / "repro").glob(f"test_bug{f.id}_*") if p.is_file()]


def _validate_turn_output(f: Finding, status: str | None, text: str) -> str:
    if status is None:
        raise InvalidAgentOutput(f"{f.id}: output has no canonical VERDICT")
    _validate_status_source(f, status)
    evidence = _without_verdict_lines(text)
    if len(evidence) < 20:
        raise InvalidAgentOutput(f"{f.id}: VERDICT has no substantive supporting evidence")
    return evidence


def _validate_final_artifacts(cfg: ConfirmConfig, f: Finding, status: str) -> None:
    _validate_status_source(f, status)
    if status == "REPRODUCED":
        repros = _repro_files(cfg, f)
        if not repros or any(p.stat().st_size == 0 for p in repros):
            raise InvalidAgentOutput(f"{f.id}: REPRODUCED requires a non-empty repro/test_bug{f.id}_* artifact")
    if status == "PENDING REPAIR":
        _read_repair_draft(cfg, f)


def _repair_draft_warning(cfg: ConfirmConfig, f: Finding, draft: RepairDraft) -> str | None:
    """Return the legacy schema diagnostic without making it a gate."""
    try:
        _parse_repair_draft(draft.raw, cfg, f)
    except Exception as exc:
        return f"{f.id}: {exc or type(exc).__name__}"
    return None


def _restore_repair_draft(path: Path, body: str | None) -> None:
    """Restore the pre-correction draft state if the advisory turn damages it."""
    if path.is_symlink() or path.is_file():
        path.unlink()
    elif path.is_dir():
        shutil.rmtree(path)
    elif path.exists():
        path.unlink()
    if body is not None:
        path.write_text(body)


def _final_outcome(
    cfg: ConfirmConfig,
    f: Finding,
    status: str,
    consensus: bool,
    rounds: int,
    body: str,
) -> Outcome:
    _validate_final_artifacts(cfg, f, status)
    return Outcome(f, status, consensus, rounds, body)


def _compose_evidence(initial: str, defenses: list[str]) -> str:
    body = _without_verdict_lines(initial)
    additions = [_without_verdict_lines(text) for text in defenses]
    additions = [text for text in additions if text]
    if additions:
        body += "\n\n## Debate addendum\n\n" + "\n\n".join(additions)
    return body


def _debate_entry(f: Finding, role: str, turn_no: int, label: str, verdict: str | None) -> str:
    """One debate-index line: the verdict + a pointer to the turn's full log. The
    full agent output is NOT inlined — inlining every prior turn made the next
    turn's prompt exceed the agent's input limit (codex rejects >1 MiB); the
    agent reads the linked logs itself instead."""
    log = f.fdir / f"turn{turn_no:02d}_{role}.log"
    return f"\n## {label} — VERDICT: {verdict or '(none)'}\nFull turn log (read it for the full argument): {log}\n"


def run_finding(cfg: ConfirmConfig, f: Finding, *, _lease: _FindingLease | None = None) -> Outcome:
    if not f.id or set(f.id) - ID_CHARS or f.id in {".", ".."}:
        raise InvalidAgentOutput(f"unsafe finding id: {f.id!r}")
    f.fdir.mkdir(parents=True, exist_ok=True)
    repro_dir = cfg.ws.work_dir(cfg.name).absolute() / "repro"
    repro_dir.mkdir(parents=True, exist_ok=True)
    owned_lease = _lease is None
    if _lease is None:
        repo_for_agent, cleanup = setup_repo(cfg, f)
        lease = _FindingLease(f.fdir.absolute(), repo_for_agent, cleanup)
    else:
        lease = _lease
    if lease.finding_dir != f.fdir.absolute() or lease._closed:
        raise ConfirmationFailed(f"{f.id}: invalid retry lease")
    debate = f.fdir / "debate.md"
    lease._run_lock.acquire()
    try:
        with lease._run_lock:
            if not lease.initialized:
                # Fresh generations must create fresh artifacts. A reactive rc75
                # continuation keeps them, its exact worktree, and its cwd.
                # A scoped repair pass continues this finding's evidence. Keep
                # its prior reproduction artifacts available to the worker;
                # they may be reused or selectively updated, but must not be
                # erased merely because Phase 3 produced a new repair token.
                if cfg.repair_round is None:
                    for stale in _repro_files(cfg, f):
                        stale.unlink()
                rr_body = f.fdir / "repair-request.body.md"
                if rr_body.is_file():
                    rr_body.unlink()
                lease.initialized = True
            repo_for_agent = lease.repo_for_agent
            turn = 1

            def prepare_pending(previous_turn: int, previous_role: str = "A") -> int:
                """Reuse the durable draft decision or make at most one correction turn.

                Both correction and no-correction decisions are recorded before
                the next turn starts. A later rate-limit replay therefore cannot
                renumber an already-started B turn from mutable draft contents.
                """
                repair_key = (previous_turn, previous_role)
                repair = lease.repair_turns.get(repair_key)
                if repair_key in lease.no_correction_drafts:
                    return previous_turn
                original = repair.original if repair is not None else None
                if repair is None:
                    problem: Exception | str | None = None
                    try:
                        draft = _read_repair_draft(cfg, f)
                        original = draft.raw
                        problem = _repair_draft_warning(cfg, f, draft)
                    except InvalidRepairRequest as exc:
                        problem = exc
                        draft_path = f.fdir / "repair-request.body.md"
                        if not draft_path.is_symlink() and draft_path.is_file():
                            with contextlib.suppress(OSError, UnicodeError):
                                original = draft_path.read_text()

                    if problem is None:
                        assert original is not None
                        lease.no_correction_drafts[repair_key] = hashlib.sha256(original.encode()).hexdigest()
                        _persist_lease(cfg, f, lease)
                        return previous_turn

                    warning = str(problem)
                    _log(f"  WARNING: {warning}")
                    if lease.repair_retry_used:
                        if original is None:
                            assert isinstance(problem, Exception)
                            raise problem
                        lease.no_correction_drafts[repair_key] = hashlib.sha256(original.encode()).hexdigest()
                        _persist_lease(cfg, f, lease)
                        return previous_turn

                    lease.repair_retry_used = True
                    correction_turn = previous_turn + 1
                    repair = _RepairTurn(
                        correction_turn,
                        prompt_repair_draft_retry(
                            cfg,
                            f,
                            repo_for_agent,
                            warning,
                            f.fdir / f"turn{previous_turn:02d}_{previous_role}.log",
                        ),
                        original,
                    )
                    lease.repair_turns[repair_key] = repair

                correction_turn = repair.turn_no
                if repair.disabled:
                    return correction_turn
                if repair.verdict is None:
                    draft_path = f.fdir / "repair-request.body.md"
                    correction_cwd = _fresh_turn_cwd(f, "A-repair", correction_turn, lease)
                    try:
                        correction_verdict, correction_text = run_turn(
                            cfg,
                            f,
                            "A-repair",
                            correction_turn,
                            repair.prompt,
                            cwd=correction_cwd,
                            lease=lease,
                        )
                        repair.verdict = correction_verdict
                    except RateLimited:
                        raise
                    except Exception as exc:
                        repair.disabled = True
                        _restore_repair_draft(draft_path, original)
                        _persist_lease(cfg, f, lease)
                        cfg.clear_policy_states(("finding", f.id, str(correction_turn), "A-repair"))
                        if original is None or not original.strip():
                            raise
                        _log(f"  WARNING: {f.id}: repair-draft correction failed ({exc}); keeping the original draft")
                        return correction_turn

                    try:
                        corrected = _read_repair_draft(cfg, f)
                    except InvalidRepairRequest:
                        _restore_repair_draft(draft_path, original)
                        if original is None or not original.strip():
                            raise
                        _log(f"  WARNING: {f.id}: correction removed the usable draft; keeping the original draft")
                        corrected = _read_repair_draft(cfg, f)

                    corrected_warning = _repair_draft_warning(cfg, f, corrected)
                    if corrected_warning is not None:
                        _log(f"  WARNING: {corrected_warning} (continuing with the non-empty draft)")
                    _validate_turn_output(f, correction_verdict, correction_text)
                    _accept_turn(
                        cfg,
                        f,
                        "A-repair",
                        correction_turn,
                        repair.prompt,
                        correction_cwd,
                        lease,
                        correction_verdict,
                        correction_text,
                    )

                debate.write_text(
                    debate.read_text()
                    + _debate_entry(
                        f,
                        "A-repair",
                        correction_turn,
                        "A (repair-draft correction)",
                        repair.verdict,
                    )
                )
                return correction_turn

        # Turn 1 — Reproducer (neutral): investigate + reproduce.
        a_prompt = prompt_reproduce(cfg, f, repo_for_agent)
        a_cwd = _fresh_turn_cwd(f, "A", 1, lease)
        a_verdict, a_text = run_turn(
            cfg,
            f,
            "A",
            1,
            a_prompt,
            cwd=a_cwd,
            lease=lease,
        )
        debate.write_text(
            f"# Debate: {f.id}\n\nThis is an INDEX of the debate. Each entry links the turn's "
            f"full agent log — open the logs you need; they are not inlined here.\n"
            + _debate_entry(f, "A", 1, "A (turn 1 — reproduce)", a_verdict)
        )
        _validate_turn_output(f, a_verdict, a_text)
        assert a_verdict is not None
        if a_verdict != "PENDING REPAIR" and (a_verdict not in CONFIRM or not cfg.debate):
            _validate_final_artifacts(cfg, f, a_verdict)
        _accept_turn(cfg, f, "A", 1, a_prompt, a_cwd, lease, a_verdict, a_text)
        if a_verdict == "PENDING REPAIR":
            turn = prepare_pending(turn)
        initial_text = a_text
        if a_verdict not in CONFIRM:
            _log(f"  [{f.id}] A: {a_verdict} (dismissal) — no debate")
            return _final_outcome(cfg, f, a_verdict, True, 0, _compose_evidence(a_text, []))
        if not cfg.debate:
            _log(f"  [{f.id}] A: {a_verdict} (debate off) — verdict final")
            return _final_outcome(cfg, f, a_verdict, True, 0, _compose_evidence(a_text, []))

        _log(f"  [{f.id}] A: {a_verdict} → opening debate")
        defenses: list[str] = []
        for rnd in range(1, cfg.rounds + 1):
            turn += 1
            b_prompt = prompt_challenge(cfg, f, repo_for_agent, str(debate))
            b_cwd = _fresh_turn_cwd(f, "B", turn, lease)
            b_verdict, b_text = run_turn(
                cfg,
                f,
                "B",
                turn,
                b_prompt,
                cwd=b_cwd,
                lease=lease,
            )
            debate.write_text(debate.read_text() + _debate_entry(f, "B", turn, f"B (round {rnd})", b_verdict))
            _validate_turn_output(f, b_verdict, b_text)
            assert b_verdict is not None
            if b_verdict != "PENDING REPAIR" and b_verdict == a_verdict:
                _validate_final_artifacts(cfg, f, b_verdict)
            _accept_turn(cfg, f, "B", turn, b_prompt, b_cwd, lease, b_verdict, b_text)
            # B agrees with A's current verdict → consensus already. Do NOT pull A
            # into a defense it does not need: A only ever hears about the debate
            # when B actually disagrees (the defend turn is where it is introduced).
            if b_verdict is not None and b_verdict == a_verdict:
                _log(f"  [{f.id}] round {rnd}: B={b_verdict} agrees — consensus, A not invoked")
                if a_verdict == "PENDING REPAIR":
                    turn = prepare_pending(turn, "B")
                return _final_outcome(
                    cfg,
                    f,
                    a_verdict,
                    True,
                    rnd,
                    _compose_evidence(initial_text, [*defenses, b_text]),
                )
            turn += 1
            defend_prompt = prompt_defend(cfg, f, repo_for_agent, str(debate))
            defend_cwd = _fresh_turn_cwd(f, "A", turn, lease)
            a_verdict, a_text = run_turn(
                cfg,
                f,
                "A",
                turn,
                defend_prompt,
                cwd=defend_cwd,
                lease=lease,
            )
            debate.write_text(debate.read_text() + _debate_entry(f, "A", turn, f"A (round {rnd})", a_verdict))
            _validate_turn_output(f, a_verdict, a_text)
            assert a_verdict is not None
            if a_verdict != "PENDING REPAIR" and a_verdict == b_verdict:
                _validate_final_artifacts(cfg, f, a_verdict)
            _accept_turn(cfg, f, "A", turn, defend_prompt, defend_cwd, lease, a_verdict, a_text)
            if a_verdict == "PENDING REPAIR":
                turn = prepare_pending(turn)
            defenses.append(a_text)
            _log(f"  [{f.id}] round {rnd}: B={b_verdict} A={a_verdict}")
            if a_verdict and b_verdict and a_verdict == b_verdict:
                return _final_outcome(cfg, f, a_verdict, True, rnd, _compose_evidence(initial_text, defenses))
        _log(f"  [{f.id}] no consensus after {cfg.rounds} rounds → NEEDS MORE INFO")
        return _final_outcome(cfg, f, "NEEDS MORE INFO", False, cfg.rounds, _compose_evidence(initial_text, defenses))
    finally:
        lease._run_lock.release()
        if owned_lease:
            lease._closed = True
            lease.cleanup()


# ── idempotent per-finding verdict cache (survives a rate-limit phase retry) ──


def _generation_content(cfg: ConfirmConfig) -> str:
    path = cfg.ws.work_dir(cfg.name) / "spec" / "confirmation-generation.json"
    try:
        return path.read_text() if path.is_file() else "0"
    except OSError as exc:
        raise ConfirmationFailed(f"cannot read confirmation generation: {exc}") from exc


def _digest(value: Any) -> str:
    encoded = json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()
    return hashlib.sha256(encoded).hexdigest()


def _adapter_identity(cfg: ConfirmConfig) -> dict[str, str]:
    path = cfg.adapter.expanduser()
    try:
        resolved = path.resolve(strict=True)
        content = hashlib.sha256(resolved.read_bytes()).hexdigest()
    except OSError:
        resolved = path.resolve()
        content = "missing"
    return {"path": str(resolved), "content": content}


def _tuning_identity(cfg: ConfirmConfig) -> dict[str, dict[str, str | None]]:
    """Effective tuning inputs known before an adapter starts.

    Explicit Specula values, including an empty reset, win over adapter-specific
    environment fallbacks. CLI config-file defaults remain intentionally opaque.
    """
    adapter = cfg.adapter.stem
    model: dict[str, str | None]
    effort: dict[str, str | None]
    if cfg.model is not None:
        model = {"source": "specula", "value": cfg.model}
    else:
        model_env = {
            "claude-code": "CLAUDE_MODEL",
            "codex": "CODEX_MODEL",
            "copilot-cli": "COPILOT_MODEL",
            "opencode": "OPENCODE_MODEL",
            "pi": "PI_MODEL",
        }.get(adapter)
        model_value = (os.environ.get(model_env) or None) if model_env is not None else None
        model = {"source": model_env if model_value is not None else "adapter-default", "value": model_value}

    if cfg.effort is not None:
        effort = {"source": "specula", "value": cfg.effort}
    elif adapter == "claude-code":
        # run_agent_blocking explicitly injects max, overriding CLAUDE_EFFORT.
        effort = {"source": "specula-default", "value": "max"}
    else:
        effort_env = {
            "codex": "CODEX_EFFORT",
            "opencode": "OPENCODE_EFFORT",
            "pi": "PI_EFFORT",
        }.get(adapter)
        effort_value = (os.environ.get(effort_env) or None) if effort_env is not None else None
        effort = {
            "source": effort_env if effort_value is not None else "adapter-default",
            "value": effort_value,
        }
    return {"model": model, "effort": effort}


def _skill_identity() -> dict[str, str]:
    root = SKILLS / "bug-confirmation"
    result: dict[str, str] = {}
    if root.is_dir():
        for path in sorted(p for p in root.rglob("*") if p.is_file()):
            result[str(path.relative_to(root))] = hashlib.sha256(path.read_bytes()).hexdigest()
    return result


def _repo_cache_identity(cfg: ConfirmConfig) -> dict[str, str]:
    repo = cfg.repo_dir.rstrip("/")
    if not repo:
        return {"path": "", "head": "", "isolation": str(cfg.worktree)}
    git_env = _dispatcher_git_env(repo)
    head = subprocess.run(["git", "-C", repo, "rev-parse", "HEAD"], env=git_env, capture_output=True)
    if head.returncode != 0:
        if cfg.worktree:
            raise ConfirmationFailed(f"worktree isolation requested but {repo!r} is not a git checkout")
        return {"path": str(Path(repo).resolve()), "head": "non-git", "isolation": "False"}
    root_result = subprocess.run(["git", "-C", repo, "rev-parse", "--show-toplevel"], env=git_env, capture_output=True)
    if root_result.returncode != 0:
        raise ConfirmationFailed(f"could not resolve repository root for cache identity: {repo!r}")
    root = Path(root_result.stdout.decode(errors="replace").strip()).resolve()
    identity = {
        "path": str(root),
        "head": head.stdout.decode(errors="replace").strip(),
        "isolation": str(cfg.worktree),
    }
    # Bind all local state in every mode. In worktree mode this ensures the
    # cached verdict matches the dirty snapshot copied into each isolation.
    pathspec = ["--", "."]
    try:
        output_rel = cfg.ws.work_dir(cfg.name).resolve().relative_to(root)
    except ValueError:
        output_rel = None
    if output_rel is not None and output_rel.parts:
        rel = output_rel.as_posix()
        pathspec += [f":(exclude){rel}", f":(exclude){rel}/**"]
    diff = subprocess.run(
        ["git", "-C", str(root), "diff", "--binary", "HEAD", *pathspec], env=git_env, capture_output=True
    )
    status = subprocess.run(
        ["git", "-C", str(root), "status", "--porcelain", "--untracked-files=all", *pathspec],
        env=git_env,
        capture_output=True,
    )
    untracked = subprocess.run(
        ["git", "-C", str(root), "ls-files", "--others", "--exclude-standard", "-z", *pathspec],
        env=git_env,
        capture_output=True,
    )
    if any(result.returncode != 0 for result in (diff, status, untracked)):
        raise ConfirmationFailed(f"could not inspect repository state for cache identity: {root}")
    local = hashlib.sha256(diff.stdout + b"\0" + status.stdout)
    for raw_name in sorted(name for name in untracked.stdout.split(b"\0") if name):
        local.update(b"\0" + raw_name + b"\0")
        try:
            local.update((root / raw_name.decode(errors="surrogateescape")).read_bytes())
        except OSError as exc:
            local.update(f"<unreadable:{exc}>".encode())
    identity["local"] = local.hexdigest()
    return identity


def _prompt_sources() -> dict[str, str]:
    root = Path(__file__).resolve().parent / "prompts" / "confirmation"
    result: dict[str, str] = {}
    for name in ("context.md", "reproduce.md", "challenge.md", "defend.md", "repair-draft-retry.md"):
        path = root / name
        result[name] = path.read_text() if path.is_file() else ""
    return result


def _spec_identity(cfg: ConfirmConfig, f: Finding) -> dict[str, str]:
    work_dir = cfg.ws.work_dir(cfg.name).resolve()
    spec_dir = work_dir / "spec"
    result: dict[str, str] = {}
    if spec_dir.is_dir():
        for path in sorted(p for p in spec_dir.rglob("*") if p.is_file() and p.suffix.lower() in {".tla", ".cfg"}):
            relative = str(path.relative_to(work_dir))
            if path.is_symlink():
                resolved = path.resolve()
                try:
                    resolved.relative_to(work_dir)
                except ValueError:
                    result[relative] = "unsafe-symlink"
                else:
                    target_hash = hashlib.sha256(resolved.read_bytes()).hexdigest() if resolved.is_file() else "missing"
                    result[relative] = f"symlink:{os.readlink(path)}:{target_hash}"
            else:
                result[relative] = hashlib.sha256(path.read_bytes()).hexdigest()
        # Bug numbers and RR links are assigned from candidate order. Bind the
        # complete candidate set so a reorder cannot reuse a verdict carrying an
        # RR whose ``bug_id: Bug N`` now points at a different report entry.
        candidates = spec_dir / "candidates.json"
        if candidates.is_file():
            result["spec/candidates.json"] = hashlib.sha256(candidates.read_bytes()).hexdigest()
    counterexample = f.data.get("counterexample")
    if isinstance(counterexample, str) and counterexample.strip():
        raw = Path(counterexample)
        if raw.is_absolute() or ".." in raw.parts:
            result["finding-counterexample"] = "unsafe-path"
        else:
            path = work_dir / raw
            resolved = path.resolve()
            try:
                resolved.relative_to(work_dir)
            except ValueError:
                result["finding-counterexample"] = "unsafe-path"
            else:
                if path.is_file() and not path.is_symlink():
                    result["finding-counterexample"] = hashlib.sha256(path.read_bytes()).hexdigest()
                elif path.is_symlink():
                    target_hash = hashlib.sha256(resolved.read_bytes()).hexdigest() if resolved.is_file() else "missing"
                    result["finding-counterexample"] = f"symlink:{os.readlink(path)}:{target_hash}"
                else:
                    result["finding-counterexample"] = "missing"
    return result


def _verdict_fingerprint(cfg: ConfirmConfig, f: Finding) -> str:
    confirmation_identity: Any
    if cfg.repair_round is None:
        confirmation_identity = _generation_content(cfg)
    else:
        # A repair pass is scoped by the committed Phase-3 result, not by the
        # global confirmation generation that invalidates unrelated findings.
        confirmation_identity = {
            "repair_token": cfg.repair_token or f"repair-round:{cfg.repair_round}",
        }
    return _digest(
        {
            "version": _CACHE_VERSION,
            "generation": confirmation_identity,
            "finding": f.data,
            "spec": _spec_identity(cfg, f),
            "repo": _repo_cache_identity(cfg),
            "adapter": _adapter_identity(cfg),
            "claude_alias": cfg.claude_alias,
            "debate": cfg.debate,
            "rounds": cfg.rounds,
            "prompt_extra": cfg.prompt_extra,
            "max_turns": cfg.max_turns,
            "tuning": _tuning_identity(cfg),
            "prompts": _prompt_sources(),
            "skill": _skill_identity(),
        }
    )


def _rr_field_text(text: str, key: str) -> list[str]:
    lines = text.splitlines()
    if lines and lines[0] == "---":
        try:
            end = lines.index("---", 1)
        except ValueError:
            return []
        lines = lines[1:end]
    else:
        # Legacy requests without a fenced header retain the old bounded read.
        lines = lines[:25]
    prefix = key + ":"
    return [line[len(prefix) :].strip() for line in lines if line.startswith(prefix)]


def _repair_request_cache_content(text: str, status: str) -> bytes:
    """Canonical RR bytes for cache validation.

    OPEN -> DEFERRED is orchestrator bookkeeping, not a new confirmation
    result. Normalize only that transition so the cached PENDING verdict remains
    reusable. IN_REPAIR and CONSUMED stay byte-distinct and therefore invalidate
    the old verdict as before.
    """
    lines = text.splitlines()
    if status == "DEFERRED":
        for i, line in enumerate(lines[:25]):
            if line.startswith("status:"):
                lines[i] = "status: OPEN"
                break
        defer_notes = {
            "- deferred (orchestrator): repair loop round cap reached",
            "- reconciled (orchestrator): deferred directory is authoritative",
        }
        if lines and lines[-1] in defer_notes:
            lines.pop()
    return ("\n".join(lines) + "\n").encode()


def _artifact_identity(cfg: ConfirmConfig, o: Outcome) -> dict[str, Any]:
    _validate_final_artifacts(cfg, o.finding, o.status)
    result: dict[str, Any] = {}
    if o.status == "REPRODUCED":
        result["repro"] = {
            path.name: hashlib.sha256(path.read_bytes()).hexdigest() for path in sorted(_repro_files(cfg, o.finding))
        }
    if o.status == "PENDING REPAIR":
        body_file = o.finding.fdir / "repair-request.body.md"
        body = body_file.read_bytes()
        result["repair_body"] = hashlib.sha256(body).hexdigest()
    if o.rr is not None:
        if not re.fullmatch(r"RR-\d+", str(o.rr)):
            raise InvalidRepairRequest(f"invalid cached repair id: {o.rr!r}")
        rr_dir = cfg.ws.work_dir(cfg.name) / "spec" / "repair-requests"
        matches = list(rr_dir.rglob(f"{o.rr}.md")) if rr_dir.is_dir() else []
        if len(matches) != 1:
            raise InvalidRepairRequest(f"cached repair {o.rr} must have exactly one active/deferred file")
        rr_file = matches[0]
        text = rr_file.read_text(errors="replace")
        ids = _rr_field_text(text, "id")
        statuses = _rr_field_text(text, "status")
        if (
            ids != [o.rr]
            or len(statuses) != 1
            or statuses[0]
            not in {
                "OPEN",
                "IN_REPAIR",
                "CONSUMED",
                "DEFERRED",
            }
        ):
            raise InvalidRepairRequest(f"cached repair {o.rr} has invalid id/status frontmatter")
        finding_ids = _rr_field_text(text, "finding_id")
        if finding_ids != [o.finding.id]:
            raise InvalidRepairRequest(f"cached repair {o.rr} has wrong finding_id")
        relative = rr_file.relative_to(rr_dir)
        expected = Path("deferred") / rr_file.name if statuses[0] == "DEFERRED" else Path(rr_file.name)
        if relative != expected:
            raise InvalidRepairRequest(f"cached repair {o.rr} has invalid location for status {statuses[0]}")
        cache_path = Path(rr_file.name) if statuses[0] == "DEFERRED" else relative
        result["repair_request"] = {
            "path": str(cache_path),
            "content": hashlib.sha256(_repair_request_cache_content(text, statuses[0])).hexdigest(),
        }
    return result


def _save_verdict(o: Outcome, cfg: ConfirmConfig) -> None:
    o.finding.fdir.mkdir(parents=True, exist_ok=True)
    vf = o.finding.fdir / "verdict.json"
    tmp = vf.with_suffix(".json.tmp")
    tmp.write_text(
        json.dumps(
            {
                "cache_version": _CACHE_VERSION,
                "fingerprint": _verdict_fingerprint(cfg, o.finding),
                "status": o.status,
                "consensus": o.consensus,
                "rounds": o.rounds,
                "rr": o.rr,
                "body": o.body,
                "artifacts": _artifact_identity(cfg, o),
            },
            ensure_ascii=False,
        )
    )
    tmp.replace(vf)


def _load_verdict(f: Finding, cfg: ConfirmConfig) -> Outcome | None:
    vf = f.fdir / "verdict.json"
    if not vf.is_file():
        return None
    try:
        d = json.loads(vf.read_text())
    except (OSError, ValueError):
        return None
    try:
        if d.get("cache_version") != _CACHE_VERSION or d.get("fingerprint") != _verdict_fingerprint(cfg, f):
            return None
        status = str(d["status"])
        if status not in CANON:
            return None
        _validate_status_source(f, status)
        outcome = Outcome(f, status, bool(d["consensus"]), int(d["rounds"]), str(d["body"]), d.get("rr"))
        if d.get("artifacts") != _artifact_identity(cfg, outcome):
            return None
        return outcome
    except (KeyError, TypeError, ValueError, OSError, ConfirmationFailed):
        return None


def _load_stored_verdict(f: Finding) -> Outcome | None:
    """Load prior terminal evidence without treating it as a reusable verdict.

    Repair mode needs the old disposition and body to keep the cumulative
    report intact even though the committed Phase-3 token deliberately changes
    the current finding's fingerprint. Cache reuse remains exclusively the job
    of :func:`_load_verdict`.
    """
    vf = f.fdir / "verdict.json"
    if not vf.is_file():
        return None
    try:
        data = json.loads(vf.read_text())
        if data.get("cache_version") != _CACHE_VERSION:
            return None
        status = str(data["status"])
        if status not in {*CANON, INCOMPLETE, "DEFERRED"}:
            return None
        _validate_status_source(f, status)
        rr = data.get("rr")
        if rr is not None and not isinstance(rr, str):
            return None
        return Outcome(
            f,
            status,
            bool(data["consensus"]),
            int(data["rounds"]),
            str(data["body"]),
            rr,
        )
    except (KeyError, TypeError, ValueError, OSError, ConfirmationFailed):
        return None


def _rewrite_stored_body(f: Finding, body: str) -> None:
    """Atomically append evidence while leaving the old cache identity stale."""
    vf = f.fdir / "verdict.json"
    data = json.loads(vf.read_text())
    if str(data.get("body", "")) == body:
        return
    data["body"] = body
    tmp = vf.with_suffix(".json.tmp")
    tmp.write_text(json.dumps(data, ensure_ascii=False))
    tmp.replace(vf)


def run_finding_safe(
    cfg: ConfirmConfig,
    f: Finding,
    *,
    prior: Outcome | None = None,
    repair_evidence: str = "",
) -> Outcome:
    """One finding, isolated. A cached terminal verdict short-circuits (idempotent
    retry). A finding that cannot finish — rate limit, infrastructure error, or
    malformed output — is recorded as an INCOMPLETE outcome (error.txt kept for
    diagnosis, and NOT cached so a later retry re-attempts it). It never propagates
    to discard the whole target's report: the rest of the batch still delivers."""
    cached = _load_verdict(f, cfg)
    if cached is not None:
        resumelib.complete_prefix(("confirm", cfg.name, "finding", f.id))
        cfg.release_finding_lease(f.id, force=True)
        _discard_persisted_lease(cfg, f)
        cfg.clear_policy_states(("finding", f.id))
        _log(f"  [{f.id}] cached {cached.status} — skip (idempotent)")
        return cached
    try:
        lease = cfg.acquire_finding_lease(f)
        o = run_finding(cfg, f, _lease=lease)
        if cfg.repair_round is not None:
            o.body = _merge_repair_evidence(prior, repair_evidence, o.body, cfg.repair_round)
        _save_verdict(o, cfg)
        resumelib.complete_prefix(("confirm", cfg.name, "finding", f.id))
        # Reproduction scripts may depend on files or builds in this exact
        # isolated checkout. Keep it as part of the terminal evidence bundle;
        # a later rerun safely replaces it through the stale-worktree path.
        cfg.release_finding_lease(f.id, force=True, retain_worktree=True)
        cfg.clear_policy_states(("finding", f.id))
        return o
    except Exception as exc:  # RateLimited / ConfirmationFailed / anything unexpected
        if not isinstance(exc, RateLimited):
            cfg.release_finding_lease(f.id)
            cfg.clear_policy_states(("finding", f.id))
        try:
            f.fdir.mkdir(parents=True, exist_ok=True)
            (f.fdir / "error.txt").write_text(traceback.format_exc())
        except OSError:
            pass
        failure_code = quota.RATE_LIMIT_RC if isinstance(exc, RateLimited) else 1
        reason = "rate-limited" if isinstance(exc, RateLimited) else str(exc) or type(exc).__name__
        _log(f"  [{f.id}] INCOMPLETE ({reason}) — see {f.fdir / 'error.txt'}; not cached, a retry re-attempts it")
        outcome = Outcome(
            f,
            INCOMPLETE,
            consensus=False,
            rounds=0,
            body=(
                "## Confirmation result\n"
                f"INCOMPLETE — this finding could not be confirmed ({reason}). It was NOT judged; "
                f"see `{f.fdir.name}/error.txt`. Re-run to retry."
            ),
            failure_code=failure_code,
        )
        if cfg.repair_round is not None:
            outcome.body = _merge_repair_evidence(prior, repair_evidence, outcome.body, cfg.repair_round)
        return outcome


# ── RR-NNN allocation (serial) — dispatcher owns the shared queue/lifecycle ──

# A per-finding agent writes only a semantic draft. The dispatcher is the sole
# owner of shared RR ids, lifecycle fields, locations, and append-only History.
_RR_LIFECYCLE_KEYS = {"id", "bug_id", "status", "round", "finding_id", "allocation_key"}
_RR_SEMANTIC_KEYS = {"target", "counterexample", "scope"}
_RR_SCOPE_KEYS = ("actions", "invariants", "hunt_cfgs", "fault_actions")
_RR_TARGET_SCOPE = {
    "SPEC_REPAIR": "actions",
    "FAULT_MODEL": "fault_actions",
    "INVARIANT": "invariants",
}
_RR_CITATION_RE = re.compile(
    r"(?:[A-Za-z0-9_.@/+~-]+\.[A-Za-z0-9]+:\d+|https?://\S+|\b[0-9a-f]{7,40}\b|"
    r"\b(?:issue|pr)\s*#\d+\b|\btests?/[A-Za-z0-9_.@/+~-]+|\btest_[A-Za-z0-9_]+\b)",
    re.IGNORECASE,
)


@dataclass(frozen=True)
class RepairDraft:
    raw: str
    frontmatter: tuple[str, ...]
    payload: str
    target: str
    counterexample: str
    scope: dict[str, tuple[str, ...]]
    trigger: str
    evidence: str
    proposed_change: str


@dataclass(frozen=True)
class TerminalRRSnapshot:
    relative_path: str
    content: bytes
    finding_id: str
    status: str


def _repair_frontmatter(body: str) -> tuple[list[str], str]:
    """Split a strict semantic RR draft into frontmatter and Markdown payload."""
    lines = body.splitlines()
    if not lines or lines[0] != "---":
        raise InvalidRepairRequest("repair draft must start with an exact --- frontmatter fence")
    try:
        end = lines.index("---", 1)
    except ValueError as exc:
        raise InvalidRepairRequest("repair draft is missing its closing --- frontmatter fence") from exc
    if end == 1:
        raise InvalidRepairRequest("repair draft frontmatter is empty")
    return lines[1:end], "\n".join(lines[end + 1 :]).strip()


def _scope_list(value: str, key: str) -> tuple[str, ...]:
    value = value.strip()
    if not (value.startswith("[") and value.endswith("]")):
        raise InvalidRepairRequest(f"repair draft scope.{key} must be a flow-style list")
    inner = value[1:-1].strip()
    if not inner:
        return ()
    result: list[str] = []
    for raw in inner.split(","):
        item = raw.strip()
        if len(item) >= 2 and item[0] == item[-1] and item[0] in {'"', "'"}:
            item = item[1:-1].strip()
        if not item or any(char in item for char in "[]\r\n"):
            raise InvalidRepairRequest(f"repair draft scope.{key} contains an invalid item")
        result.append(item)
    return tuple(result)


def _scope_block_item(value: str, key: str) -> str:
    item = value.strip()
    if len(item) >= 2 and item[0] == item[-1] and item[0] in {'"', "'"}:
        item = item[1:-1].strip()
    if not item or any(char in item for char in "[]\r\n"):
        raise InvalidRepairRequest(f"repair draft scope.{key} contains an invalid item")
    return item


def _safe_rr_path(value: str, field: str) -> None:
    path = Path(value)
    if not value or value == "." or path.is_absolute() or ".." in path.parts or re.match(r"^[A-Za-z]:[\\/]", value):
        raise InvalidRepairRequest(f"repair draft {field} must be a safe relative path")


def _rr_resolved_path(cfg: ConfirmConfig, value: str) -> Path:
    raw = Path(value)
    work_dir = cfg.ws.work_dir(cfg.name)
    base = work_dir if raw.parts and raw.parts[0] == "spec" else work_dir / "spec"
    return (base / raw).resolve()


def _parse_repair_draft(body: str, cfg: ConfirmConfig | None = None, f: Finding | None = None) -> RepairDraft:
    fm_lines, payload = _repair_frontmatter(body)
    top: dict[str, str] = {}
    scope: dict[str, tuple[str, ...]] = {}
    in_scope = False
    index = 0
    while index < len(fm_lines):
        line = fm_lines[index]
        if not line.strip():
            index += 1
            continue
        if line[0].isspace():
            if not in_scope:
                raise InvalidRepairRequest("repair draft has an indented field outside scope")
            match = re.fullmatch(r"\s+([A-Za-z_][A-Za-z0-9_-]*):\s*(.*)", line)
            if match is None:
                raise InvalidRepairRequest("repair draft scope fields must be indented")
            key, value = match.groups()
            if key not in _RR_SCOPE_KEYS:
                raise InvalidRepairRequest(f"repair draft has unknown scope field {key}")
            if key in scope:
                raise InvalidRepairRequest(f"repair draft repeats scope.{key}")
            if value.strip():
                scope[key] = _scope_list(value, key)
                index += 1
                continue
            items: list[str] = []
            index += 1
            while index < len(fm_lines):
                candidate = fm_lines[index]
                if not candidate.strip():
                    index += 1
                    continue
                item_match = re.fullmatch(r"\s+-\s+(.+?)\s*", candidate)
                if item_match is None:
                    break
                items.append(_scope_block_item(item_match.group(1), key))
                index += 1
            scope[key] = tuple(items)
            continue

        match = re.fullmatch(r"([A-Za-z_][A-Za-z0-9_-]*):\s*(.*)", line)
        if match is None:
            raise InvalidRepairRequest(f"repair draft has malformed frontmatter line: {line!r}")
        key, value = match.groups()
        in_scope = key == "scope"
        if key in _RR_LIFECYCLE_KEYS:
            raise InvalidRepairRequest(f"repair draft must not set dispatcher-owned field {key}")
        if key not in _RR_SEMANTIC_KEYS:
            raise InvalidRepairRequest(f"repair draft has unknown frontmatter field {key}")
        if key in top:
            raise InvalidRepairRequest(f"repair draft repeats {key}")
        if key == "scope" and value.strip():
            raise InvalidRepairRequest("repair draft scope must be a mapping")
        top[key] = value.strip()
        index += 1

    missing = sorted(_RR_SEMANTIC_KEYS - top.keys())
    if missing:
        raise InvalidRepairRequest(f"repair draft is missing {', '.join(missing)}")
    missing_scope = sorted(set(_RR_SCOPE_KEYS) - scope.keys())
    if missing_scope:
        raise InvalidRepairRequest(f"repair draft is missing scope.{', scope.'.join(missing_scope)}")

    target = top["target"]
    if target not in _RR_TARGET_SCOPE:
        raise InvalidRepairRequest(f"repair draft has invalid target {target!r}")
    if not scope["hunt_cfgs"]:
        raise InvalidRepairRequest("repair draft scope.hunt_cfgs must not be empty")
    target_scope = _RR_TARGET_SCOPE[target]
    if not scope[target_scope]:
        raise InvalidRepairRequest(f"repair draft target {target} requires non-empty scope.{target_scope}")

    counterexample = top["counterexample"].strip().strip("\"'")
    _safe_rr_path(counterexample, "counterexample")
    for hunt_cfg in scope["hunt_cfgs"]:
        _safe_rr_path(hunt_cfg, "scope.hunt_cfgs")
    if cfg is not None and f is not None:
        expected_counterexample = f.data.get("counterexample")
        if isinstance(expected_counterexample, str) and expected_counterexample.strip():
            _safe_rr_path(expected_counterexample.strip(), "finding counterexample")
            if _rr_resolved_path(cfg, counterexample) != _rr_resolved_path(cfg, expected_counterexample.strip()):
                raise InvalidRepairRequest(
                    f"repair draft counterexample does not match finding {f.id}: {counterexample!r}"
                )

    section_matches = list(re.finditer(r"(?m)^##\s+([^\n]+?)\s*$", payload))
    sections: dict[str, str] = {}
    allowed_sections = {"Trigger", "Evidence", "Proposed change"}
    for index, match in enumerate(section_matches):
        name = match.group(1)
        if name == "History":
            raise InvalidRepairRequest("repair draft must not contain dispatcher-owned History")
        if name not in allowed_sections:
            raise InvalidRepairRequest(f"repair draft has unknown section {name!r}")
        if name in sections:
            raise InvalidRepairRequest(f"repair draft repeats section {name}")
        end = section_matches[index + 1].start() if index + 1 < len(section_matches) else len(payload)
        sections[name] = payload[match.end() : end].strip()
    for required in ("Trigger", "Evidence"):
        if not sections.get(required):
            raise InvalidRepairRequest(f"repair draft is missing non-empty ## {required}")
    if not _RR_CITATION_RE.search(sections["Evidence"]):
        raise InvalidRepairRequest("repair draft Evidence must contain a code, issue, commit, or test citation")
    return RepairDraft(
        body,
        tuple(fm_lines),
        payload,
        target,
        counterexample,
        scope,
        sections["Trigger"],
        sections["Evidence"],
        sections.get("Proposed change", ""),
    )


def _permissive_repair_draft(body: str) -> RepairDraft:
    """Best-effort reader for agent-authored repair text.

    The strict parser remains useful for a correction warning, but formatting or
    schema disagreements must not block a non-empty handoff to the repair agent.
    """
    try:
        return _parse_repair_draft(body)
    except Exception:
        try:
            frontmatter, payload = _repair_frontmatter(body)
        except Exception:
            frontmatter, payload = [], body.strip()

        top: dict[str, str] = {}
        for line in frontmatter:
            match = re.fullmatch(r"([A-Za-z_][A-Za-z0-9_-]*):\s*(.*)", line)
            if match is not None and match.group(1) not in top:
                top[match.group(1)] = match.group(2).strip()
        sections: dict[str, str] = {}
        matches = list(re.finditer(r"(?m)^##\s+([^\n]+?)\s*$", payload))
        for index, match in enumerate(matches):
            end = matches[index + 1].start() if index + 1 < len(matches) else len(payload)
            sections.setdefault(match.group(1), payload[match.end() : end].strip())
        return RepairDraft(
            body,
            tuple(frontmatter),
            payload,
            top.get("target", ""),
            top.get("counterexample", "").strip("\"'"),
            {},
            sections.get("Trigger", ""),
            sections.get("Evidence", ""),
            sections.get("Proposed change", ""),
        )


def _repair_semantic_parts(draft: RepairDraft) -> tuple[list[str], str]:
    frontmatter: list[str] = []
    for line in draft.frontmatter:
        match = re.fullmatch(r"([A-Za-z_][A-Za-z0-9_-]*):\s*(.*)", line)
        if match is not None and match.group(1) in _RR_LIFECYCLE_KEYS:
            continue
        frontmatter.append(line)
    payload = draft.payload
    history = re.search(r"(?m)^##\s+History\s*$", payload)
    if history is not None:
        payload = payload[: history.start()].rstrip()
    return frontmatter, payload.strip()


def _repair_semantic_text(draft: RepairDraft) -> str:
    frontmatter, payload = _repair_semantic_parts(draft)
    if frontmatter:
        head = "\n".join(frontmatter)
        return f"---\n{head}\n---\n\n{payload}".strip()
    return payload.strip()


def _repair_allocation_key(cfg: ConfirmConfig, finding_id: str, draft: RepairDraft) -> str:
    """Stable identity without requiring the agent payload to match a schema."""
    del cfg
    return _digest({"finding_id": finding_id, "draft": _repair_semantic_text(draft)})


def _repair_draft_from_request(text: str) -> RepairDraft:
    """Recover agent-authored content from a published RR.

    This lets workspaces written by the earlier allocation-key algorithm retain
    an unchanged DEFERRED request after upgrading: the raw handoff, excluding
    dispatcher lifecycle and History, decides equality.
    """
    return _permissive_repair_draft(_repair_semantic_text(_permissive_repair_draft(text)))


def _read_repair_draft(cfg: ConfirmConfig, f: Finding) -> RepairDraft:
    path = f.fdir / "repair-request.body.md"
    if path.is_symlink() or not path.is_file():
        raise InvalidRepairRequest(f"{f.id}: PENDING REPAIR requires repair-request.body.md")
    try:
        body = path.read_text()
    except (OSError, UnicodeError) as exc:
        raise InvalidRepairRequest(f"{f.id}: cannot read repair-request.body.md: {exc}") from exc
    if not body.strip():
        raise InvalidRepairRequest(f"{f.id}: repair-request.body.md is empty")
    return _permissive_repair_draft(body)


def _merge_rr(
    rid: str,
    bug_id: str,
    cx_fallback: str,
    body: str,
    *,
    finding_id: str,
    allocation_key: str = "",
    status: str = "OPEN",
    round_: int = 0,
    history: list[str] | None = None,
) -> str:
    """Wrap a non-empty agent draft with dispatcher-owned lifecycle fields."""
    del cx_fallback
    if not finding_id or set(finding_id) - ID_CHARS or finding_id in {".", ".."}:
        raise InvalidRepairRequest(f"invalid stable finding_id {finding_id!r}")
    draft = _permissive_repair_draft(body)
    lifecycle = f"id: {rid}\nfinding_id: {finding_id}\nbug_id: {bug_id}\nstatus: {status}\nround: {round_}\n"
    if allocation_key:
        lifecycle += f"allocation_key: {allocation_key}\n"
    entries = list(history or [f"- r{round_} (phase4-confirm): created from {finding_id}"])
    semantic_frontmatter, payload = _repair_semantic_parts(draft)
    semantic_text = "\n".join(semantic_frontmatter)
    if semantic_text:
        semantic_text += "\n"
    history_text = "\n".join(entries)
    return f"---\n{lifecycle}{semantic_text}---\n\n{payload}\n\n## History\n{history_text}\n"


def _rr_history(text: str, round_: int) -> list[str]:
    match = re.search(r"(?m)^##\s+History\s*$", text)
    if match is None:
        return [f"- r{round_} (phase4-confirm): imported legacy request without dispatcher History"]
    history = text[match.end() :].strip()
    return history.splitlines() if history else []


def _concise_evidence(value: str, limit: int = 600) -> str:
    compact = re.sub(r"\s+", " ", value).strip()
    if len(compact) <= limit:
        return compact
    return compact[: limit - 1].rstrip() + "…"


def _load_repair_commit(cfg: ConfirmConfig) -> dict[str, Any]:
    """Verify the exact durable Phase-3 result selected by the pipeline."""
    assert cfg.repair_round is not None
    marker = cfg.ws.work_dir(cfg.name) / "spec" / ".repair-phase3-commit.json"
    if marker.is_symlink() or not marker.is_file():
        raise ConfirmationFailed("repair confirmation requires a safe .repair-phase3-commit.json")
    try:
        doc = json.loads(marker.read_text())
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise ConfirmationFailed(f"invalid repair Phase-3 commit marker: {exc}") from exc
    if not isinstance(doc, dict) or doc.get("version") != 2:
        raise ConfirmationFailed("repair Phase-3 commit marker must use version 2")
    if doc.get("repair_round") != cfg.repair_round:
        raise ConfirmationFailed("repair Phase-3 commit marker has the wrong repair round")
    if (
        not cfg.repair_token
        or re.fullmatch(r"[0-9a-f]{32}", cfg.repair_token) is None
        or doc.get("commit_token") != cfg.repair_token
    ):
        raise ConfirmationFailed("repair Phase-3 commit marker has the wrong commit token")

    request_ids = doc.get("request_ids")
    violation_ids = doc.get("violation_ids")
    findings_json = doc.get("findings_json")
    if (
        not isinstance(request_ids, list)
        or not all(isinstance(value, str) and re.fullmatch(r"RR-\d+", value) for value in request_ids)
        or len(set(request_ids)) != len(request_ids)
        or not isinstance(violation_ids, list)
        or not all(
            isinstance(value, str)
            and value.startswith("MC-")
            and not (set(value) - ID_CHARS)
            and value not in {".", ".."}
            for value in violation_ids
        )
        or len(set(violation_ids)) != len(violation_ids)
        or not isinstance(findings_json, str)
    ):
        raise ConfirmationFailed("repair Phase-3 commit marker has invalid request or violation ids")
    try:
        snapshot = json.loads(findings_json)
    except json.JSONDecodeError as exc:
        raise ConfirmationFailed(f"repair Phase-3 findings snapshot is invalid: {exc}") from exc
    snapshot_findings = snapshot.get("findings") if isinstance(snapshot, dict) else None
    snapshot_ids = (
        [finding.get("id") for finding in snapshot_findings if isinstance(finding, dict)]
        if isinstance(snapshot_findings, list)
        else None
    )
    if snapshot_ids != violation_ids:
        raise ConfirmationFailed("repair Phase-3 violation ids do not match its findings snapshot")
    live = cfg.ws.work_dir(cfg.name) / "spec" / "findings.json"
    if live.is_symlink() or not live.is_file() or live.read_text() != findings_json:
        raise ConfirmationFailed("live findings.json diverges from the committed Phase-3 snapshot")
    return doc


def _repair_round_requests(
    cfg: ConfirmConfig,
    request_ids: list[str],
) -> dict[str, tuple[str, str]]:
    """Return this round's consumed RR id and newest Phase-3 History entry."""
    if cfg.repair_round is None:
        return {}
    rr_dir = cfg.ws.work_dir(cfg.name) / "spec" / "repair-requests"
    if request_ids and (not rr_dir.is_dir() or rr_dir.is_symlink()):
        raise InvalidRepairRequest("repair commit references requests but repair-requests is missing or unsafe")
    result: dict[str, tuple[str, str]] = {}
    for rid in request_ids:
        path = rr_dir / f"{rid}.md"
        if path.is_symlink() or not path.is_file():
            raise InvalidRepairRequest(f"repair request {path.name} must be a safe regular file")
        text = path.read_text(errors="replace")
        statuses = _rr_field_text(text, "status")
        finding_ids = _rr_field_text(text, "finding_id")
        ids = _rr_field_text(text, "id")
        if statuses != ["CONSUMED"] or ids != [rid] or len(finding_ids) != 1:
            raise InvalidRepairRequest(f"repair request {path.name} has invalid repair-round identity")
        finding_id = finding_ids[0]
        if finding_id in result:
            raise InvalidRepairRequest(
                f"repair round {cfg.repair_round} has multiple consumed requests for {finding_id}"
            )
        history = [line for line in _rr_history(text, cfg.repair_round) if line.strip()]
        newest = _concise_evidence(history[-1].lstrip("- ").strip()) if history else "repair completed"
        result[finding_id] = (ids[0], newest)
    return result


def _repair_evidence(
    cfg: ConfirmConfig,
    f: Finding,
    requests: dict[str, tuple[str, str]],
    *,
    current_violation: bool,
) -> str:
    assert cfg.repair_round is not None
    lines = [f"## Repair round {cfg.repair_round} evidence"]
    if cfg.repair_token:
        # The visible round counter restarts with a new pipeline invocation.
        # This durable identity keeps an exact retry idempotent without
        # suppressing a later repair that happens to display the same round.
        lines.append(f"<!-- specula-repair-token: {cfg.repair_token} -->")
    request = requests.get(f.id)
    if request is not None:
        rid, history = request
        request_path = cfg.ws.work_dir(cfg.name).absolute() / "spec" / "repair-requests" / f"{rid}.md"
        lines.append(f"- **Repair request**: `{request_path}`")
        if current_violation:
            lines.append("  Read its updated `## Evidence` before confirming the current violation.")
        lines.append(f"- **Phase 3 result**: {history}")
    if current_violation:
        summary = f.data.get("summary")
        if isinstance(summary, str) and summary.strip():
            lines.append(f"- **Current violation analysis**: {_concise_evidence(summary)}")
        counterexample = f.data.get("counterexample")
        if isinstance(counterexample, str) and counterexample.strip():
            lines.append(f"- **Counterexample**: `{counterexample.strip()}`")
    return "\n".join(lines)


def _repair_prompt_context(
    f: Finding,
    prior: Outcome | None,
    repair_evidence: str,
) -> str:
    """Tell a scoped worker to continue, rather than rediscover, its evidence."""
    lines = [
        "## Repair-loop evidence continuation",
        "",
        "This is not a fresh confirmation. Use the existing evidence and the current",
        "Phase 3 conformance result below. Do not repeat already-established work.",
        "Preserve correct evidence; if current source/trace evidence disproves a prior",
        "statement, explicitly correct that statement in your updated analysis.",
    ]
    if prior is not None:
        lines.extend(
            [
                "",
                f"- Existing disposition: `{prior.status}`" + (f" (`{prior.rr}`)" if prior.rr is not None else ""),
                f"- Existing evidence: `{f.fdir.absolute() / 'verdict.json'}`",
                "  Read this finding's `body` before investigating further.",
            ]
        )
    lines.extend(["", repair_evidence])
    return "\n".join(lines)


def _merge_repair_evidence(
    prior: Outcome | None,
    repair_evidence: str,
    current_body: str | None,
    repair_round: int,
) -> str:
    """Continue the existing evidence body with one concise repair update."""
    token_marker = re.search(r"<!-- specula-repair-token: [0-9a-f]{32} -->", repair_evidence)
    marker = token_marker.group(0) if token_marker is not None else f"## Repair round {repair_round} evidence"
    parts: list[str] = []
    if prior is not None and prior.body.strip():
        parts.append(prior.body.strip())
    if repair_evidence.strip() and not any(marker in part for part in parts):
        parts.append(repair_evidence.strip())
    if current_body is not None and current_body.strip():
        parts.append(f"## Phase 4 confirmation after repair round {repair_round}\n\n{current_body.strip()}")
    return "\n\n".join(parts)


def _prior_attempt_history(finding_id: str, records: list[tuple[str, Path, str, str, str]]) -> list[str]:
    """Seed a fresh request's History with the finding's terminal predecessors.

    A surviving finding re-enters repair as a new OPEN request; Phase 3 only
    reads that request, so without this thread it never learns what earlier
    rounds tried. One bullet per terminal record quotes its newest History
    line so a repair recorded as failed is never silently repeated.
    """
    entries = [f"- r0 (phase4-confirm): created from {finding_id}"]
    for rid, _path, text, status, _key in sorted(records, key=lambda record: record[0]):
        bullets = _rr_history(text, 0)
        last = bullets[-1].lstrip("- ").strip() if bullets else "no recorded History"
        entries.append(f"- r0 (phase4-confirm): prior attempt {rid} ({status}): {last}")
    return entries


def _atomic_replace_rr(path: Path, text: str) -> None:
    tmp = path.with_name(f".{path.name}.{os.getpid()}.{threading.get_ident()}.{secrets.token_hex(4)}.tmp")
    try:
        with tmp.open("x") as fh:
            fh.write(text)
            fh.flush()
            os.fsync(fh.fileno())
        os.replace(tmp, path)
    finally:
        tmp.unlink(missing_ok=True)


def _atomic_create_rr(path: Path, text: str) -> None:
    """Publish one complete RR without ever exposing a partial final path."""
    tmp = path.with_name(f".{path.name}.{os.getpid()}.{threading.get_ident()}.{secrets.token_hex(4)}.tmp")
    try:
        with tmp.open("x") as fh:
            fh.write(text)
            fh.flush()
            os.fsync(fh.fileno())
        os.link(tmp, path)
    finally:
        tmp.unlink(missing_ok=True)


_REPORT_RR_ROW_RE = re.compile(
    r"(?m)^\|\s*(\d+)\s*\|\s*([^|\s]+)\s*\|\s*([^|]+?)\s*\|"
    r"(?:\s*[^|]*\s*\|)?\s*$"
)
_REPORT_DETAIL_RE = re.compile(r"(?m)^##\s+(?:Bug|Entry)\s+(\d+)\s*:")
_REPORT_STATUS_FIELD_RE = re.compile(r"^\s*-\s*\*\*Status\*\*:", re.I)


def _report_repair_status_key(status: str, rid: str) -> str | None:
    status = status.strip()
    if status in {"PENDING REPAIR", f"PENDING REPAIR ({rid})"}:
        return "PENDING REPAIR"
    if status in {"DEFERRED", f"DEFERRED (repair loop exhausted; {rid} in deferred/)"}:
        return "DEFERRED"
    return None


def _legacy_rr_report_identity(
    cfg: ConfirmConfig,
    rid: str,
    *,
    require_reference: bool = True,
) -> tuple[str, str] | None:
    """Prove the stable identity of a pre-``finding_id`` legacy request.

    The stored ``bug_id`` is deliberately ignored: ``Bug N`` is only a display
    label and may already be stale after candidates were reordered. The report
    is accepted only when its RR-bearing table row and matching detail section
    independently name the same stable Finding ID. Anything less fails closed
    so switching confirmation modes cannot silently create a duplicate OPEN.
    """
    report = cfg.ws.work_dir(cfg.name) / "confirmed-bugs.md"
    if report.is_symlink():
        raise InvalidRepairRequest(f"cannot migrate legacy repair {rid}: confirmed-bugs.md is missing or unsafe")
    if not report.is_file():
        if not require_reference:
            return None
        raise InvalidRepairRequest(f"cannot migrate legacy repair {rid}: confirmed-bugs.md is missing or unsafe")
    text = report.read_text()
    rows: list[tuple[int, str]] = []
    for match in _REPORT_RR_ROW_RE.finditer(text):
        rr_refs = re.findall(r"\bRR-\d+\b", match.group(3))
        if rid in rr_refs:
            rows.append((int(match.group(1)), match.group(2)))
    if not rows and not require_reference:
        return None
    if len(rows) != 1:
        raise InvalidRepairRequest(
            f"cannot migrate legacy repair {rid}: expected exactly one RR-bearing report row, found {len(rows)}"
        )
    bug_no, finding_id = rows[0]
    if not finding_id or set(finding_id) - ID_CHARS or finding_id in {".", ".."}:
        raise InvalidRepairRequest(f"cannot migrate legacy repair {rid}: unsafe finding id {finding_id!r}")

    details = list(_REPORT_DETAIL_RE.finditer(text))
    detail_ids: list[str] = []
    for index, match in enumerate(details):
        if int(match.group(1)) != bug_no:
            continue
        end = details[index + 1].start() if index + 1 < len(details) else len(text)
        detail_ids.extend(re.findall(r"(?m)^- \*\*Finding ID\*\*:\s*([^\s]+)\s*$", text[match.end() : end]))
    if detail_ids != [finding_id]:
        raise InvalidRepairRequest(
            f"cannot migrate legacy repair {rid}: report detail does not prove finding_id {finding_id}"
        )
    if sum(1 for match in _REPORT_RR_ROW_RE.finditer(text) if match.group(2) == finding_id) != 1:
        raise InvalidRepairRequest(
            f"cannot migrate legacy repair {rid}: finding_id {finding_id} is not unique in the report"
        )
    return finding_id, f"Bug {bug_no}"


def _rr_with_identity_fields(text: str, finding_id: str, allocation_key: str, bug_id: str | None) -> str:
    """Add missing dispatcher identity fields without changing semantic payload."""
    lines = text.splitlines()
    if not lines or lines[0] != "---":
        raise InvalidRepairRequest("legacy repair request is missing fenced frontmatter")
    try:
        end = lines.index("---", 1)
    except ValueError as exc:
        raise InvalidRepairRequest("legacy repair request is missing its closing frontmatter fence") from exc
    insert_at = next((i + 1 for i, line in enumerate(lines[1:end], 1) if line.startswith("id:")), 1)
    if not _rr_field_text(text, "finding_id"):
        lines.insert(insert_at, f"finding_id: {finding_id}")
        end += 1
        insert_at += 1
    if not _rr_field_text(text, "allocation_key"):
        lines.insert(insert_at, f"allocation_key: {allocation_key}")
        end += 1
    if bug_id is not None and _rr_field_text(text, "bug_id") != [bug_id]:
        bug_indexes = [i for i, line in enumerate(lines[1:end], 1) if line.startswith("bug_id:")]
        if len(bug_indexes) != 1:
            raise InvalidRepairRequest("legacy repair request has invalid bug_id")
        lines[bug_indexes[0]] = f"bug_id: {bug_id}"
    return "\n".join(lines) + "\n"


def _ensure_rr_stable_identities(
    cfg: ConfirmConfig,
    rr_dir: Path,
    *,
    verify_against_report: bool = False,
    require_active_report_link: bool = False,
) -> None:
    """Normalize legacy RRs before any identity lookup or new allocation."""
    active_by_finding: dict[str, list[str]] = {}
    for path in sorted(rr_dir.rglob("RR-*.md")):
        if path.is_symlink():
            raise InvalidRepairRequest(f"repair request {path.name} must not be a symlink")
        text = path.read_text()
        ids = _rr_field_text(text, "id")
        bug_ids = _rr_field_text(text, "bug_id")
        finding_ids = _rr_field_text(text, "finding_id")
        keys = _rr_field_text(text, "allocation_key")
        statuses = _rr_field_text(text, "status")
        if ids != [path.stem] or len(bug_ids) != 1:
            raise InvalidRepairRequest(f"repair request {path.name} has invalid legacy identity fields")
        if len(finding_ids) > 1 or len(keys) > 1:
            raise InvalidRepairRequest(f"repair request {path.name} repeats a stable identity field")
        if len(statuses) != 1 or statuses[0] not in {"OPEN", "IN_REPAIR", "CONSUMED", "DEFERRED"}:
            raise InvalidRepairRequest(f"repair request {path.name} has invalid status")
        report_identity = None
        if not finding_ids:
            report_identity = _legacy_rr_report_identity(cfg, ids[0])
        elif verify_against_report:
            report_identity = _legacy_rr_report_identity(
                cfg,
                ids[0],
                require_reference=False,
            )
            if report_identity is None and require_active_report_link and statuses[0] in {"OPEN", "IN_REPAIR"}:
                raise InvalidRepairRequest(
                    f"repair request {ids[0]} is {statuses[0]} but is not linked from confirmed-bugs.md"
                )
        reported_finding_id = report_identity[0] if report_identity is not None else None
        reported_bug_id = (
            report_identity[1] if report_identity is not None and statuses[0] in {"OPEN", "IN_REPAIR"} else None
        )
        if finding_ids and reported_finding_id is not None and finding_ids[0] != reported_finding_id:
            raise InvalidRepairRequest(
                f"repair request {ids[0]} finding_id {finding_ids[0]!r} conflicts with report identity "
                f"{reported_finding_id!r}"
            )
        if finding_ids:
            finding_id = finding_ids[0]
        else:
            assert reported_finding_id is not None
            finding_id = reported_finding_id
        if not finding_id or set(finding_id) - ID_CHARS or finding_id in {".", ".."}:
            raise InvalidRepairRequest(f"repair request {path.name} has invalid finding_id")
        expected_parent = rr_dir / "deferred" if statuses[0] == "DEFERRED" else rr_dir
        if path.parent != expected_parent:
            raise InvalidRepairRequest(f"repair request {ids[0]} has invalid location for status {statuses[0]}")
        if statuses[0] in {"OPEN", "IN_REPAIR"}:
            active_by_finding.setdefault(finding_id, []).append(ids[0])
        bug_id_changed = reported_bug_id is not None and bug_ids != [reported_bug_id]
        if keys and finding_ids and not bug_id_changed:
            continue
        try:
            allocation_key = (
                keys[0] if keys else _repair_allocation_key(cfg, finding_id, _repair_draft_from_request(text))
            )
        except InvalidRepairRequest as exc:
            raise InvalidRepairRequest(
                f"cannot migrate legacy repair {ids[0]}: semantic request is invalid ({exc})"
            ) from exc
        migrated = _rr_with_identity_fields(text, finding_id, allocation_key, reported_bug_id)
        _atomic_replace_rr(path, migrated)
    duplicates = {finding_id: rids for finding_id, rids in active_by_finding.items() if len(rids) > 1}
    if duplicates:
        finding_id, rids = next(iter(duplicates.items()))
        raise InvalidRepairRequest(
            f"finding_id {finding_id} has multiple active repair requests: {', '.join(sorted(rids))}"
        )


def validate_report_repair_references(cfg: ConfirmConfig) -> None:
    """Validate canonical report links against RR location and lifecycle state."""
    report = cfg.ws.work_dir(cfg.name) / "confirmed-bugs.md"
    if report.is_symlink() or not report.is_file():
        raise InvalidRepairRequest("confirmed-bugs.md is missing or unsafe")
    text = report.read_text()
    rr_dir = cfg.ws.work_dir(cfg.name) / "spec" / "repair-requests"
    details = list(_REPORT_DETAIL_RE.finditer(text))
    seen: set[str] = set()
    for row in _REPORT_RR_ROW_RE.finditer(text):
        bug_no = int(row.group(1))
        rendered_status = row.group(3).strip()
        pending = re.fullmatch(r"PENDING REPAIR \((RR-\d+)\)", rendered_status)
        deferred = re.fullmatch(r"DEFERRED \(repair loop exhausted; (RR-\d+) in deferred/\)", rendered_status)
        refs = re.findall(r"\bRR-\d+\b", rendered_status)
        if pending is None and deferred is None:
            if refs or rendered_status.startswith(("PENDING REPAIR", "DEFERRED")):
                raise InvalidRepairRequest(
                    f"report Entry {bug_no} has an RR reference with invalid status {rendered_status!r}"
                )
            continue
        match = pending or deferred
        assert match is not None
        rid = match.group(1)
        if refs != [rid] or rid in seen:
            raise InvalidRepairRequest(f"report repair reference {rid} is not unique")
        seen.add(rid)

        detail_statuses: list[str] = []
        for index, detail in enumerate(details):
            if int(detail.group(1)) != bug_no:
                continue
            end = details[index + 1].start() if index + 1 < len(details) else len(text)
            detail_statuses.extend(re.findall(r"(?m)^- \*\*Status\*\*:\s*(.+?)\s*$", text[detail.end() : end]))
        rendered_key = _report_repair_status_key(rendered_status, rid)
        if not detail_statuses or any(
            _report_repair_status_key(status, rid) != rendered_key for status in detail_statuses
        ):
            raise InvalidRepairRequest(f"report Entry {bug_no} table/detail repair status is inconsistent")

        matches = list(rr_dir.rglob(f"{rid}.md")) if rr_dir.is_dir() and not rr_dir.is_symlink() else []
        if len(matches) != 1:
            raise InvalidRepairRequest(f"report repair reference {rid} resolves to {len(matches)} files")
        expected_path = rr_dir / f"{rid}.md"
        expected_status = "OPEN"
        if deferred is not None:
            expected_path = rr_dir / "deferred" / f"{rid}.md"
            expected_status = "DEFERRED"
        path = matches[0]
        if path != expected_path or path.is_symlink():
            raise InvalidRepairRequest(f"report repair reference {rid} must be {expected_path.relative_to(rr_dir)}")
        statuses = _rr_field_text(path.read_text(), "status")
        if statuses != [expected_status]:
            raise InvalidRepairRequest(
                f"report repair reference {rid} requires status {expected_status}, found "
                f"{statuses[0] if len(statuses) == 1 else '<invalid>'}"
            )


def snapshot_terminal_rr_audit(cfg: ConfirmConfig) -> dict[str, TerminalRRSnapshot]:
    """Capture terminal bytes and active identity after identity preflight."""
    rr_dir = cfg.ws.work_dir(cfg.name) / "spec" / "repair-requests"
    if not rr_dir.is_dir() or rr_dir.is_symlink():
        return {}
    snapshot: dict[str, TerminalRRSnapshot] = {}
    for path in sorted(rr_dir.rglob("RR-*.md")):
        text = path.read_text()
        statuses = _rr_field_text(text, "status")
        ids = _rr_field_text(text, "id")
        finding_ids = _rr_field_text(text, "finding_id")
        if len(ids) != 1 or len(finding_ids) != 1 or len(statuses) != 1 or ids[0] in snapshot:
            raise InvalidRepairRequest(f"repair audit {path.name} has a duplicate or invalid identity")
        snapshot[ids[0]] = TerminalRRSnapshot(
            str(path.relative_to(rr_dir)),
            path.read_bytes(),
            finding_ids[0],
            statuses[0],
        )
    return snapshot


def _atomic_replace_rr_bytes(path: Path, content: bytes) -> None:
    tmp = path.with_name(f".{path.name}.{os.getpid()}.{threading.get_ident()}.{secrets.token_hex(4)}.tmp")
    try:
        with tmp.open("xb") as fh:
            fh.write(content)
            fh.flush()
            os.fsync(fh.fileno())
        os.replace(tmp, path)
    finally:
        tmp.unlink(missing_ok=True)


def _remove_rr_path(path: Path) -> None:
    if path.is_symlink() or path.is_file():
        path.unlink(missing_ok=True)
    elif path.exists():
        shutil.rmtree(path)


def restore_terminal_rr_audit(
    cfg: ConfirmConfig,
    snapshot: dict[str, TerminalRRSnapshot],
) -> list[str]:
    """Restore terminal paths/bytes and report every attempted mutation."""
    if not snapshot:
        return []
    rr_dir = cfg.ws.work_dir(cfg.name) / "spec" / "repair-requests"
    if rr_dir.is_symlink() or (rr_dir.exists() and not rr_dir.is_dir()):
        _remove_rr_path(rr_dir)
    rr_dir.mkdir(parents=True, exist_ok=True)
    violations: list[str] = []
    for rid, saved in snapshot.items():
        expected = rr_dir / saved.relative_path
        changed = False
        for path in list(rr_dir.rglob(f"{rid}.md")):
            if path != expected:
                _remove_rr_path(path)
                changed = True
        if expected.parent.is_symlink() or (expected.parent.exists() and not expected.parent.is_dir()):
            _remove_rr_path(expected.parent)
        expected.parent.mkdir(parents=True, exist_ok=True)
        current = None
        current_identity: tuple[list[str], list[str], list[str]] | None = None
        if expected.is_file() and not expected.is_symlink():
            current = expected.read_bytes()
            text = current.decode(errors="replace")
            current_identity = (
                _rr_field_text(text, "id"),
                _rr_field_text(text, "finding_id"),
                _rr_field_text(text, "status"),
            )
        expected_identity = ([rid], [saved.finding_id], [saved.status])
        terminal_changed = saved.status in {"CONSUMED", "DEFERRED"} and current != saved.content
        active_identity_changed = saved.status in {"OPEN", "IN_REPAIR"} and current_identity != expected_identity
        if terminal_changed or active_identity_changed:
            if expected.exists() and expected.is_dir() and not expected.is_symlink():
                shutil.rmtree(expected)
            _atomic_replace_rr_bytes(expected, saved.content)
            changed = True
        if changed:
            kind = "terminal audit" if saved.status in {"CONSUMED", "DEFERRED"} else "active identity"
            violations.append(f"{rid} {kind} was modified, moved, or deleted and was restored")
    return violations


def ensure_rr_stable_identities(
    cfg: ConfirmConfig,
    *,
    verify_against_report: bool = False,
    require_active_report_link: bool = False,
) -> None:
    """Validate/migrate every RR before legacy output or parallel reuse.

    The legacy Phase-4 launcher calls this after its agent exits; the parallel
    allocator calls it before looking up an existing request.  Keeping the same
    fail-closed implementation on both paths makes switching modes safe.
    """
    rr_dir = cfg.ws.work_dir(cfg.name) / "spec" / "repair-requests"
    if not rr_dir.exists():
        return
    if rr_dir.is_symlink() or not rr_dir.is_dir():
        raise InvalidRepairRequest("repair-requests must be a real directory")
    with _rr_lock:
        _ensure_rr_stable_identities(
            cfg,
            rr_dir,
            verify_against_report=verify_against_report,
            require_active_report_link=require_active_report_link,
        )


def allocate_rr(cfg: ConfirmConfig, o: Outcome) -> str:
    """Serially assign the next RR-NNN and file the agent-authored request."""
    draft = _read_repair_draft(cfg, o.finding)
    body = draft.raw
    rr_dir = cfg.ws.work_dir(cfg.name) / "spec" / "repair-requests"
    with _rr_lock:
        rr_dir.mkdir(parents=True, exist_ok=True)
        ensure_rr_stable_identities(cfg)
        # Confirmation generation, repo identity, adapter, and prompts decide
        # whether Phase 4 must run again; they do not by themselves describe a
        # different repair. Terminal DEFERRED requests reopen only when this
        # finding's raw handoff changes.
        allocation_key = _repair_allocation_key(cfg, o.finding.id, draft)
        records: list[tuple[str, Path, str, str, str]] = []
        for path in rr_dir.rglob("RR-*.md"):
            text = path.read_text(errors="replace")
            keys = _rr_field_text(text, "allocation_key")
            statuses = _rr_field_text(text, "status")
            ids = _rr_field_text(text, "id")
            finding_ids = _rr_field_text(text, "finding_id")
            same_finding = o.finding.id in finding_ids
            same_allocation = allocation_key in keys
            if not same_finding and not same_allocation:
                continue
            if same_allocation and not same_finding:
                raise InvalidRepairRequest(f"existing allocation key has wrong finding_id for {o.finding.id}")
            if path.is_symlink():
                raise InvalidRepairRequest(f"existing allocation for {o.finding.id} must not be a symlink")
            if finding_ids != [o.finding.id]:
                raise InvalidRepairRequest(f"existing allocation for {o.finding.id} has invalid finding_id")
            if len(keys) != 1:
                raise InvalidRepairRequest(f"existing allocation for {o.finding.id} has invalid allocation_key")
            status = statuses[0] if len(statuses) == 1 else ""
            if status not in {"OPEN", "IN_REPAIR", "DEFERRED", "CONSUMED"}:
                raise InvalidRepairRequest(
                    f"existing repair request for {o.finding.id} has invalid status {status or '<missing>'}"
                )
            if len(ids) != 1 or path.name != f"{ids[0]}.md":
                raise InvalidRepairRequest(f"existing allocation for {o.finding.id} has inconsistent id")
            expected_parent = rr_dir / "deferred" if status == "DEFERRED" else rr_dir
            if path.parent != expected_parent:
                raise InvalidRepairRequest(
                    f"existing allocation for {o.finding.id} has invalid location for status {status}"
                )
            rounds = _rr_field_text(text, "round")
            if len(rounds) != 1 or not rounds[0].isdigit():
                raise InvalidRepairRequest(f"existing allocation for {o.finding.id} has invalid round")
            try:
                existing_key = _repair_allocation_key(cfg, o.finding.id, _repair_draft_from_request(text))
            except InvalidRepairRequest:
                # A malformed body cannot prove semantic equality. OPEN will be
                # refreshed from the valid draft; DEFERRED remains immutable and
                # a new OPEN id is allocated.
                existing_key = ""
            records.append((ids[0], path, text, status, existing_key))

        active = [record for record in records if record[3] in {"OPEN", "IN_REPAIR"}]
        if len(active) > 1:
            raise InvalidRepairRequest(f"multiple active repair requests already exist for {o.finding.id}")
        if active:
            rid, path, text, status, old_key = active[0]
            if status == "IN_REPAIR":
                raise InvalidRepairRequest(
                    f"existing repair request {rid} for {o.finding.id} is IN_REPAIR and cannot be refreshed"
                )
            current_bug_ids = _rr_field_text(text, "bug_id")
            if len(current_bug_ids) != 1:
                raise InvalidRepairRequest(f"existing repair request {rid} has invalid bug_id")
            expected_bug_id = f"Bug {o.bug_no}" if o.bug_no > 0 else current_bug_ids[0]
            bug_changed = current_bug_ids != [expected_bug_id]
            semantic_changed = old_key != allocation_key
            if semantic_changed or bug_changed:
                round_ = int(_rr_field_text(text, "round")[0])
                history = _rr_history(text, round_)
                if semantic_changed:
                    history.append(f"- r{round_} (phase4-confirm): refreshed semantic payload for {o.finding.id}")
                updated = _merge_rr(
                    rid,
                    expected_bug_id,
                    str(o.finding.data.get("counterexample") or ""),
                    body,
                    finding_id=o.finding.id,
                    allocation_key=allocation_key,
                    status="OPEN",
                    round_=round_,
                    history=history,
                )
                _atomic_replace_rr(path, updated)
            return rid

        exact_deferred = [record for record in records if record[3] == "DEFERRED" and record[4] == allocation_key]
        if len(exact_deferred) > 1:
            raise InvalidRepairRequest(f"multiple deferred allocations match {o.finding.id}")
        if exact_deferred:
            return exact_deferred[0][0]

        nums = [int(m.group(1)) for p in rr_dir.rglob("RR-*.md") if (m := re.fullmatch(r"RR-(\d+)\.md", p.name))]
        next_num = max(nums, default=0) + 1
        cx = str(o.finding.data.get("counterexample") or "")
        # bug_id is the legacy report display label used by the RR ledger;
        # finding_id separately preserves the stable raw id.
        rid = f"RR-{next_num:03d}"
        merged = _merge_rr(
            rid,
            f"Bug {o.bug_no}",
            cx,
            body,
            finding_id=o.finding.id,
            allocation_key=allocation_key,
            history=_prior_attempt_history(o.finding.id, records) if records else None,
        )
        try:
            # Final guard against an external writer racing the in-process
            # lock. The hard-link publish is atomic and non-overwriting, so
            # readers never observe an empty/partial final RR.
            _atomic_create_rr(rr_dir / f"{rid}.md", merged)
        except FileExistsError:
            # Another dispatcher won the cross-process publish race. Rescan its
            # complete file before choosing/reusing an id; blindly incrementing
            # could create two active requests for one finding.
            return allocate_rr(cfg, o)
    return rid


# ── step 0: consolidate + dedup the two finding sources into candidates.json ──


def _scenario_refs(value: Any) -> set[str]:
    if isinstance(value, int):
        return {f"Scenario {value}"}
    if not isinstance(value, str):
        return set()
    if value.strip().isdigit():
        return {f"Scenario {int(value.strip())}"}
    return {f"Scenario {number}" for number in re.findall(r"\bScenario\s+(\d+)\b", value, re.I)}


def _validate_candidates(
    path: Path,
    expected_mc_ids: set[str] | dict[str, dict[str, Any]] | None = None,
    expected_scenarios: set[str] | None = None,
) -> list[str]:
    """Structural-minimum validation of candidates.json: only what would break
    the per-finding fan-out (unusable id, id collision, unroutable source). The
    stricter completeness / scenario-dedup / MC-immutability checks were removed on
    purpose — they only fail-closed (withhold) an otherwise-runnable batch without
    improving any verdict, and rejected sound consolidations (a scenario partly
    absorbed into an MC candidate while its distinct-site residual is emitted as a
    CR candidate is legitimate). Per-finding confirmation tolerates imperfect
    input; a weak candidate surfaces there, not as a whole-batch stop."""
    del expected_mc_ids, expected_scenarios  # intentionally no longer enforced
    errs: list[str] = []
    try:
        doc = json.loads(path.read_text())
    except (OSError, ValueError) as e:
        return [f"not valid JSON: {e}"]
    if not isinstance(doc, dict):
        return ["top level is not an object"]
    findings = doc.get("findings")
    if not isinstance(findings, list):
        return ["'findings' missing or not a list"]
    seen: set[str] = set()
    for i, f in enumerate(findings):
        where = f"findings[{i}]"
        if not isinstance(f, dict):
            errs.append(f"{where}: not an object")
            continue
        fid = f.get("id")
        if not isinstance(fid, str) or not fid or len(fid) > 128 or set(fid) - ID_CHARS or fid in {".", ".."}:
            errs.append(f"{where}: id missing or not filesystem-safe: {fid!r}")
        elif fid in seen:
            errs.append(f"{where}: duplicate id {fid!r}")
        else:
            seen.add(fid)
        if f.get("source") not in VALID_SOURCES:
            errs.append(f"{where}: source not in {VALID_SOURCES}: {f.get('source')!r}")
    return errs


def _expected_mc_ids(spec_dir: Path) -> tuple[dict[str, dict[str, Any]] | None, list[str]]:
    path = spec_dir / "findings.json"
    if not path.is_file():
        return None, []
    try:
        doc = json.loads(path.read_text())
    except (OSError, ValueError) as exc:
        return None, [f"invalid findings.json: {exc}"]
    findings = doc.get("findings") if isinstance(doc, dict) else None
    if not isinstance(findings, list):
        return None, ["invalid findings.json: 'findings' missing or not a list"]
    findings_by_id: dict[str, dict[str, Any]] = {}
    errs: list[str] = []
    for i, finding in enumerate(findings):
        fid = finding.get("id") if isinstance(finding, dict) else None
        if not isinstance(fid, str) or not fid:
            errs.append(f"invalid findings.json: findings[{i}] has no id")
        elif fid in findings_by_id:
            errs.append(f"invalid findings.json: duplicate id {fid!r}")
        else:
            findings_by_id[fid] = finding
            if not fid.startswith("MC-") or set(fid) - ID_CHARS or fid in {".", ".."}:
                errs.append(f"invalid findings.json: unsafe model-checking id {fid!r}")
            if finding.get("source") != "model-checking":
                errs.append(f"invalid findings.json: {fid} source must be 'model-checking'")
            for field in ("invariant", "config", "counterexample"):
                if not isinstance(finding.get(field), str) or not str(finding[field]).strip():
                    errs.append(f"invalid findings.json: {fid} requires non-empty {field}")
            counterexample = finding.get("counterexample")
            if isinstance(counterexample, str) and counterexample.strip():
                raw = Path(counterexample)
                if raw.is_absolute() or ".." in raw.parts:
                    errs.append(f"invalid findings.json: {fid} counterexample must stay under the work directory")
                else:
                    work_dir = spec_dir.parent.resolve()
                    cx = (work_dir / raw).resolve()
                    try:
                        cx.relative_to(work_dir)
                    except ValueError:
                        errs.append(f"invalid findings.json: {fid} counterexample escapes the work directory")
                    else:
                        if not cx.is_file() or cx.stat().st_size == 0:
                            errs.append(f"invalid findings.json: {fid} counterexample is missing or empty")
    return findings_by_id, errs


def _expected_brief_scenarios(brief: Path) -> set[str] | None:
    if not brief.is_file():
        return set()
    text = brief.read_text(errors="replace")
    return {f"Scenario {number}" for number in re.findall(r"(?im)^#{2,4}\s+Scenario\s+(\d+)\s*:", text)}


def _candidate_fingerprint(cfg: ConfirmConfig) -> str:
    wd = cfg.ws.work_dir(cfg.name)
    spec_dir = wd / "spec"
    files: dict[str, str] = {}
    for label, path in (
        ("findings", spec_dir / "findings.json"),
        ("bug_report", spec_dir / "bug-report.md"),
        ("brief", wd / "modeling-brief.md"),
        ("prompt", Path(__file__).resolve().parent / "prompts" / "confirmation" / "consolidate.md"),
        ("schema", SKILLS / "validation-workflow" / "references" / "findings-json-format.md"),
    ):
        files[label] = path.read_text(errors="replace") if path.is_file() else ""
    return _digest(
        {
            "version": _CACHE_VERSION,
            "generation": _generation_content(cfg),
            "prompt_extra": cfg.prompt_extra,
            "adapter": _adapter_identity(cfg),
            "claude_alias": cfg.claude_alias,
            "max_turns": cfg.max_turns,
            "tuning": _tuning_identity(cfg),
            "files": files,
        }
    )


def _candidate_output_digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _candidate_cache_valid(
    cfg: ConfirmConfig,
    out: Path,
    expected: set[str] | dict[str, dict[str, Any]] | None,
    expected_scenarios: set[str] | None = None,
) -> bool:
    if _validate_candidates(out, expected, expected_scenarios):
        return False
    sidecar = out.parent / _CANDIDATE_CACHE
    if not sidecar.is_file():
        # A candidates-only workspace is an explicit caller-provided input (and
        # is useful for unit/in-process callers). Real consolidation inputs need
        # a dispatcher-owned sidecar before they may be reused.
        wd = cfg.ws.work_dir(cfg.name)
        has_sources = any(
            path.is_file()
            for path in (out.parent / "findings.json", out.parent / "bug-report.md", wd / "modeling-brief.md")
        )
        return not has_sources and not (out.parent / "confirmation-generation.json").is_file()
    try:
        meta = json.loads(sidecar.read_text())
        return bool(
            meta.get("cache_version") == _CACHE_VERSION
            and meta.get("fingerprint") == _candidate_fingerprint(cfg)
            and meta.get("output_digest") == _candidate_output_digest(out)
        )
    except (OSError, ValueError, TypeError):
        return False


def _write_candidate_cache(cfg: ConfirmConfig, out: Path) -> None:
    sidecar = out.parent / _CANDIDATE_CACHE
    tmp = sidecar.with_suffix(sidecar.suffix + ".tmp")
    tmp.write_text(
        json.dumps(
            {
                "cache_version": _CACHE_VERSION,
                "fingerprint": _candidate_fingerprint(cfg),
                "output_digest": _candidate_output_digest(out),
            },
            sort_keys=True,
        )
    )
    tmp.replace(sidecar)


def consolidate(cfg: ConfirmConfig) -> None:
    """Phase-4 step 0: one agent merges MC (bug-report/findings.json) with
    code-review Scenarios (modeling-brief) and dedups them into candidates.json.
    Idempotent: a present-and-valid candidates.json is reused. Raises
    RateLimited on exit 75; raises RuntimeError if the output is missing/invalid."""
    wd = cfg.ws.work_dir(cfg.name)
    spec_dir = wd / "spec"
    out = spec_dir / "candidates.json"
    expected_mc_ids, source_errs = _expected_mc_ids(spec_dir)
    brief = wd / "modeling-brief.md"
    external_candidates = (
        out.is_file()
        and not (spec_dir / "findings.json").is_file()
        and not (spec_dir / "bug-report.md").is_file()
        and not brief.is_file()
        and not (spec_dir / "confirmation-generation.json").is_file()
    )
    expected_scenarios = None if external_candidates else _expected_brief_scenarios(brief)
    resume_logical = ("confirm", cfg.name, "consolidate")
    if source_errs:
        raise ConsolidateFailed(f"invalid model-checking input for {cfg.name}: {source_errs[0]}")
    if out.is_file() and _candidate_cache_valid(cfg, out, expected_mc_ids, expected_scenarios):
        cfg.clear_policy_states(("consolidate",))
        resumelib.complete_turn(resume_logical, allow_previous_owner=resumelib.manual_mode())
        _log(f"  {cfg.name}: candidates.json present and valid — skipping consolidate")
        return
    bug_report = spec_dir / "bug-report.md"
    findings_json = spec_dir / "findings.json"
    mc_src = (
        f"`{findings_json}` (structured MC findings — prefer this)" if findings_json.is_file() else f"`{bug_report}`"
    )
    prompt = (
        render(
            "confirmation/consolidate",
            name=cfg.name,
            mc_src=mc_src,
            brief=str(brief),
            out=str(out),
            validation_workflow_skill=prompt_skill_ids("validation-workflow"),
        )
        + cfg.prompt_extra
    )
    if cfg.dry_run:
        _log(f"  {cfg.name}: [DRY] consolidate → {out}")
        return
    spec_dir.mkdir(parents=True, exist_ok=True)
    policy_state = cfg.policy_state(("consolidate",), prompt)
    fresh = policy_state.invocation_attempt == 0 and not resumelib.has_prefix(resume_logical)
    if fresh:
        # Do not let a fresh failed agent make stale output look fresh. An exact
        # rc75 continuation, however, may need candidates already written by its
        # still-live native session, so the replay must not delete them.
        out.unlink(missing_ok=True)
        (spec_dir / _CANDIDATE_CACHE).unlink(missing_ok=True)
    run_cwd = _consolidate_cwd(wd, fresh=fresh)
    try:
        rc, _ = run_agent_blocking(
            cfg.adapter,
            prompt,
            spec_dir / ".consolidate.prompt.md",
            spec_dir / ".consolidate.log",
            phase_key=PHASE_KEY,
            work_dir=wd,
            cwd=run_cwd,
            claude_alias=cfg.claude_alias,
            max_turns=cfg.max_turns,
            model=cfg.model,
            effort=cfg.effort,
            policy_retries=cfg.policy_retries,
            transient_resumes=cfg.transient_resumes,
            policy_state=policy_state,
            resume_logical=resume_logical,
            resume_phase=PHASE_KEY,
            resume_target=cfg.name,
            resume_kind="consolidate",
            manual_prompt_extra=cfg.resume_prompt_extra,
        )
    except BaseException:
        cfg.clear_policy_states(("consolidate",))
        raise
    if rc == 75:
        raise RateLimited(f"{cfg.name} consolidate")
    cfg.clear_policy_states(("consolidate",))
    if rc != 0:
        out.unlink(missing_ok=True)
        raise ConsolidateFailed(f"consolidate adapter exited {rc}")
    errs = (
        _validate_candidates(out, expected_mc_ids, expected_scenarios)
        if out.is_file()
        else ["no candidates.json produced"]
    )
    if errs:
        if out.is_file():
            out.unlink()  # drop the invalid file so load_findings does not choke on it
        raise ConsolidateFailed(f"no valid candidates.json for {cfg.name}: {errs[0]}")
    _write_candidate_cache(cfg, out)
    resumelib.complete_turn(resume_logical, allow_previous_owner=resumelib.manual_mode())
    doc = json.loads(out.read_text())
    cand = doc.get("findings", [])
    n_merged = sum(1 for c in cand if c.get("dedup_note"))
    _log(f"  {cfg.name}: consolidated {len(cand)} candidates ({n_merged} absorbed a code-review dup)")


# ── aggregation → confirmed-bugs.md ──────────────────────────────────────────


def _novelty(body: str) -> str:
    """Parse the Reproducer's per-bug Novelty: NEW / KNOWN-unfixed / KNOWN-fixed.
    Missing claims stay UNKNOWN; absence is not evidence that a bug is new."""
    claims = re.findall(r"(?im)^\s*-?\s*\*\*Novelty\*\*:\s*([^\r\n]+)", body)
    if not claims:
        return "UNKNOWN"
    claim = claims[-1]
    kind = re.match(r"\s*(NEW|KNOWN)\b", claim, re.IGNORECASE)
    if not kind:
        return "UNKNOWN"
    if kind.group(1).upper() == "NEW":
        return "NEW"
    # Bind fix-status to the same (last) Novelty declaration. An older claim's
    # metadata must not leak into a debate correction.
    fix = re.search(r"fix-status:\s*(unfixed|fixed)", claim, re.IGNORECASE)
    if not fix:
        return "UNKNOWN"
    return "KNOWN-fixed" if fix.group(1).lower() == "fixed" else "KNOWN-unfixed"


def _report_body(body: str) -> str:
    """Prevent nested agent prose from injecting canonical report records."""
    lines: list[str] = []
    for line in body.splitlines():
        if re.match(r"^\s*VERDICT\s*:", line, re.I):
            continue
        if _REPORT_STATUS_FIELD_RE.match(line):
            continue
        if re.match(r"^##\s+(?:Bug|Entry)\s+\d+\s*:", line, re.I):
            line = "\\" + line
        lines.append(line)
    return "\n".join(lines).strip()


def aggregate(cfg: ConfirmConfig, outcomes: list[Outcome]) -> None:
    """Write the phase's confirmed-bugs.md from the per-finding outcomes. This is
    the canonical Phase-4 deliverable the classification phase (Phase 4b) and the
    repair loop read; A/B isolation is handled by the run dir, not by a separate
    filename. Headers are ``## Entry N:`` (integer N, table order) so Phase 4b's
    "one row per entry header" parsing aligns; the finding id (MC-1 / CR-2) is
    carried as a body field and a table column."""
    report = cfg.ws.work_dir(cfg.name) / "confirmed-bugs.md"

    def effective_status(outcome: Outcome) -> str:
        if outcome.status != "PENDING REPAIR" or outcome.rr is None:
            return outcome.status
        rr_dir = cfg.ws.work_dir(cfg.name) / "spec" / "repair-requests"
        deferred = rr_dir / "deferred" / f"{outcome.rr}.md"
        if not deferred.is_file():
            consumed = rr_dir / f"{outcome.rr}.md"
            if cfg.repair_round is not None and consumed.is_file():
                text = consumed.read_text(errors="replace")
                if _rr_field_text(text, "id") == [outcome.rr] and _rr_field_text(text, "status") == ["CONSUMED"]:
                    return "FALSE POSITIVE"
        else:
            text = deferred.read_text(errors="replace")
            if _rr_field_text(text, "id") == [outcome.rr] and _rr_field_text(text, "status") == ["DEFERRED"]:
                return "DEFERRED"
        return outcome.status

    effective = [(outcome, effective_status(outcome)) for outcome in outcomes]
    # A non-canonical status (e.g. INCOMPLETE from a finding whose confirmation
    # could not finish — infra error / rate limit) is rendered verbatim and simply
    # not counted as a bug/finding; it must never discard the whole report.
    incomplete = [o for o, status in effective if status not in CANON and status != "DEFERRED"]
    status_counts = {status: sum(effective_status == status for _, effective_status in effective) for status in CANON}
    deferred_count = sum(status == "DEFERRED" for _, status in effective)
    reproduced = [o for o, status in effective if status == "REPRODUCED"]
    nov = [_novelty(o.body) for o in reproduced]
    n_new = nov.count("NEW")
    n_known_unfixed = nov.count("KNOWN-unfixed")
    n_known_fixed = nov.count("KNOWN-fixed")
    n_unknown = nov.count("UNKNOWN")

    env_limited = [o for o, status in effective if status == "ENV_LIMITED"]
    masked = [o for o, status in effective if status == "MASKED"]

    lines = [f"# Confirmation Report — {cfg.name}", "", "## Final Result", ""]
    split = (
        f"Reproduced bugs: {len(reproduced)} = {n_new} NEW + {n_known_unfixed} KNOWN-unfixed"
        f" + {n_known_fixed} KNOWN-fixed + {n_unknown} UNKNOWN"
    )
    lines.append(split)
    # The "finding" tier — real defects that are not confirmed live bugs: real but
    # only triggerable in production (env-limited), or a real anomaly whose
    # consequence a safeguard currently masks. Reported separately so they are
    # neither miscounted as bugs nor lost as false positives.
    lines.append(f"Masked live findings: {len(masked)}")
    lines.append(f"Env-limited findings: {len(env_limited)}")
    lines.append(f"False positives: {status_counts['FALSE POSITIVE']}")
    lines.append(f"Dropped: {status_counts['DROPPED']}")
    lines.append(f"Needs more info: {status_counts['NEEDS MORE INFO']}")
    lines.append(f"Pending repair: {status_counts['PENDING REPAIR']}")
    lines.append(f"Incomplete: {len(incomplete)}")
    lines.append(f"Deferred: {deferred_count}")
    lines.append(f"Total disposition entries: {len(outcomes)}")
    lines.append(
        f"Dispositions: {len(outcomes)} total = {status_counts['REPRODUCED']} reproduced"
        f" + {status_counts['ENV_LIMITED']} env-limited + {status_counts['MASKED']} masked"
        f" + {status_counts['FALSE POSITIVE']} false-positive + {status_counts['NEEDS MORE INFO']} needs-more-info"
        f" + {status_counts['DROPPED']} dropped + {status_counts['PENDING REPAIR']} pending-repair"
        f" + {len(incomplete)} incomplete + {deferred_count} deferred"
    )
    lines.append("")
    lines.append("| Entry | Finding | Status | Counts as final bug? |")
    lines.append("|---|---|---|---|")
    for o, status in effective:
        if status == "DEFERRED":
            rendered_status = f"DEFERRED (repair loop exhausted; {o.rr} in deferred/)"
        elif status == "FALSE POSITIVE" and o.status == "PENDING REPAIR":
            rendered_status = status
        else:
            rr = f" ({o.rr})" if o.rr else ""
            rendered_status = f"{status}{rr}"
        counts = "yes" if status == "REPRODUCED" else "no"
        lines.append(f"| {o.bug_no} | {o.finding.id} | {rendered_status} | {counts} |")
    lines.append("")
    for o, status in effective:
        if status == "DEFERRED":
            rendered_status = f"DEFERRED (repair loop exhausted; {o.rr} in deferred/)"
        elif status == "FALSE POSITIVE" and o.status == "PENDING REPAIR":
            rendered_status = status
        else:
            rr = f" ({o.rr})" if o.rr else ""
            rendered_status = f"{status}{rr}"
        title = re.sub(r"[\r\n]+", " ", str(o.finding.data.get("title", ""))).strip()
        lines.append(f"## Entry {o.bug_no}: {title}")
        lines.append("")
        lines.append(f"- **Finding ID**: {o.finding.id}")
        lines.append(f"- **Status**: {rendered_status}")
        debate_summary = (
            "not run" if o.rounds == 0 else (f"{'consensus' if o.consensus else 'NO CONSENSUS'} in {o.rounds} round(s)")
        )
        lines.append(f"- **Debate**: {debate_summary}")
        lines.append(f"- **Transcript**: {o.finding.fdir / 'debate.md'}")
        lines.append("")
        lines.append(_report_body(o.body))
        lines.append("")
        lines.append("---")
        lines.append("")
    report.write_text("\n".join(lines))
    _log(f"\nWrote {report}  ({len(outcomes)} findings, {len(reproduced)} reproduced)")


# ── driver ───────────────────────────────────────────────────────────────────


def _findings_from_data(cfg: ConfirmConfig, data: list[dict[str, Any]]) -> list[Finding]:
    conf_root = cfg.ws.work_dir(cfg.name).absolute() / "confirmation"
    findings: list[Finding] = []
    for item in data:
        fid = str(item.get("id", ""))
        if not fid or set(fid) - ID_CHARS or fid in {".", ".."}:
            raise ConfirmationFailed(f"unsafe finding id: {fid!r}")
        findings.append(Finding(item, conf_root / fid))
    return findings


def _parse_report_status(value: str) -> tuple[str, str | None]:
    value = value.strip()
    if value in CANON or value == INCOMPLETE:
        return value, None
    pending = re.fullmatch(r"PENDING REPAIR \((RR-\d+)\)", value)
    if pending is not None:
        return "PENDING REPAIR", pending.group(1)
    deferred = re.fullmatch(r"DEFERRED \(repair loop exhausted; (RR-\d+) in deferred/\)", value)
    if deferred is not None:
        return "DEFERRED", deferred.group(1)
    raise ConfirmationFailed(f"cannot import prior report status {value!r}")


def _prior_report_catalog(cfg: ConfirmConfig) -> tuple[list[dict[str, Any]], list[Outcome]]:
    """Import a canonical Phase-4 report into the existing verdict model.

    Legacy confirmation remains a supported initial mode but did not write
    candidates.json or per-finding verdict.json. A scoped repair pass imports
    missing evidence from the canonical report so it can preserve the same
    findings while dispatching only the current MC violations.
    """
    report = cfg.ws.work_dir(cfg.name) / "confirmed-bugs.md"
    if report.is_symlink() or not report.is_file():
        return [], []
    text = report.read_text()
    rows = list(_REPORT_RR_ROW_RE.finditer(text))
    details = list(_REPORT_DETAIL_RE.finditer(text))
    if not rows and not details:
        return [], []
    if len(rows) != len(details):
        raise ConfirmationFailed("legacy confirmation report table/detail counts do not match")

    detail_by_number: dict[int, tuple[re.Match[str], int]] = {}
    for index, detail in enumerate(details):
        number = int(detail.group(1))
        if number in detail_by_number:
            raise ConfirmationFailed(f"legacy confirmation report repeats Entry {number}")
        end = details[index + 1].start() if index + 1 < len(details) else len(text)
        detail_by_number[number] = (detail, end)

    catalog: list[dict[str, Any]] = []
    outcomes: list[Outcome] = []
    seen_ids: set[str] = set()
    for row in rows:
        bug_no = int(row.group(1))
        finding_id = row.group(2).strip()
        if not finding_id or set(finding_id) - ID_CHARS or finding_id in {".", ".."} or finding_id in seen_ids:
            raise ConfirmationFailed(f"legacy confirmation report has invalid finding id {finding_id!r}")
        seen_ids.add(finding_id)
        detail_info = detail_by_number.get(bug_no)
        if detail_info is None:
            raise ConfirmationFailed(f"legacy confirmation report is missing Entry {bug_no}")
        detail, end = detail_info
        heading_end = text.find("\n", detail.end(), end)
        if heading_end < 0:
            heading_end = end
        title = text[detail.end() : heading_end].strip()
        block = text[heading_end:end].strip()
        detail_ids = re.findall(r"(?m)^- \*\*Finding ID\*\*:\s*([^\s]+)\s*$", block)
        if detail_ids != [finding_id]:
            raise ConfirmationFailed(f"legacy confirmation Entry {bug_no} does not match {finding_id}")
        status, rr = _parse_report_status(row.group(3))
        source_claims = re.findall(r"(?im)^\s*-\s*\*\*Source\*\*:\s*([^\r\n]+)", block)
        source_claim = source_claims[-1].strip().lower() if source_claims else ""
        if source_claim.startswith("mc") or finding_id.startswith("MC-"):
            source = "model-checking"
        elif source_claim.startswith("code review") or finding_id.startswith("CR-"):
            source = "code-review"
        else:
            raise ConfirmationFailed(f"legacy confirmation Entry {bug_no} has no usable Source")
        if status == "PENDING REPAIR" and source != "model-checking":
            raise ConfirmationFailed(f"legacy confirmation Entry {bug_no} has invalid repair source")

        data = {
            "id": finding_id,
            "source": source,
            "title": title,
            "summary": title,
        }
        finding = Finding(data, cfg.ws.work_dir(cfg.name).absolute() / "confirmation" / finding_id)
        body_lines = [
            line
            for line in block.splitlines()
            if not re.match(
                r"^\s*-\s*\*\*(?:Finding ID|Status|Debate|Transcript)\*\*:",
                line,
                re.I,
            )
        ]
        while body_lines and (not body_lines[-1].strip() or body_lines[-1].strip() == "---"):
            body_lines.pop()
        body = "\n".join(body_lines).strip() or "Imported evidence from the canonical legacy confirmation report."
        catalog.append(data)
        outcomes.append(Outcome(finding, status, True, 0, body, rr, bug_no))
    return catalog, outcomes


def _save_imported_verdict(outcome: Outcome) -> None:
    """Materialize legacy report evidence without making it a cache hit."""
    outcome.finding.fdir.mkdir(parents=True, exist_ok=True)
    verdict = outcome.finding.fdir / "verdict.json"
    if verdict.exists():
        return
    tmp = verdict.with_suffix(".json.tmp")
    tmp.write_text(
        json.dumps(
            {
                "cache_version": _CACHE_VERSION,
                "fingerprint": "legacy-report-import",
                "status": outcome.status,
                "consensus": outcome.consensus,
                "rounds": outcome.rounds,
                "rr": outcome.rr,
                "body": outcome.body,
                "artifacts": {},
            },
            ensure_ascii=False,
        )
    )
    tmp.replace(verdict)


def _prepare_repair_findings(cfg: ConfirmConfig) -> tuple[list[Finding], list[Finding]]:
    """Load current Phase-3 violations and merge them into the old catalog.

    The returned first list is the *only* dispatch set. The second is the
    cumulative catalog used to retain prior code-review/model-checking outcomes
    in the report and to keep stable entry ordering.
    """
    wd = cfg.ws.work_dir(cfg.name).absolute()
    spec_dir = wd / "spec"
    current_by_id, errs = _expected_mc_ids(spec_dir)
    if current_by_id is None:
        raise ConfirmationFailed("repair confirmation requires spec/findings.json")
    if errs:
        raise ConfirmationFailed(errs[0])

    candidates = spec_dir / "candidates.json"
    report_catalog, imported = _prior_report_catalog(cfg)
    if candidates.is_file():
        candidate_errs = _validate_candidates(candidates)
        if candidate_errs:
            raise ConfirmationFailed(f"invalid cumulative candidates: {candidate_errs[0]}")
        doc = json.loads(candidates.read_text())
        catalog_data = list(doc["findings"])
    else:
        catalog_data = list(report_catalog)
        doc = {"findings": catalog_data}

    positions = {str(item["id"]): index for index, item in enumerate(catalog_data)}
    for item in report_catalog:
        fid = str(item["id"])
        if fid not in positions:
            positions[fid] = len(catalog_data)
            catalog_data.append(item)
    for fid, item in current_by_id.items():
        if fid in positions:
            catalog_data[positions[fid]] = item
        else:
            positions[fid] = len(catalog_data)
            catalog_data.append(item)
    doc["findings"] = catalog_data

    if not cfg.dry_run:
        # Import every missing prior verdict before publishing candidates.
        # If this loop is interrupted, candidates remains absent/unchanged and
        # the canonical report drives the same idempotent import on retry.
        for outcome in imported:
            _save_imported_verdict(outcome)
        spec_dir.mkdir(parents=True, exist_ok=True)
        tmp = candidates.with_suffix(".json.tmp")
        tmp.write_text(json.dumps(doc, ensure_ascii=False, indent=2) + "\n")
        tmp.replace(candidates)
        (spec_dir / _CANDIDATE_CACHE).unlink(missing_ok=True)

    current = _findings_from_data(cfg, list(current_by_id.values()))
    catalog = _findings_from_data(cfg, catalog_data)
    return current, catalog


def load_findings(cfg: ConfirmConfig) -> list[Finding]:
    wd = cfg.ws.work_dir(cfg.name).absolute()
    spec_dir = wd / "spec"
    path = spec_dir / "candidates.json"
    if not path.is_file():
        path = spec_dir / "findings.json"
    if not path.is_file():
        # No candidate list (e.g. --dry-run, which does not run consolidate, or a
        # consolidate that produced nothing) — nothing to fan out.
        return []
    doc = json.loads(path.read_text())
    errs = _validate_candidates(path) if path.name == "candidates.json" else []
    if errs:
        raise ConfirmationFailed(f"invalid candidate input: {errs[0]}")
    return _findings_from_data(cfg, doc.get("findings", []))


def run_parallel_confirmation(cfg: ConfirmConfig, *, retain_rate_limited_state: bool = False) -> int:
    """Drive step 0 (consolidate) → per-finding fan-out → aggregate for ONE
    target. Returns 75 for exclusively rate-limited incomplete findings and 1 for
    permanent/format/infrastructure incomplete findings while retaining their
    partial report. Pre-fan-out or aggregation failures withhold the deliverable."""
    result = 1
    try:
        try:
            if not cfg.dry_run:
                log_path = cfg.ws.work_dir(cfg.name) / "bug-confirmation.log"
                log_path.parent.mkdir(parents=True, exist_ok=True)
                log_path.write_text("")  # summary link + `tail -f` follow THIS run
                _set_log_file(log_path)
            result = _drive_confirmation(cfg)
        except Exception as exc:
            try:
                _log(f"confirmation driver crashed ({exc})")
            except OSError:
                print(f"confirmation driver crashed ({exc})", flush=True)
            result = 1 if cfg.dry_run else _withhold(cfg, "confirmation driver failure — deliverable withheld")
        return result
    finally:
        if result != quota.RATE_LIMIT_RC or not retain_rate_limited_state:
            cfg.clear_retry_runtime()
        _set_log_file(None)


def _withhold(cfg: ConfirmConfig, reason: str, code: int = 1) -> int:
    """Remove a stale deliverable and return an actionable failure code."""
    reports = [
        cfg.ws.work_dir(cfg.name) / "confirmed-bugs.md",
        cfg.ws.work_dir(cfg.name) / "spec" / "confirmed-bugs.md",
    ]
    # A repair pass updates a cumulative deliverable. If preparation itself
    # fails, the already-confirmed report remains the valid last-known result.
    if not cfg.dry_run and cfg.repair_round is None:
        for report in reports:
            if report.is_file():
                try:
                    report.unlink()
                except OSError as exc:
                    print(f"failed to remove stale {report}: {exc}", flush=True)
    try:
        _log(reason)
    except OSError:
        print(reason, flush=True)
    return code


def _post_validate_repair_state(cfg: ConfirmConfig) -> int:
    if cfg.dry_run:
        return 0
    try:
        ensure_rr_stable_identities(
            cfg,
            verify_against_report=True,
            require_active_report_link=True,
        )
        validate_report_repair_references(cfg)
    except (ConfirmationFailed, OSError, UnicodeError, ValueError) as exc:
        _log(f"repair identity post-validation failed ({exc}) — report retained for inspection")
        return 1
    return 0


def _drive_confirmation(cfg: ConfirmConfig) -> int:
    if cfg.max_parallel < 1:
        return _withhold(cfg, "invalid max_parallel; expected a positive integer")
    if cfg.debate and cfg.rounds < 1:
        return _withhold(cfg, "invalid debate rounds; expected a positive integer")
    if cfg.repair_round is not None and cfg.repair_round < 1:
        return _withhold(cfg, "invalid repair_round; expected a positive integer")
    if not cfg.dry_run:
        try:
            # This must precede consolidate/aggregation: the previous canonical
            # report may be the only proof that binds a pre-finding_id legacy RR
            # to its stable candidate. A zero-PENDING run still replaces that
            # report, so waiting until allocate_rr would lose the evidence.
            ensure_rr_stable_identities(
                cfg,
                verify_against_report=True,
                require_active_report_link=False,
            )
        except (ConfirmationFailed, OSError, UnicodeError, ValueError) as exc:
            _log(f"repair identity preflight failed ({exc}) — existing report retained")
            return 1

    prior_by_id: dict[str, Outcome] = {}
    repair_evidence_by_id: dict[str, str] = {}
    try:
        if cfg.repair_round is None:
            try:
                consolidate(cfg)
            except RateLimited:
                return _withhold(
                    cfg,
                    "consolidate rate-limited — deliverable withheld for scheduler retry",
                    quota.RATE_LIMIT_RC,
                )
            except ConsolidateFailed as exc:
                return _withhold(
                    cfg,
                    f"consolidate failed ({exc}) — deliverable withheld; downstream gate + retry settle it",
                )
            findings = load_findings(cfg)
            catalog = findings
        else:
            commit = _load_repair_commit(cfg)
            findings, catalog = _prepare_repair_findings(cfg)
            if [finding.id for finding in findings] != commit["violation_ids"]:
                raise ConfirmationFailed("current repair findings do not match the committed violation ids")
            requests = _repair_round_requests(cfg, commit["request_ids"])
            current_findings = {finding.id: finding for finding in findings}
            for finding in catalog:
                prior = _load_stored_verdict(finding)
                if prior is not None:
                    prior_by_id[finding.id] = prior
                repair_evidence_by_id[finding.id] = _repair_evidence(
                    cfg,
                    finding,
                    requests,
                    current_violation=finding.id in current_findings,
                )
            missing_prior = [
                finding.id
                for finding in catalog
                if finding.id not in current_findings and finding.id not in prior_by_id
            ]
            if missing_prior:
                raise ConfirmationFailed("cumulative findings have no prior evidence: " + ", ".join(missing_prior))
            for finding_id, (request_id, _history) in requests.items():
                prior = prior_by_id.get(finding_id)
                prior_matches = prior is not None and prior.status == "PENDING REPAIR" and prior.rr == request_id
                completed_current = (
                    _load_verdict(current_findings[finding_id], cfg)
                    if finding_id in current_findings and not prior_matches
                    else None
                )
                if not prior_matches and completed_current is None:
                    raise ConfirmationFailed(
                        f"repair request {request_id} has no matching prior PENDING REPAIR evidence for {finding_id}"
                    )
            for finding in findings:
                finding.repair_context = _repair_prompt_context(
                    finding,
                    prior_by_id.get(finding.id),
                    repair_evidence_by_id[finding.id],
                )

            # A consumed request is a completed repair even when Phase 3 found
            # no current violation with that ID. Append its concise Phase-3
            # result to the same verdict evidence before rebuilding the report.
            if not cfg.dry_run:
                for finding in catalog:
                    prior = prior_by_id.get(finding.id)
                    request = requests.get(finding.id)
                    if prior is None or prior.status != "PENDING REPAIR" or request is None:
                        continue
                    if prior.rr != request[0]:
                        continue
                    body = _merge_repair_evidence(
                        prior,
                        repair_evidence_by_id[finding.id],
                        None,
                        cfg.repair_round,
                    )
                    _rewrite_stored_body(finding, body)
                    prior.body = body
    except (ConfirmationFailed, OSError, ValueError, TypeError) as exc:
        return _withhold(cfg, f"candidate loading failed ({exc}) — deliverable withheld")
    _log(
        f"Parallel confirmation: {cfg.name} — {len(findings)} "
        f"{'current repair violations' if cfg.repair_round is not None else 'findings'}, "
        f"debate={'ON' if cfg.debate else 'OFF'}, max_parallel={cfg.max_parallel}"
    )
    if cfg.dry_run:
        for finding in findings:
            _log(f"    [{finding.id}] [DRY] would run confirmation")
        return 0
    if not findings:
        if cfg.repair_round is None:
            aggregate(cfg, [])
        else:
            preserved = [prior_by_id[finding.id] for finding in catalog if finding.id in prior_by_id]
            for index, preserved_outcome in enumerate(preserved, 1):
                preserved_outcome.bug_no = index
            aggregate(cfg, preserved)
        return _post_validate_repair_state(cfg)

    outcomes: list[Outcome] = []
    unstarted: list[Finding] = []
    scheduled_findings = findings
    next_finding = 0
    rate_limit_seen = threading.Event()

    recovery_source = resumelib.unfinished_entries if resumelib.manual_mode() else resumelib.previous_entries
    recovery_entries = [
        entry for entry in recovery_source(phase=PHASE_KEY, target=cfg.name) if entry.get("kind") == "finding-turn"
    ]
    recovery_ids = list(dict.fromkeys(str(entry.get("finding_id") or "") for entry in recovery_entries))
    if recovery_ids:
        by_id = {finding.id: finding for finding in findings}
        missing = [finding_id for finding_id in recovery_ids if finding_id not in by_id]
        if missing:
            return _withhold(
                cfg,
                "resume checkpoint no longer matches current findings: " + ", ".join(missing),
            )
        _log(f"Restoring {len(recovery_ids)} interrupted finding conversation(s) serially")
        failed_recovery: Outcome | None = None
        for finding_id in recovery_ids:
            finding = by_id[finding_id]
            if cfg.repair_round is None:
                recovered = run_finding_safe(cfg, finding)
            else:
                recovered = run_finding_safe(
                    cfg,
                    finding,
                    prior=prior_by_id.get(finding.id),
                    repair_evidence=repair_evidence_by_id[finding.id],
                )
            if recovered.status == INCOMPLETE:
                failed_recovery = recovered
                break
        if failed_recovery is not None:
            outcomes.append(failed_recovery)
            for finding in findings:
                if finding.id == failed_recovery.finding.id:
                    continue
                cached = _load_verdict(finding, cfg)
                if cached is not None:
                    outcomes.append(cached)
                    continue
                outcomes.append(
                    Outcome(
                        finding,
                        INCOMPLETE,
                        consensus=False,
                        rounds=0,
                        body=(
                            "## Confirmation result\n"
                            "INCOMPLETE — this finding was not started while an interrupted conversation "
                            "was being restored. It was NOT judged and was NOT cached. Re-run to retry."
                        ),
                        failure_code=failed_recovery.failure_code or 1,
                    )
                )
            scheduled_findings = []

    def run_scheduled(finding: Finding) -> Outcome | None:
        # A future may have been submitted before another worker reports a rate
        # limit but not have started confirmation yet. Keep that finding untouched
        # so the scheduler retry can run it later.
        if rate_limit_seen.is_set():
            return None
        if cfg.repair_round is None:
            outcome = run_finding_safe(cfg, finding)
        else:
            outcome = run_finding_safe(
                cfg,
                finding,
                prior=prior_by_id.get(finding.id),
                repair_evidence=repair_evidence_by_id[finding.id],
            )
        if outcome.status == INCOMPLETE and outcome.failure_code == quota.RATE_LIMIT_RC:
            # Set this in the worker before it releases its executor slot. That
            # closes the race where a queued future could otherwise begin between
            # this result becoming available and the dispatcher observing it.
            rate_limit_seen.set()
        return outcome

    with ThreadPoolExecutor(max_workers=cfg.max_parallel) as ex:
        in_flight: dict[Future[Outcome | None], Finding] = {}

        def fill_wave() -> None:
            nonlocal next_finding
            while (
                not rate_limit_seen.is_set()
                and next_finding < len(scheduled_findings)
                and len(in_flight) < cfg.max_parallel
            ):
                finding = scheduled_findings[next_finding]
                next_finding += 1
                in_flight[ex.submit(run_scheduled, finding)] = finding

        fill_wave()
        while in_flight:
            done, _ = wait(tuple(in_flight), return_when=FIRST_COMPLETED)
            for fut in done:
                finding = in_flight.pop(fut)
                try:
                    outcome = fut.result()
                except Exception as exc:  # run_finding_safe absorbs failures; stay robust regardless
                    _log(f"  [{finding.id}] worker crashed unexpectedly ({exc})")
                    outcome = Outcome(
                        finding,
                        INCOMPLETE,
                        consensus=False,
                        rounds=0,
                        body=f"## Confirmation result\nINCOMPLETE — worker crashed: {exc}.",
                        failure_code=1,
                    )
                if outcome is None:
                    unstarted.append(finding)
                else:
                    outcomes.append(outcome)

            if rate_limit_seen.is_set():
                # Futures that have not entered run_scheduled can still be
                # cancelled. A concurrently running finding returns normally and
                # remains in in_flight until its result is collected.
                for fut, finding in list(in_flight.items()):
                    if fut.cancel():
                        in_flight.pop(fut)
                        unstarted.append(finding)
            else:
                fill_wave()

    if rate_limit_seen.is_set():
        unstarted.extend(scheduled_findings[next_finding:])
        for finding in unstarted:
            cached = _load_verdict(finding, cfg)
            if cached is not None:
                _log(f"  [{finding.id}] cached {cached.status} — preserve after batch rate limit")
                outcomes.append(cached)
                continue
            _log(f"  [{finding.id}] INCOMPLETE (not started after batch rate limit) — not cached; retry later")
            incomplete = Outcome(
                finding,
                INCOMPLETE,
                consensus=False,
                rounds=0,
                body=(
                    "## Confirmation result\n"
                    "INCOMPLETE — this finding was not started because another finding was rate-limited. "
                    "It was NOT judged and was NOT cached. Re-run to retry."
                ),
                failure_code=quota.RATE_LIMIT_RC,
            )
            if cfg.repair_round is not None:
                incomplete.body = _merge_repair_evidence(
                    prior_by_id.get(finding.id),
                    repair_evidence_by_id[finding.id],
                    incomplete.body,
                    cfg.repair_round,
                )
            outcomes.append(incomplete)
    # Partial delivery beats total loss: a finding that could not finish is an
    # INCOMPLETE row, clearly marked; every completed finding is still reported. A
    # single infra error / rate limit no longer withholds the whole target.
    if cfg.repair_round is None:
        order = {f.id: i for i, f in enumerate(findings)}
        outcomes.sort(key=lambda o: order[o.finding.id])
    else:
        current_outcomes = {outcome.finding.id: outcome for outcome in outcomes}
        outcomes = [
            current_outcomes.get(finding.id) or prior_by_id[finding.id]
            for finding in catalog
            if finding.id in current_outcomes or finding.id in prior_by_id
        ]
    for i, o in enumerate(outcomes, 1):
        o.bug_no = i  # the "## Entry N:" number, in table order (drives aggregate + the RR bug_id)
    try:
        for o in outcomes:
            if o.status.startswith("PENDING REPAIR") and o.rr is None and not cfg.dry_run:
                o.rr = allocate_rr(cfg, o)
                _save_verdict(o, cfg)  # persist the assigned RR into the idempotent cache
        aggregate(cfg, outcomes)
    except (ConfirmationFailed, OSError, ValueError) as exc:
        return _withhold(cfg, f"confirmation aggregation failed ({exc}) — deliverable withheld")
    post_validation = _post_validate_repair_state(cfg)
    if post_validation != 0:
        return post_validation
    # Keep the partial report, but do not tell the scheduler/downstream that an
    # incomplete target succeeded. A permanent failure wins over rate limiting;
    # only an exclusively rate-limited partial result is retryable with rc 75.
    incomplete_codes = [o.failure_code or 1 for o in outcomes if o.status == INCOMPLETE]
    if any(code != quota.RATE_LIMIT_RC for code in incomplete_codes):
        return 1
    if incomplete_codes:
        return quota.RATE_LIMIT_RC
    return 0
