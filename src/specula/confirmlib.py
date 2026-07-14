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
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from specula import quota
from specula.phaselib import SPECULA_ROOT, Workspace, run_agent_blocking
from specula.prompts import render
from specula.skill_refs import prompt_skill_ids

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

    @property
    def id(self) -> str:
        return str(self.data["id"])


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
    # New controls stay after the original fields to preserve positional callers.
    # None = no Specula override; "" = explicit reset to the CLI default.
    model: str | None = None
    effort: str | None = None
    debate: bool = False
    rounds: int = 5
    max_turns: str = "0"


@dataclass
class Outcome:
    finding: Finding
    status: str
    consensus: bool
    rounds: int
    body: str  # initial A evidence plus any later A defenses
    rr: str | None = None  # assigned RR-NNN when status is PENDING REPAIR
    bug_no: int = 0  # 1-based index in confirmed-bugs.md (the "## Bug N:" number)
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
    )
    if rc == 75:
        raise RateLimited(f"{f.id} turn {turn_no} {role}")
    if rc != 0:
        raise ConfirmationFailed(f"{f.id} turn {turn_no} {role}: adapter exited {rc}")
    if not text.strip():
        raise InvalidAgentOutput(f"{f.id} turn {turn_no} {role}: empty agent output")
    return parse_verdict(text), text


def _fresh_turn_cwd(f: Finding, role: str, turn_no: int) -> Path:
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
    if cwd.is_symlink():
        cwd.unlink()
    elif cwd.exists():
        shutil.rmtree(cwd)
    cwd.mkdir(parents=True)
    try:
        subprocess.run(
            ["git", "init", "--quiet", str(cwd)],
            check=True,
            capture_output=True,
            text=True,
        )
    except (OSError, subprocess.CalledProcessError) as exc:
        raise ConfirmationFailed(f"{f.id}: could not create trusted per-turn cwd: {exc}") from exc
    return cwd


# ── per-finding git worktree (build isolation) ───────────────────────────────


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
    probe = subprocess.run(["git", "-C", repo, "rev-parse", "--is-inside-work-tree"], capture_output=True, text=True)
    if probe.returncode != 0 or probe.stdout.strip() != "true":
        raise ConfirmationFailed(f"{f.id}: worktree isolation requested but {repo!r} is not a git checkout")
    root_result = subprocess.run(["git", "-C", repo, "rev-parse", "--show-toplevel"], capture_output=True, text=True)
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
    dirty = subprocess.run(status_cmd, capture_output=True, text=True)
    if dirty.returncode != 0:
        raise ConfirmationFailed(f"{f.id}: could not inspect repository state: {dirty.stderr.strip()}")
    patch = subprocess.run(["git", "-C", str(root), "diff", "--binary", "HEAD", *pathspec], capture_output=True)
    untracked = subprocess.run(
        ["git", "-C", str(root), "ls-files", "--others", "--exclude-standard", "-z", *pathspec],
        capture_output=True,
    )
    if patch.returncode != 0 or untracked.returncode != 0:
        raise ConfirmationFailed(f"{f.id}: could not snapshot local repository changes")
    wt = f.fdir.absolute() / "worktree"
    try:
        wt.parent.resolve().relative_to(cfg.ws.work_dir(cfg.name).resolve())
    except ValueError as exc:
        raise ConfirmationFailed(f"{f.id}: worktree destination escapes the confirmation output") from exc
    wt.parent.mkdir(parents=True, exist_ok=True)
    if wt.is_symlink():
        raise ConfirmationFailed(f"{f.id}: refusing stale worktree symlink")
    # Target only this dispatcher-owned path. Avoid global `worktree prune`,
    # which can affect unrelated user worktrees.
    subprocess.run(["git", "-C", str(root), "worktree", "remove", "--force", str(wt)], capture_output=True)
    if wt.exists():
        if wt.is_dir():
            shutil.rmtree(wt)
        else:
            wt.unlink()
    try:
        subprocess.run(
            ["git", "-C", str(root), "worktree", "add", "--detach", "--force", str(wt)],
            check=True,
            capture_output=True,
            text=True,
        )
    except subprocess.CalledProcessError as e:
        raise ConfirmationFailed(f"{f.id}: worktree isolation failed: {e.stderr.strip()[:200]}") from e

    try:
        if patch.stdout:
            applied = subprocess.run(
                ["git", "-C", str(wt), "apply", "--binary", "-"], input=patch.stdout, capture_output=True
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
        subprocess.run(["git", "-C", str(root), "worktree", "remove", "--force", str(wt)], capture_output=True)
        raise

    if dirty.stdout.strip():
        _log(f"  [{f.id}] copied tracked/untracked local changes into isolated worktree")

    def cleanup() -> None:
        # Best-effort, NEVER fatal. A worktree that cannot be removed — e.g. a
        # containerised build (sonic-dash-ha) left artifacts root-owned that this
        # user cannot delete — is a disk-cleanup nuisance, never a reason to discard
        # a finding whose confirmation already finished. Drop the git registration
        # where possible and warn; the leftover directory is harmless (each finding
        # uses its own path).
        result = subprocess.run(
            ["git", "-C", str(root), "worktree", "remove", "--force", str(wt)], capture_output=True, text=True
        )
        if result.returncode == 0:
            return
        subprocess.run(["git", "-C", str(root), "worktree", "prune"], capture_output=True)
        message = f"{f.id}: could not remove isolated worktree (left on disk): {result.stderr.strip()[:200]}"
        try:
            _log(f"  WARNING: {message}")
        except OSError:
            print(f"  WARNING: {message}", flush=True)

    return str(wt), cleanup


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


def _restore_repair_draft(path: Path, body: str) -> None:
    """Restore a usable pre-correction draft if the advisory turn damages it."""
    if path.is_symlink() or path.is_file():
        path.unlink()
    elif path.is_dir():
        shutil.rmtree(path)
    elif path.exists():
        path.unlink()
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


def run_finding(cfg: ConfirmConfig, f: Finding) -> Outcome:
    if not f.id or set(f.id) - ID_CHARS or f.id in {".", ".."}:
        raise InvalidAgentOutput(f"unsafe finding id: {f.id!r}")
    f.fdir.mkdir(parents=True, exist_ok=True)
    repro_dir = cfg.ws.work_dir(cfg.name).absolute() / "repro"
    repro_dir.mkdir(parents=True, exist_ok=True)
    # Fresh generations must create fresh artifacts. Completed findings in a
    # rate-limit retry are skipped by the fingerprinted verdict cache.
    for stale in _repro_files(cfg, f):
        stale.unlink()
    rr_body = f.fdir / "repair-request.body.md"
    if rr_body.is_file():
        rr_body.unlink()
    debate = f.fdir / "debate.md"
    repo_for_agent, cleanup = setup_repo(cfg, f)
    try:
        turn = 1
        repair_retry_used = False

        def prepare_pending(previous_turn: int, previous_role: str = "A") -> int:
            """Warn about a draft problem and make at most one correction turn.

            A readable, non-empty draft is always usable.  If the optional
            correction fails, retain that original draft rather than turning a
            parser complaint into an INCOMPLETE finding.
            """
            nonlocal repair_retry_used
            original: str | None = None
            problem: Exception | str | None = None
            try:
                draft = _read_repair_draft(cfg, f)
                original = draft.raw
                problem = _repair_draft_warning(cfg, f, draft)
            except InvalidRepairRequest as exc:
                problem = exc

            if problem is None:
                return previous_turn

            warning = str(problem)
            _log(f"  WARNING: {warning}")
            if repair_retry_used:
                if original is None:
                    assert isinstance(problem, Exception)
                    raise problem
                return previous_turn

            repair_retry_used = True
            correction_turn = previous_turn + 1
            draft_path = f.fdir / "repair-request.body.md"
            try:
                correction_verdict, _ = run_turn(
                    cfg,
                    f,
                    "A-repair",
                    correction_turn,
                    prompt_repair_draft_retry(
                        cfg,
                        f,
                        repo_for_agent,
                        warning,
                        f.fdir / f"turn{previous_turn:02d}_{previous_role}.log",
                    ),
                    cwd=_fresh_turn_cwd(f, "A-repair", correction_turn),
                )
                debate.write_text(
                    debate.read_text()
                    + _debate_entry(
                        f,
                        "A-repair",
                        correction_turn,
                        "A (repair-draft correction)",
                        correction_verdict,
                    )
                )
            except Exception as exc:
                if original is None:
                    raise
                _log(f"  WARNING: {f.id}: repair-draft correction failed ({exc}); keeping the original draft")
                _restore_repair_draft(draft_path, original)
                return correction_turn

            try:
                corrected = _read_repair_draft(cfg, f)
            except InvalidRepairRequest:
                if original is None:
                    raise
                _log(f"  WARNING: {f.id}: correction removed the usable draft; keeping the original draft")
                _restore_repair_draft(draft_path, original)
                return correction_turn

            corrected_warning = _repair_draft_warning(cfg, f, corrected)
            if corrected_warning is not None:
                _log(f"  WARNING: {corrected_warning} (continuing with the non-empty draft)")
            return correction_turn

        # Turn 1 — Reproducer (neutral): investigate + reproduce.
        a_verdict, a_text = run_turn(
            cfg,
            f,
            "A",
            1,
            prompt_reproduce(cfg, f, repo_for_agent),
            cwd=_fresh_turn_cwd(f, "A", 1),
        )
        debate.write_text(
            f"# Debate: {f.id}\n\nThis is an INDEX of the debate. Each entry links the turn's "
            f"full agent log — open the logs you need; they are not inlined here.\n"
            + _debate_entry(f, "A", 1, "A (turn 1 — reproduce)", a_verdict)
        )
        _validate_turn_output(f, a_verdict, a_text)
        assert a_verdict is not None
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
            b_verdict, b_text = run_turn(
                cfg,
                f,
                "B",
                turn,
                prompt_challenge(cfg, f, repo_for_agent, str(debate)),
                cwd=_fresh_turn_cwd(f, "B", turn),
            )
            debate.write_text(debate.read_text() + _debate_entry(f, "B", turn, f"B (round {rnd})", b_verdict))
            _validate_turn_output(f, b_verdict, b_text)
            assert b_verdict is not None
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
            a_verdict, a_text = run_turn(
                cfg,
                f,
                "A",
                turn,
                prompt_defend(cfg, f, repo_for_agent, str(debate)),
                cwd=_fresh_turn_cwd(f, "A", turn),
            )
            debate.write_text(debate.read_text() + _debate_entry(f, "A", turn, f"A (round {rnd})", a_verdict))
            _validate_turn_output(f, a_verdict, a_text)
            assert a_verdict is not None
            if a_verdict == "PENDING REPAIR":
                turn = prepare_pending(turn)
            defenses.append(a_text)
            _log(f"  [{f.id}] round {rnd}: B={b_verdict} A={a_verdict}")
            if a_verdict and b_verdict and a_verdict == b_verdict:
                return _final_outcome(cfg, f, a_verdict, True, rnd, _compose_evidence(initial_text, defenses))
        _log(f"  [{f.id}] no consensus after {cfg.rounds} rounds → NEEDS MORE INFO")
        return _final_outcome(cfg, f, "NEEDS MORE INFO", False, cfg.rounds, _compose_evidence(initial_text, defenses))
    finally:
        cleanup()


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
        }.get(adapter)
        model_value = (os.environ.get(model_env) or None) if model_env is not None else None
        model = {"source": model_env if model_value is not None else "adapter-default", "value": model_value}

    if cfg.effort is not None:
        effort = {"source": "specula", "value": cfg.effort}
    elif adapter == "claude-code":
        # run_agent_blocking explicitly injects max, overriding CLAUDE_EFFORT.
        effort = {"source": "specula-default", "value": "max"}
    elif adapter == "codex":
        effort_value = os.environ.get("CODEX_EFFORT") or None
        effort = {
            "source": "CODEX_EFFORT" if effort_value is not None else "adapter-default",
            "value": effort_value,
        }
    else:
        effort = {"source": "adapter-default", "value": None}
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
    head = subprocess.run(["git", "-C", repo, "rev-parse", "HEAD"], capture_output=True)
    if head.returncode != 0:
        if cfg.worktree:
            raise ConfirmationFailed(f"worktree isolation requested but {repo!r} is not a git checkout")
        return {"path": str(Path(repo).resolve()), "head": "non-git", "isolation": "False"}
    root_result = subprocess.run(["git", "-C", repo, "rev-parse", "--show-toplevel"], capture_output=True)
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
    diff = subprocess.run(["git", "-C", str(root), "diff", "--binary", "HEAD", *pathspec], capture_output=True)
    status = subprocess.run(
        ["git", "-C", str(root), "status", "--porcelain", "--untracked-files=all", *pathspec],
        capture_output=True,
    )
    untracked = subprocess.run(
        ["git", "-C", str(root), "ls-files", "--others", "--exclude-standard", "-z", *pathspec],
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
    return _digest(
        {
            "version": _CACHE_VERSION,
            "generation": _generation_content(cfg),
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


def run_finding_safe(cfg: ConfirmConfig, f: Finding) -> Outcome:
    """One finding, isolated. A cached terminal verdict short-circuits (idempotent
    retry). A finding that cannot finish — rate limit, infrastructure error, or
    malformed output — is recorded as an INCOMPLETE outcome (error.txt kept for
    diagnosis, and NOT cached so a later retry re-attempts it). It never propagates
    to discard the whole target's report: the rest of the batch still delivers."""
    cached = _load_verdict(f, cfg)
    if cached is not None:
        _log(f"  [{f.id}] cached {cached.status} — skip (idempotent)")
        return cached
    try:
        o = run_finding(cfg, f)
        _save_verdict(o, cfg)
        return o
    except Exception as exc:  # RateLimited / ConfirmationFailed / anything unexpected
        try:
            f.fdir.mkdir(parents=True, exist_ok=True)
            (f.fdir / "error.txt").write_text(traceback.format_exc())
        except OSError:
            pass
        failure_code = quota.RATE_LIMIT_RC if isinstance(exc, RateLimited) else 1
        reason = "rate-limited" if isinstance(exc, RateLimited) else str(exc) or type(exc).__name__
        _log(f"  [{f.id}] INCOMPLETE ({reason}) — see {f.fdir / 'error.txt'}; not cached, a retry re-attempts it")
        return Outcome(
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


_REPORT_RR_ROW_RE = re.compile(r"(?m)^\|\s*(\d+)\s*\|\s*([^|\s]+)\s*\|\s*([^|]+?)\s*\|\s*$")
_REPORT_DETAIL_RE = re.compile(r"(?m)^##\s+Bug\s+(\d+)\s*:")


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
    report = cfg.ws.work_dir(cfg.name) / "spec" / "confirmed-bugs.md"
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
    report = cfg.ws.work_dir(cfg.name) / "spec" / "confirmed-bugs.md"
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
                    f"report Bug {bug_no} has an RR reference with invalid status {rendered_status!r}"
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
        if detail_statuses != [rendered_status]:
            raise InvalidRepairRequest(f"report Bug {bug_no} table/detail repair status is inconsistent")

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
        # bug_id points at the confirmed-bugs.md heading (## Bug N:) used by the
        # report and ledger; finding_id separately preserves the stable raw id.
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


def _family_refs(value: Any) -> set[str]:
    if isinstance(value, int):
        return {f"Family {value}"}
    if not isinstance(value, str):
        return set()
    if value.strip().isdigit():
        return {f"Family {int(value.strip())}"}
    return {f"Family {number}" for number in re.findall(r"\bFamily\s+(\d+)\b", value, re.I)}


def _validate_candidates(
    path: Path,
    expected_mc_ids: set[str] | dict[str, dict[str, Any]] | None = None,
    expected_families: set[str] | None = None,
) -> list[str]:
    """Structural-minimum validation of candidates.json: only what would break
    the per-finding fan-out (unusable id, id collision, unroutable source). The
    stricter completeness / family-dedup / MC-immutability checks were removed on
    purpose — they only fail-closed (withhold) an otherwise-runnable batch without
    improving any verdict, and rejected sound consolidations (a family partly
    absorbed into an MC candidate while its distinct-site residual is emitted as a
    CR candidate is legitimate). Per-finding confirmation tolerates imperfect
    input; a weak candidate surfaces there, not as a whole-batch stop."""
    del expected_mc_ids, expected_families  # intentionally no longer enforced
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


def _expected_brief_families(brief: Path) -> set[str] | None:
    if not brief.is_file():
        return set()
    text = brief.read_text(errors="replace")
    return {f"Family {number}" for number in re.findall(r"(?im)^#{2,4}\s+Family\s+(\d+)\s*:", text)}


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
    expected_families: set[str] | None = None,
) -> bool:
    if _validate_candidates(out, expected, expected_families):
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
    code-review families (modeling-brief) and dedups them into candidates.json.
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
    expected_families = None if external_candidates else _expected_brief_families(brief)
    if source_errs:
        raise ConsolidateFailed(f"invalid model-checking input for {cfg.name}: {source_errs[0]}")
    if out.is_file() and _candidate_cache_valid(cfg, out, expected_mc_ids, expected_families):
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
    # Do not let a failed agent make a stale output look fresh.
    out.unlink(missing_ok=True)
    (spec_dir / _CANDIDATE_CACHE).unlink(missing_ok=True)
    rc, _ = run_agent_blocking(
        cfg.adapter,
        prompt,
        spec_dir / ".consolidate.prompt.md",
        spec_dir / ".consolidate.log",
        phase_key=PHASE_KEY,
        work_dir=wd,
        claude_alias=cfg.claude_alias,
        max_turns=cfg.max_turns,
        model=cfg.model,
        effort=cfg.effort,
    )
    if rc == 75:
        raise RateLimited(f"{cfg.name} consolidate")
    if rc != 0:
        out.unlink(missing_ok=True)
        raise ConsolidateFailed(f"consolidate adapter exited {rc}")
    errs = (
        _validate_candidates(out, expected_mc_ids, expected_families)
        if out.is_file()
        else ["no candidates.json produced"]
    )
    if errs:
        if out.is_file():
            out.unlink()  # drop the invalid file so load_findings does not choke on it
        raise ConsolidateFailed(f"no valid candidates.json for {cfg.name}: {errs[0]}")
    _write_candidate_cache(cfg, out)
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
        if re.match(r"^##\s+Bug\s+\d+\s*:", line, re.I):
            line = "\\" + line
        lines.append(line)
    return "\n".join(lines).strip()


def aggregate(cfg: ConfirmConfig, outcomes: list[Outcome]) -> None:
    """Write the phase's confirmed-bugs.md from the per-finding outcomes. This is
    the canonical Phase-4 deliverable the classification phase (Phase 4b) and the
    repair loop read; A/B isolation is handled by the run dir, not by a separate
    filename. Headers are ``## Bug N:`` (integer N, table order) so Phase 4b's
    "one row per ``## Bug N:`` header" parsing aligns; the finding id (MC-1 / CR-2)
    is carried as a body field and a table column."""
    report = cfg.ws.work_dir(cfg.name) / "spec" / "confirmed-bugs.md"

    def effective_status(outcome: Outcome) -> str:
        if outcome.status != "PENDING REPAIR" or outcome.rr is None:
            return outcome.status
        deferred = cfg.ws.work_dir(cfg.name) / "spec" / "repair-requests" / "deferred" / f"{outcome.rr}.md"
        if not deferred.is_file():
            return outcome.status
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

    lines = [f"# Confirmed Bugs — {cfg.name}", ""]
    split = (
        f"Reproduced: {len(reproduced)} = {n_new} NEW + {n_known_unfixed} KNOWN-unfixed"
        f" + {n_known_fixed} KNOWN-fixed + {n_unknown} UNKNOWN"
    )
    lines.append(split)
    # The "finding" tier — real defects that are not confirmed live bugs: real but
    # only triggerable in production (env-limited), or a real anomaly whose
    # consequence a safeguard currently masks. Reported separately so they are
    # neither miscounted as bugs nor lost as false positives.
    lines.append(f"Findings: {len(env_limited) + len(masked)} = {len(env_limited)} env-limited + {len(masked)} masked")
    lines.append(
        f"Dispositions: {len(outcomes)} total = {status_counts['REPRODUCED']} reproduced"
        f" + {status_counts['ENV_LIMITED']} env-limited + {status_counts['MASKED']} masked"
        f" + {status_counts['FALSE POSITIVE']} false-positive + {status_counts['NEEDS MORE INFO']} needs-more-info"
        f" + {status_counts['DROPPED']} dropped + {status_counts['PENDING REPAIR']} pending-repair"
        f" + {len(incomplete)} incomplete + {deferred_count} deferred"
    )
    lines.append("")
    lines.append("| Bug | Finding | Status |")
    lines.append("|---|---|---|")
    for o, status in effective:
        if status == "DEFERRED":
            rendered_status = f"DEFERRED (repair loop exhausted; {o.rr} in deferred/)"
        else:
            rr = f" ({o.rr})" if o.rr else ""
            rendered_status = f"{status}{rr}"
        lines.append(f"| {o.bug_no} | {o.finding.id} | {rendered_status} |")
    lines.append("")
    for o, status in effective:
        if status == "DEFERRED":
            rendered_status = f"DEFERRED (repair loop exhausted; {o.rr} in deferred/)"
        else:
            rr = f" ({o.rr})" if o.rr else ""
            rendered_status = f"{status}{rr}"
        title = re.sub(r"[\r\n]+", " ", str(o.finding.data.get("title", ""))).strip()
        lines.append(f"## Bug {o.bug_no}: {title}")
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
    conf_root = wd / "confirmation"
    doc = json.loads(path.read_text())
    errs = _validate_candidates(path) if path.name == "candidates.json" else []
    if errs:
        raise ConfirmationFailed(f"invalid candidate input: {errs[0]}")
    findings: list[Finding] = []
    for data in doc.get("findings", []):
        fid = str(data.get("id", ""))
        if not fid or set(fid) - ID_CHARS or fid in {".", ".."}:
            raise ConfirmationFailed(f"unsafe finding id: {fid!r}")
        findings.append(Finding(data, conf_root / fid))
    return findings


def run_parallel_confirmation(cfg: ConfirmConfig) -> int:
    """Drive step 0 (consolidate) → per-finding fan-out → aggregate for ONE
    target. Returns 75 for exclusively rate-limited incomplete findings and 1 for
    permanent/format/infrastructure incomplete findings while retaining their
    partial report. Pre-fan-out or aggregation failures withhold the deliverable."""
    try:
        try:
            if not cfg.dry_run:
                log_path = cfg.ws.work_dir(cfg.name) / "bug-confirmation.log"
                log_path.parent.mkdir(parents=True, exist_ok=True)
                log_path.write_text("")  # summary link + `tail -f` follow THIS run
                _set_log_file(log_path)
            return _drive_confirmation(cfg)
        except Exception as exc:
            try:
                _log(f"confirmation driver crashed ({exc})")
            except OSError:
                print(f"confirmation driver crashed ({exc})", flush=True)
            if cfg.dry_run:
                return 1
            return _withhold(cfg, "confirmation driver failure — deliverable withheld")
    finally:
        _set_log_file(None)


def _withhold(cfg: ConfirmConfig, reason: str, code: int = 1) -> int:
    """Remove a stale deliverable and return an actionable failure code."""
    report = cfg.ws.work_dir(cfg.name) / "spec" / "confirmed-bugs.md"
    if not cfg.dry_run and report.is_file():
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
    try:
        consolidate(cfg)
    except RateLimited:
        return _withhold(
            cfg,
            "consolidate rate-limited — deliverable withheld for scheduler retry",
            quota.RATE_LIMIT_RC,
        )
    except ConsolidateFailed as e:
        return _withhold(cfg, f"consolidate failed ({e}) — deliverable withheld; downstream gate + retry settle it")

    try:
        findings = load_findings(cfg)
    except (ConfirmationFailed, OSError, ValueError, TypeError) as exc:
        return _withhold(cfg, f"candidate loading failed ({exc}) — deliverable withheld")
    _log(
        f"Parallel confirmation: {cfg.name} — {len(findings)} findings, "
        f"debate={'ON' if cfg.debate else 'OFF'}, max_parallel={cfg.max_parallel}"
    )
    if cfg.dry_run:
        for finding in findings:
            _log(f"    [{finding.id}] [DRY] would run confirmation")
        return 0
    if not findings:
        aggregate(cfg, [])
        return _post_validate_repair_state(cfg)

    outcomes: list[Outcome] = []
    unstarted: list[Finding] = []
    next_finding = 0
    rate_limit_seen = threading.Event()

    def run_scheduled(finding: Finding) -> Outcome | None:
        # A future may have been submitted before another worker reports a rate
        # limit but not have started confirmation yet. Keep that finding untouched
        # so the scheduler retry can run it later.
        if rate_limit_seen.is_set():
            return None
        outcome = run_finding_safe(cfg, finding)
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
            while not rate_limit_seen.is_set() and next_finding < len(findings) and len(in_flight) < cfg.max_parallel:
                finding = findings[next_finding]
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
        unstarted.extend(findings[next_finding:])
        for finding in unstarted:
            cached = _load_verdict(finding, cfg)
            if cached is not None:
                _log(f"  [{finding.id}] cached {cached.status} — preserve after batch rate limit")
                outcomes.append(cached)
                continue
            _log(f"  [{finding.id}] INCOMPLETE (not started after batch rate limit) — not cached; retry later")
            outcomes.append(
                Outcome(
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
            )
    # Partial delivery beats total loss: a finding that could not finish is an
    # INCOMPLETE row, clearly marked; every completed finding is still reported. A
    # single infra error / rate limit no longer withholds the whole target.
    order = {f.id: i for i, f in enumerate(findings)}
    outcomes.sort(key=lambda o: order[o.finding.id])
    for i, o in enumerate(outcomes, 1):
        o.bug_no = i  # the "## Bug N:" number, in table order (drives aggregate + the RR bug_id)
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
