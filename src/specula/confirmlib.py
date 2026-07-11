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
import shutil
import subprocess
import threading
import traceback
from collections.abc import Callable
from concurrent.futures import ThreadPoolExecutor
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
_CACHE_VERSION = 2
_CANDIDATE_CACHE = ".candidates-cache.json"

_VERDICT_RE = re.compile(r"^\s*VERDICT:\s*(.+?)\s*$", re.MULTILINE)
_rr_lock = threading.Lock()
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


# ── prompt builders ──────────────────────────────────────────────────────────


def _context(cfg: ConfirmConfig, f: Finding, repo_for_agent: str) -> str:
    wd = cfg.ws.work_dir(cfg.name)
    return render(
        "confirmation/context",
        finding_json=json.dumps(f.data, indent=2, ensure_ascii=False),
        repo=repo_for_agent,
        spec_dir=str(wd / "spec"),
        repro_dir=str(wd / "repro"),
        fdir=str(f.fdir),
        finding_id=f.id,
        bug_confirmation_skill=prompt_skill_ids("bug-confirmation"),
    )


def prompt_reproduce(cfg: ConfirmConfig, f: Finding, repo: str) -> str:
    return (
        render(
            "confirmation/reproduce",
            finding_id=f.id,
            canon=" / ".join(CANON),
            fdir=str(f.fdir),
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
            context=_context(cfg, f, repo),
        )
        + cfg.prompt_extra
    )


# ── one debate turn (blocking, via the shared phaselib primitive) ────────────


def run_turn(cfg: ConfirmConfig, f: Finding, role: str, turn_no: int, prompt: str) -> tuple[str | None, str]:
    """Run one agent turn synchronously; return (verdict, response text).

    Raises :class:`RateLimited` on adapter exit 75 — the turn is never silently
    downgraded to a terminal verdict; the caller withholds the deliverable so the
    scheduler retries."""
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
        work_dir=cfg.ws.work_dir(cfg.name),
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


# ── per-finding git worktree (build isolation) ───────────────────────────────


def setup_repo(cfg: ConfirmConfig, f: Finding) -> tuple[str, Callable[[], None]]:
    """Return (repo_path_for_agent, cleanup). With worktree (default) each finding
    gets its own detached worktree so parallel builds do not collide. If a worktree
    cannot be created (permissions, non-git repo, unconfigured), fall back to the
    shared repo rather than failing the finding — isolation is a build-safety
    optimisation, not a correctness requirement."""
    repo = cfg.repo_dir.rstrip("/")
    if not cfg.worktree or cfg.dry_run or not repo:
        return repo, lambda: None
    try:
        return _setup_worktree(cfg, f, repo)
    except Exception as exc:
        _log(f"  [{f.id}] worktree isolation unavailable ({str(exc)[:150]}); using the shared repo")
        return repo, lambda: None


def _setup_worktree(cfg: ConfirmConfig, f: Finding, repo: str) -> tuple[str, Callable[[], None]]:
    """Per-finding detached git worktree with the launch dir's local changes copied
    in. Raises on any failure; setup_repo turns that into a shared-repo fallback."""
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
    wt = f.fdir / "worktree"
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
    # PENDING REPAIR: the agent's repair-request.body.md is taken best-effort.
    # _merge_rr stamps the dispatcher-owned lifecycle and strips stray owned keys,
    # so an imperfectly-formatted RR body never discards the verdict — the contract
    # was never fully specified to the agent, so we do not punish it for shape.


def _validate_initial_output(cfg: ConfirmConfig, f: Finding, status: str | None, text: str) -> str:
    """Validate stable machine-level output without prescribing prose headings."""
    evidence = _validate_turn_output(f, status, text)
    assert status is not None
    _validate_final_artifacts(cfg, f, status)
    return evidence


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
    repro_dir = cfg.ws.work_dir(cfg.name) / "repro"
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
        # Turn 1 — Reproducer (neutral): investigate + reproduce.
        a_verdict, a_text = run_turn(cfg, f, "A", 1, prompt_reproduce(cfg, f, repo_for_agent))
        debate.write_text(
            f"# Debate: {f.id}\n\nThis is an INDEX of the debate. Each entry links the turn's "
            f"full agent log — open the logs you need; they are not inlined here.\n"
            + _debate_entry(f, "A", 1, "A (turn 1 — reproduce)", a_verdict)
        )
        _validate_initial_output(cfg, f, a_verdict, a_text)
        assert a_verdict is not None
        initial_text = a_text
        if a_verdict not in CONFIRM:
            _log(f"  [{f.id}] A: {a_verdict} (dismissal) — no debate")
            return _final_outcome(cfg, f, a_verdict, True, 0, _compose_evidence(a_text, []))
        if not cfg.debate:
            _log(f"  [{f.id}] A: {a_verdict} (debate off) — verdict final")
            return _final_outcome(cfg, f, a_verdict, True, 0, _compose_evidence(a_text, []))

        _log(f"  [{f.id}] A: {a_verdict} → opening debate")
        defenses: list[str] = []
        turn = 1
        for rnd in range(1, cfg.rounds + 1):
            turn += 1
            b_verdict, b_text = run_turn(cfg, f, "B", turn, prompt_challenge(cfg, f, repo_for_agent, str(debate)))
            debate.write_text(debate.read_text() + _debate_entry(f, "B", turn, f"B (round {rnd})", b_verdict))
            _validate_turn_output(f, b_verdict, b_text)
            assert b_verdict is not None
            # B agrees with A's current verdict → consensus already. Do NOT pull A
            # into a defense it does not need: A only ever hears about the debate
            # when B actually disagrees (the defend turn is where it is introduced).
            if b_verdict is not None and b_verdict == a_verdict:
                _log(f"  [{f.id}] round {rnd}: B={b_verdict} agrees — consensus, A not invoked")
                return _final_outcome(cfg, f, a_verdict, True, rnd, _compose_evidence(initial_text, defenses))
            turn += 1
            a_verdict, a_text = run_turn(cfg, f, "A", turn, prompt_defend(cfg, f, repo_for_agent, str(debate)))
            debate.write_text(debate.read_text() + _debate_entry(f, "A", turn, f"A (round {rnd})", a_verdict))
            _validate_turn_output(f, a_verdict, a_text)
            assert a_verdict is not None
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
    for name in ("context.md", "reproduce.md", "challenge.md", "defend.md"):
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
    prefix = key + ":"
    return [line[len(prefix) :].strip() for line in text.splitlines()[:25] if line.startswith(prefix)]


def _artifact_identity(cfg: ConfirmConfig, o: Outcome) -> dict[str, Any]:
    _validate_final_artifacts(cfg, o.finding, o.status)
    result: dict[str, Any] = {}
    if o.status == "REPRODUCED":
        result["repro"] = {
            path.name: hashlib.sha256(path.read_bytes()).hexdigest() for path in sorted(_repro_files(cfg, o.finding))
        }
    if o.status == "PENDING REPAIR":
        body_file = o.finding.fdir / "repair-request.body.md"
        result["repair_body"] = hashlib.sha256(body_file.read_bytes()).hexdigest()
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
        if ids != [o.rr] or len(statuses) != 1 or statuses[0] not in {"OPEN", "IN_REPAIR", "CONSUMED"}:
            raise InvalidRepairRequest(f"cached repair {o.rr} has invalid id/status frontmatter")
        result["repair_request"] = {
            "path": str(rr_file.relative_to(rr_dir)),
            "content": hashlib.sha256(rr_file.read_bytes()).hexdigest(),
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
        )


# ── RR-NNN allocation (serial) — dispatcher stamps lifecycle, agent owns scope ─

# Lifecycle frontmatter fields the dispatcher owns and always overrides; every
# other frontmatter line (target, counterexample, the whole scope: block) is the
# agent's and passes through verbatim.
_RR_OWNED = ("id:", "bug_id:", "status:", "round:", "finding_id:", "allocation_key:")


def _repair_frontmatter(body: str) -> tuple[list[str], str]:
    """Split an agent RR body into (frontmatter lines, evidence rest). Best-effort:
    a body without a well-formed `---` header is treated as all-evidence with no
    frontmatter, not rejected — _merge_rr stamps the required lifecycle itself."""
    if not body.startswith("---"):
        return [], body
    parts = body.split("---", 2)
    if len(parts) != 3:
        return [], body
    return parts[1].splitlines(), parts[2]


def _merge_rr(
    rid: str,
    finding_id: str,
    cx_fallback: str,
    body: str,
    *,
    raw_finding_id: str = "",
    allocation_key: str = "",
) -> str:
    """Stamp dispatcher-owned lifecycle fields onto the agent-authored RR body.

    Best-effort: the agent's target/counterexample/scope pass through untouched,
    stray dispatcher-owned keys are stripped (below), and a body with no/partial
    frontmatter still yields a well-formed request (the lifecycle header is always
    added). RR-body shape is never a reason to discard the PENDING REPAIR verdict.
    ``cx_fallback`` is kept in the signature for API compatibility, unused."""
    del cx_fallback
    lifecycle = f"id: {rid}\nbug_id: {finding_id}\nstatus: OPEN\nround: 0\n"
    if raw_finding_id:
        lifecycle += f"finding_id: {raw_finding_id}\n"
    if allocation_key:
        lifecycle += f"allocation_key: {allocation_key}\n"
    fm_lines, rest = _repair_frontmatter(body)
    # top-level (unindented) frontmatter lines only; the indented scope children
    # keep their leading whitespace so they are never mistaken for owned fields.
    kept = [ln for ln in fm_lines if not (ln == ln.lstrip() and ln.startswith(_RR_OWNED))]
    kept_fm = "\n".join(kept).strip("\n")
    return f"---\n{lifecycle}{kept_fm}\n---{rest}"


def allocate_rr(cfg: ConfirmConfig, o: Outcome) -> str:
    """Serially assign the next RR-NNN and file the agent-authored request."""
    body_file = o.finding.fdir / "repair-request.body.md"
    body = body_file.read_text() if body_file.is_file() else ""
    rr_dir = cfg.ws.work_dir(cfg.name) / "spec" / "repair-requests"
    with _rr_lock:
        rr_dir.mkdir(parents=True, exist_ok=True)
        allocation_key = _digest(
            {
                "verdict": _verdict_fingerprint(cfg, o.finding),
                "repair_body": hashlib.sha256(body.encode()).hexdigest(),
                "cache_version": _CACHE_VERSION,
            }
        )
        existing: list[str] = []
        for path in rr_dir.rglob("RR-*.md"):
            text = path.read_text(errors="replace")
            keys = _rr_field_text(text, "allocation_key")
            statuses = _rr_field_text(text, "status")
            ids = _rr_field_text(text, "id")
            finding_ids = _rr_field_text(text, "finding_id")
            if keys == [allocation_key] and statuses and statuses[0] in {"OPEN", "IN_REPAIR"}:
                if finding_ids != [o.finding.id]:
                    raise InvalidRepairRequest(f"existing allocation key has wrong finding_id for {o.finding.id}")
                if len(ids) != 1 or path.name != f"{ids[0]}.md":
                    raise InvalidRepairRequest(f"existing allocation for {o.finding.id} has inconsistent id")
                existing.append(ids[0])
        if len(existing) > 1:
            raise InvalidRepairRequest(f"multiple repair requests already exist for {o.finding.id} in this generation")
        if existing:
            return existing[0]
        nums = [int(m.group(1)) for p in rr_dir.rglob("RR-*.md") if (m := re.fullmatch(r"RR-(\d+)\.md", p.name))]
        next_num = max(nums, default=0) + 1
        cx = str(o.finding.data.get("counterexample") or "")
        # bug_id points at the confirmed-bugs.md heading (## Bug N:) used by the
        # report and ledger; finding_id separately preserves the stable raw id.
        while True:
            rid = f"RR-{next_num:03d}"
            merged = _merge_rr(
                rid,
                f"Bug {o.bug_no}",
                cx,
                body,
                raw_finding_id=o.finding.id,
                allocation_key=allocation_key,
            )
            try:
                # Final guard against an external writer racing the in-process
                # lock. Never overwrite or renumber repair history.
                with (rr_dir / f"{rid}.md").open("x") as fh:
                    fh.write(merged)
                break
            except FileExistsError:
                next_num += 1
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
    # A non-canonical status (e.g. INCOMPLETE from a finding whose confirmation
    # could not finish — infra error / rate limit) is rendered verbatim and simply
    # not counted as a bug/finding; it must never discard the whole report.
    incomplete = [o for o in outcomes if o.status not in CANON]
    status_counts = {status: sum(o.status == status for o in outcomes) for status in CANON}
    reproduced = [o for o in outcomes if o.status == "REPRODUCED"]
    nov = [_novelty(o.body) for o in reproduced]
    n_new = nov.count("NEW")
    n_known_unfixed = nov.count("KNOWN-unfixed")
    n_known_fixed = nov.count("KNOWN-fixed")
    n_unknown = nov.count("UNKNOWN")

    env_limited = [o for o in outcomes if o.status == "ENV_LIMITED"]
    masked = [o for o in outcomes if o.status == "MASKED"]

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
        f" + {len(incomplete)} incomplete + 0 deferred"
    )
    lines.append("")
    lines.append("| Bug | Finding | Status |")
    lines.append("|---|---|---|")
    for o in outcomes:
        rr = f" ({o.rr})" if o.rr else ""
        lines.append(f"| {o.bug_no} | {o.finding.id} | {o.status}{rr} |")
    lines.append("")
    for o in outcomes:
        rr = f" ({o.rr})" if o.rr else ""
        title = re.sub(r"[\r\n]+", " ", str(o.finding.data.get("title", ""))).strip()
        lines.append(f"## Bug {o.bug_no}: {title}")
        lines.append("")
        lines.append(f"- **Finding ID**: {o.finding.id}")
        lines.append(f"- **Status**: {o.status}{rr}")
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
    wd = cfg.ws.work_dir(cfg.name)
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
    target. Returns 75 for rate limiting, nonzero for permanent/infrastructure
    failures, and always removes a stale deliverable on failure."""
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


def _drive_confirmation(cfg: ConfirmConfig) -> int:
    if cfg.max_parallel < 1:
        return _withhold(cfg, "invalid max_parallel; expected a positive integer")
    if cfg.debate and cfg.rounds < 1:
        return _withhold(cfg, "invalid debate rounds; expected a positive integer")
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
        return 0

    outcomes: list[Outcome] = []
    with ThreadPoolExecutor(max_workers=cfg.max_parallel) as ex:
        futures = [(f, ex.submit(run_finding_safe, cfg, f)) for f in findings]
        for finding, fut in futures:
            try:
                outcomes.append(fut.result())
            except Exception as exc:  # run_finding_safe absorbs failures; stay robust regardless
                _log(f"  [{finding.id}] worker crashed unexpectedly ({exc})")
                outcomes.append(
                    Outcome(
                        finding,
                        INCOMPLETE,
                        consensus=False,
                        rounds=0,
                        body=f"## Confirmation result\nINCOMPLETE — worker crashed: {exc}.",
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
    return 0
