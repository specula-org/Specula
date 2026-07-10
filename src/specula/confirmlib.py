"""Parallel per-finding bug confirmation (Phase 4).

The default Phase-4 mode: instead of one agent confirming every finding in one
context (the legacy single-agent path, still reachable via ``--legacy-confirm``),
this fans out one Reproducer agent per finding, in parallel, after a step-0
consolidate+dedup of the two finding sources into ``candidates.json``. The
Reproducer follows the bug-confirmation skill (``guide.md`` + phase docs); this
module is the dispatcher: it owns the per-finding work, serial RR-NNN allocation,
and aggregation into ``confirmed-bugs.md``.

Every agent turn goes through :func:`specula.phaselib.run_agent_blocking` — the
same adapter path, flags, and stop-gate env as ``Phase._launch``. Rate-limit
(adapter exit 75) is NOT swallowed into a per-finding verdict (``NEEDS MORE
INFO`` is terminal and the pipeline never revisits it, so a transient blip would
lose the finding forever). It is handled the way a batch phase handles a mid-run
agent death: the deliverable is **withheld** — ``confirmed-bugs.md`` is not
written — so the classification phase's prerequisite gate stops the pipeline and
the scheduler's transient-log retry re-runs this phase. No special exit code is
propagated: that would single this phase out from its batch siblings (all of
which return 0 and let the downstream gate + scheduler log-probe drive retries).
A retry skips findings that already carry a terminal verdict (idempotent
``verdict.json``), so only the interrupted findings re-run.
"""

from __future__ import annotations

import json
import re
import subprocess
import threading
import traceback
from collections.abc import Callable
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from specula.phaselib import SPECULA_ROOT, Workspace, run_agent_blocking
from specula.prompts import render

SKILLS = SPECULA_ROOT / "skills"
PHASE_KEY = "bug_confirmation"

# Framework terminal/loop statuses (skills/bug-confirmation/guide.md).
CANON = ["REPRODUCED", "REPRODUCTION FAILED", "FALSE POSITIVE", "NEEDS MORE INFO", "DROPPED", "PENDING REPAIR"]
VALID_SOURCES = {"model-checking", "code-review"}
ID_CHARS = set("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789._-")

_VERDICT_RE = re.compile(r"^\s*VERDICT:\s*(.+?)\s*$", re.MULTILINE)
_rr_lock = threading.Lock()
_print_lock = threading.Lock()
_log_file: Path | None = None  # when set, _log also tees here (the phase's bug-confirmation.log)


def _set_log_file(path: Path | None) -> None:
    global _log_file
    _log_file = path


class RateLimited(Exception):
    """A turn hit adapter exit 75 (rate limit). A purely internal control-flow
    signal: run_parallel_confirmation catches it and withholds the deliverable
    (writes no confirmed-bugs.md) so the classification gate + the scheduler's
    transient-log retry re-run the phase. Never a per-finding NEEDS MORE INFO
    (terminal, never revisited), and never a special phase exit code."""


class ConsolidateFailed(Exception):
    """Consolidate ran (not rate-limited) but produced no valid candidates.json.
    Treated like any batch-phase agent failure: the driver withholds the
    deliverable and returns 0 so the downstream gate + the scheduler's
    transient-log retry settle it — never a hard RuntimeError, which that probe
    cannot retry and which would single this phase out from its batch siblings."""


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


@dataclass
class Outcome:
    finding: Finding
    status: str
    consensus: bool
    rounds: int
    body: str  # the Reproducer's response, used as the verdict body
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
        skills=str(SKILLS),
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


# ── one agent turn (blocking, via the shared phaselib primitive) ─────────────


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
    )
    if rc == 75:
        raise RateLimited(f"{f.id} turn {turn_no} {role}")
    return parse_verdict(text), text


# ── per-finding git worktree (build isolation) ───────────────────────────────


def setup_repo(cfg: ConfirmConfig, f: Finding) -> tuple[str, Callable[[], None]]:
    """Return (repo_path_for_agent, cleanup). With worktree (default) each finding
    gets its own detached worktree so parallel builds do not collide."""
    repo = cfg.repo_dir.rstrip("/")
    if not cfg.worktree or not repo or cfg.dry_run:
        return repo, lambda: None
    if not (Path(repo) / ".git").exists():
        _log(f"  [{f.id}] repo is not a git checkout — sharing tree (no worktree)")
        return repo, lambda: None
    wt = f.fdir / "worktree"
    try:
        subprocess.run(
            ["git", "-C", repo, "worktree", "add", "--detach", "--force", str(wt)],
            check=True,
            capture_output=True,
            text=True,
        )
    except subprocess.CalledProcessError as e:
        _log(f"  [{f.id}] worktree add failed ({e.stderr.strip()[:80]}) — sharing tree")
        return repo, lambda: None

    def cleanup() -> None:
        subprocess.run(["git", "-C", repo, "worktree", "remove", "--force", str(wt)], capture_output=True)

    return str(wt), cleanup


# ── one finding: reproduce → verdict ─────────────────────────────────────────


def run_finding(cfg: ConfirmConfig, f: Finding) -> Outcome:
    f.fdir.mkdir(parents=True, exist_ok=True)
    (cfg.ws.work_dir(cfg.name) / "repro").mkdir(parents=True, exist_ok=True)
    transcript = f.fdir / "debate.md"
    repo_for_agent, cleanup = setup_repo(cfg, f)
    try:
        a_verdict, a_text = run_turn(cfg, f, "A", 1, prompt_reproduce(cfg, f, repo_for_agent))
        transcript.write_text(f"# {f.id}\n\n## Reproduce\n\n{a_text}\n")
        if a_verdict is None:
            _log(f"  [{f.id}] Reproducer produced no VERDICT → NEEDS MORE INFO")
            return Outcome(f, "NEEDS MORE INFO", False, 0, a_text)
        _log(f"  [{f.id}] {a_verdict}")
        return Outcome(f, a_verdict, True, 0, a_text)
    finally:
        cleanup()


# ── idempotent per-finding verdict cache (survives a rate-limit phase retry) ──


def _save_verdict(o: Outcome) -> None:
    o.finding.fdir.mkdir(parents=True, exist_ok=True)
    (o.finding.fdir / "verdict.json").write_text(
        json.dumps(
            {"status": o.status, "consensus": o.consensus, "rounds": o.rounds, "rr": o.rr, "body": o.body},
            ensure_ascii=False,
        )
    )


def _load_verdict(f: Finding) -> Outcome | None:
    vf = f.fdir / "verdict.json"
    if not vf.is_file():
        return None
    try:
        d = json.loads(vf.read_text())
    except (OSError, ValueError):
        return None
    return Outcome(f, str(d["status"]), bool(d["consensus"]), int(d["rounds"]), str(d["body"]), d.get("rr"))


def run_finding_safe(cfg: ConfirmConfig, f: Finding) -> Outcome:
    """One finding, isolated. A cached terminal verdict short-circuits (idempotent
    retry). A RateLimited turn propagates (aborts the phase). Any other exception
    is contained as NEEDS MORE INFO so one finding cannot abort the batch."""
    cached = _load_verdict(f)
    if cached is not None:
        _log(f"  [{f.id}] cached {cached.status} — skip (idempotent)")
        return cached
    try:
        o = run_finding(cfg, f)
    except RateLimited:
        raise  # rate limit aborts the phase; do NOT persist or downgrade
    except Exception:
        f.fdir.mkdir(parents=True, exist_ok=True)
        (f.fdir / "error.txt").write_text(traceback.format_exc())
        _log(f"  [{f.id}] CRASHED — see {f.fdir / 'error.txt'} → NEEDS MORE INFO")
        o = Outcome(f, "NEEDS MORE INFO", False, 0, "(finding crashed during confirmation; see error.txt)")
    _save_verdict(o)
    return o


# ── RR-NNN allocation (serial) — dispatcher stamps lifecycle, agent owns scope ─

# Lifecycle frontmatter fields the dispatcher owns and always overrides; every
# other frontmatter line (target, counterexample, the whole scope: block) is the
# agent's and passes through verbatim.
_RR_OWNED = ("id:", "bug_id:", "status:", "round:")


def _merge_rr(rid: str, finding_id: str, cx_fallback: str, body: str) -> str:
    """Stamp dispatcher-owned lifecycle fields onto the agent-authored RR body.

    Keeps the agent's target/counterexample/scope untouched; injects
    target/counterexample only when the agent omitted them; never fabricates
    scope. Falls back to a minimal stub only when the agent produced no
    frontmatter at all — an agent-side defect, flagged in the body."""
    lifecycle = f"id: {rid}\nbug_id: {finding_id}\nstatus: OPEN\nround: 0\n"
    fm = None
    rest = body
    if body.startswith("---"):
        parts = body.split("---", 2)  # ["", <frontmatter>, <rest>]
        if len(parts) == 3:
            fm, rest = parts[1], parts[2]
    if fm is None:  # agent wrote no frontmatter — honest stub, empty scope, flagged
        note = (
            "" if body.strip() else "## Trigger\n(agent returned PENDING REPAIR but wrote no repair-request.body.md)\n"
        )
        stub = (
            f"---\n{lifecycle}target: SPEC_REPAIR\ncounterexample: {cx_fallback}\n"
            f"scope:\n  actions: []\n  invariants: []\n  hunt_cfgs: []\n  fault_actions: []\n---\n\n"
        )
        return stub + note + body
    # top-level (unindented) frontmatter lines only; the indented scope children
    # keep their leading whitespace so they are never mistaken for owned fields.
    kept = [ln for ln in fm.splitlines() if not (ln == ln.lstrip() and ln.startswith(_RR_OWNED))]
    top = {ln.split(":", 1)[0] for ln in kept if ln == ln.lstrip() and ":" in ln}
    inject = ""
    if "target" not in top:
        inject += "target: SPEC_REPAIR\n"
    if "counterexample" not in top:
        inject += f"counterexample: {cx_fallback}\n"
    kept_fm = "\n".join(kept).strip("\n")
    return f"---\n{lifecycle}{inject}{kept_fm}\n---{rest}"


def allocate_rr(cfg: ConfirmConfig, o: Outcome) -> str:
    """Serially assign the next RR-NNN and file the agent-authored request."""
    body_file = o.finding.fdir / "repair-request.body.md"
    body = body_file.read_text() if body_file.is_file() else ""
    rr_dir = cfg.ws.work_dir(cfg.name) / "spec" / "repair-requests"
    with _rr_lock:
        rr_dir.mkdir(parents=True, exist_ok=True)
        nums = [int(m.group(1)) for p in rr_dir.glob("RR-*.md") if (m := re.match(r"RR-(\d+)\.md$", p.name))]
        rid = f"RR-{max(nums, default=0) + 1:03d}"
        cx = str(o.finding.data.get("counterexample") or "")
        # bug_id points at the confirmed-bugs.md heading (## Bug N:), the label the
        # re-check pass correlates against — not the raw finding id.
        (rr_dir / f"{rid}.md").write_text(_merge_rr(rid, f"Bug {o.bug_no}", cx, body))
    return rid


# ── step 0: consolidate + dedup the two finding sources into candidates.json ──


def _validate_candidates(path: Path) -> list[str]:
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
        if not isinstance(fid, str) or not fid or set(fid) - ID_CHARS:
            errs.append(f"{where}: id missing or not filesystem-safe: {fid!r}")
        elif fid in seen:
            errs.append(f"{where}: duplicate id {fid!r}")
        else:
            seen.add(fid)
        if f.get("source") not in VALID_SOURCES:
            errs.append(f"{where}: source not in {VALID_SOURCES}: {f.get('source')!r}")
        if not f.get("title"):
            errs.append(f"{where}: empty title")
        if not f.get("summary"):
            errs.append(f"{where}: empty summary")
    return errs


def consolidate(cfg: ConfirmConfig) -> None:
    """Phase-4 step 0: one agent merges MC (bug-report/findings.json) with
    code-review families (modeling-brief) and dedups them into candidates.json.
    Idempotent: a present-and-valid candidates.json is reused. Raises
    RateLimited on exit 75; raises RuntimeError if the output is missing/invalid."""
    wd = cfg.ws.work_dir(cfg.name)
    spec_dir = wd / "spec"
    out = spec_dir / "candidates.json"
    if out.is_file() and not _validate_candidates(out):
        _log(f"  {cfg.name}: candidates.json present and valid — skipping consolidate")
        return
    bug_report = spec_dir / "bug-report.md"
    findings_json = spec_dir / "findings.json"
    brief = wd / "modeling-brief.md"
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
            schema_doc=str(SKILLS / "validation-workflow" / "references" / "findings-json-format.md"),
        )
        + cfg.prompt_extra
    )
    if cfg.dry_run:
        _log(f"  {cfg.name}: [DRY] consolidate → {out}")
        return
    spec_dir.mkdir(parents=True, exist_ok=True)
    rc, _ = run_agent_blocking(
        cfg.adapter,
        prompt,
        spec_dir / ".consolidate.prompt.md",
        spec_dir / ".consolidate.log",
        phase_key=PHASE_KEY,
        work_dir=wd,
        claude_alias=cfg.claude_alias,
    )
    if rc == 75:
        raise RateLimited(f"{cfg.name} consolidate")
    errs = _validate_candidates(out) if out.is_file() else ["no candidates.json produced"]
    if errs:
        if out.is_file():
            out.unlink()  # drop the invalid file so load_findings does not choke on it
        raise ConsolidateFailed(f"no valid candidates.json for {cfg.name}: {errs[0]}")
    doc = json.loads(out.read_text())
    cand = doc.get("findings", [])
    n_merged = sum(1 for c in cand if c.get("dedup_note"))
    _log(f"  {cfg.name}: consolidated {len(cand)} candidates ({n_merged} absorbed a code-review dup)")


# ── aggregation → confirmed-bugs.md ──────────────────────────────────────────


def _novelty(body: str) -> str:
    """Parse the Reproducer's per-bug Novelty: NEW / KNOWN-unfixed / KNOWN-fixed.
    Defaults to NEW when absent (a bug with no novelty claim is treated as new)."""
    m = re.search(r"\*\*Novelty\*\*:\s*(NEW|KNOWN)", body, re.IGNORECASE)
    if not m or m.group(1).upper() == "NEW":
        return "NEW"
    fix = re.search(r"fix-status:\s*(unfixed|fixed)", body, re.IGNORECASE)
    return "KNOWN-fixed" if (fix and fix.group(1).lower() == "fixed") else "KNOWN-unfixed"


def aggregate(cfg: ConfirmConfig, outcomes: list[Outcome]) -> None:
    """Write the phase's confirmed-bugs.md from the per-finding outcomes. This is
    the canonical Phase-4 deliverable the classification phase (Phase 4b) and the
    repair loop read; A/B isolation is handled by the run dir, not by a separate
    filename. Headers are ``## Bug N:`` (integer N, table order) so Phase 4b's
    "one row per ``## Bug N:`` header" parsing aligns; the finding id (MC-1 / CR-2)
    is carried as a body field and a table column."""
    report = cfg.ws.work_dir(cfg.name) / "spec" / "confirmed-bugs.md"
    reproduced = [o for o in outcomes if o.status == "REPRODUCED"]
    nov = [_novelty(o.body) for o in reproduced]
    n_new = nov.count("NEW")
    n_known_unfixed = nov.count("KNOWN-unfixed")
    n_known_fixed = nov.count("KNOWN-fixed")

    lines = [f"# Confirmed Bugs — {cfg.name}", ""]
    split = f"Reproduced: {len(reproduced)} = {n_new} NEW + {n_known_unfixed} KNOWN-unfixed"
    if n_known_fixed:
        split += f"    (KNOWN-fixed: {n_known_fixed} — each needs a version recheck)"
    lines.append(split)
    lines.append("")
    lines.append("| Bug | Finding | Status |")
    lines.append("|---|---|---|")
    for o in outcomes:
        rr = f" ({o.rr})" if o.rr else ""
        lines.append(f"| {o.bug_no} | {o.finding.id} | {o.status}{rr} |")
    lines.append("")
    for o in outcomes:
        rr = f" ({o.rr})" if o.rr else ""
        lines.append(f"## Bug {o.bug_no}: {o.finding.data.get('title', '')}")
        lines.append("")
        lines.append(f"- **Finding ID**: {o.finding.id}")
        lines.append(f"- **Status**: {o.status}{rr}")
        lines.append(f"- **Transcript**: {o.finding.fdir / 'debate.md'}")
        lines.append("")
        lines.append(o.body.strip())
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
    return [Finding(d, conf_root / str(d["id"])) for d in doc.get("findings", [])]


def run_parallel_confirmation(cfg: ConfirmConfig) -> int:
    """Drive step 0 (consolidate) → per-finding fan-out → aggregate for ONE
    target. Always returns 0, like every other batch phase: on a rate limit it
    withholds confirmed-bugs.md rather than propagating a special exit code, and
    the missing deliverable is what the classification gate + the scheduler's
    transient-log retry act on."""
    if not cfg.dry_run:
        log_path = cfg.ws.work_dir(cfg.name) / "bug-confirmation.log"
        log_path.parent.mkdir(parents=True, exist_ok=True)
        log_path.write_text("")  # fresh per run so the summary link + `tail -f` follow THIS run
        _set_log_file(log_path)
    try:
        return _drive_confirmation(cfg)
    finally:
        _set_log_file(None)


def _withhold(cfg: ConfirmConfig, reason: str) -> int:
    """Withhold the phase deliverable and return 0. Removes any existing
    confirmed-bugs.md so the classification gate sees a MISSING deliverable (and
    the scheduler retries) rather than passing on a STALE report left by a prior
    run — the batch-phase failure contract."""
    report = cfg.ws.work_dir(cfg.name) / "spec" / "confirmed-bugs.md"
    if report.is_file():
        report.unlink()
    _log(reason)
    return 0


def _drive_confirmation(cfg: ConfirmConfig) -> int:
    try:
        consolidate(cfg)
    except RateLimited:
        return _withhold(cfg, "consolidate rate-limited — deliverable withheld for scheduler retry")
    except ConsolidateFailed as e:
        return _withhold(cfg, f"consolidate failed ({e}) — deliverable withheld; downstream gate + retry settle it")

    findings = load_findings(cfg)
    _log(f"Parallel confirmation: {cfg.name} — {len(findings)} findings, max_parallel={cfg.max_parallel}")
    if not findings:
        if not cfg.dry_run:
            aggregate(cfg, [])
        return 0

    outcomes: list[Outcome] = []
    rate_limited = False
    with ThreadPoolExecutor(max_workers=cfg.max_parallel) as ex:
        futures = [ex.submit(run_finding_safe, cfg, f) for f in findings]
        for fut in futures:
            try:
                outcomes.append(fut.result())
            except RateLimited:
                rate_limited = True
    if rate_limited:
        # Do NOT aggregate a partial confirmed-bugs.md — it would look complete and
        # the classification gate would pass with findings missing. Withhold it (as
        # a batch phase does when its agent dies mid-run): remove any stale report
        # so the gate + the scheduler's transient-log retry re-run us; verdict.json
        # skips the findings already done. Return 0, consistent with batch phases.
        return _withhold(
            cfg, "rate-limited mid-confirmation — deliverable withheld; completed findings cached for retry"
        )

    order = {f.id: i for i, f in enumerate(findings)}
    outcomes.sort(key=lambda o: order[o.finding.id])
    for i, o in enumerate(outcomes, 1):
        o.bug_no = i  # the "## Bug N:" number, in table order (drives aggregate + the RR bug_id)
    for o in outcomes:
        if o.status.startswith("PENDING REPAIR") and o.rr is None and not cfg.dry_run:
            o.rr = allocate_rr(cfg, o)
            _save_verdict(o)  # persist the assigned RR into the idempotent cache
    if not cfg.dry_run:
        aggregate(cfg, outcomes)
    return 0
