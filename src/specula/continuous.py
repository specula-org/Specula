"""Continuous orchestration: one native main session per target for Phases 1-3.

The main session (phase key ``main``) performs analysis, spec generation,
harness generation, and validation in one native conversation. It may request
native compaction, and every end of its turn is a handoff to this controller
(``context_runner`` binds it to the exact native session, rc 73). The
controller validates the handoff, runs the unchanged one-shot confirmation in
clean contexts, resumes the same conversation for repair requests, and runs the
unchanged classification once no repair work remains.

Durable lifecycle, per target (``<work>/.context-control/``):

``main-state.json`` (controller-owned; atomic writes)
    ``stage``: ``main`` (the main conversation owns the work), ``confirm`` (it
    yielded; a confirmation batch is pending or running), ``closed`` (the
    conversation is finished; classification and summary remain),
    ``classified`` (only the summary remains), or ``complete``.
    ``repair_round`` is the round the main conversation works on (0 = initial
    pass), ``session_id`` the native session every handoff must come from,
    and ``rejection`` the reason the last handoff was refused.

``confirmation.json`` (written by context_runner at each yield)
    ``pending`` -> ``confirming`` (with the dispatch identity) -> ``completed``,
    or ``rejected``. A request bound to another native session fails closed.

Repair rounds reuse the phased machinery unchanged: ``repair-loop.json``
reserves each global round once, ``.repair-phase3-snapshot.json`` records the
OPEN requests handed to the main session, ``.repair-phase3-commit.json`` binds
the accepted repair result to its exact ``findings.json``, and the scoped
dispatcher confirms only those violations. Every step is idempotent, so a
restart repositions each target from these files alone.
"""

from __future__ import annotations

import contextlib
import io
import json
import os
import re
import shutil
import sys
import time
from collections.abc import Iterator
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path
from typing import TYPE_CHECKING, Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from specula import resumelib, stop_gate
from specula.context_control import CONFIRMATION_REQUEST, CONFIRMATION_YIELD_RC, REPAIR_SNAPSHOT, write_json
from specula.notes import notes_section
from specula.phaselib import (
    AgentFiles,
    BugConfirmationPhase,
    Phase,
    SpecValidationPhase,
    Workspace,
    _resume_state_path,
    _trim,
    _wc_l,
)
from specula.prompts import render
from specula.rules import with_rules
from specula.skill_refs import prompt_skill_ids

if TYPE_CHECKING:
    from specula.pipelinelib import Pipeline

PHASE_KEY = "main"
LAUNCHER = "launch_continuous.sh"
STATE_FILE = ".context-control/main-state.json"
ABANDONED_DIR = ".context-control/abandoned"
STAGES = ("main", "confirm", "closed", "classified", "complete")
REQUEST_STATUSES = ("pending", "confirming", "completed", "rejected")
CONFIRMATION_ENV = "SPECULA_CI_CONFIRMATION"  # lets confirmation run while main stays suspended
HISTORY_LIMIT = 100


class ContinuousError(RuntimeError):
    """Persisted continuous state is inconsistent; refuse to guess."""


def _continuation_prompt(text: str, *, work_dir: Path | None = None, notes: bool = False) -> str:
    """Single hook for every continuation or resume prompt this module generates.

    It covers the compaction continue prompt (written by context_runner), the
    post-confirmation repair and rejection prompts, and the fresh-context
    restart prompt. The pinned rules are prepended here; ``with_rules`` is
    idempotent, so prompts that also pass through phaselib's generic launch
    path still carry exactly one rules block. ``notes`` appends the working-
    notes pointer for ``work_dir``. ``_manual_prompt_extra`` fragments are not
    wrapped: phaselib appends them to its own (rules-pinned) manual-resume prompt.
    """
    if notes and work_dir is not None:
        text = text.rstrip("\n") + "\n" + notes_section(work_dir, first=False)
    return with_rules(text)


def _now() -> str:
    return datetime.now().astimezone().isoformat(timespec="seconds")


def _log(message: str) -> None:
    print(f"[{time.strftime('%H:%M:%S')}] {message}")


# ── durable state ──────────────────────────────────────────────────────────


@dataclass
class MainState:
    stage: str = "main"
    repair_round: int = 0
    session_id: str | None = None
    context: str = "original"  # "fresh" after --fresh-context abandoned a session
    rejection: str | None = None
    history: list[dict[str, Any]] = field(default_factory=list)

    def to_object(self, target: str) -> dict[str, Any]:
        return {
            "version": 1,
            "target": target,
            "stage": self.stage,
            "repair_round": self.repair_round,
            "session_id": self.session_id,
            "context": self.context,
            "rejection": self.rejection,
            "history": self.history[-HISTORY_LIMIT:],
        }

    @classmethod
    def from_object(cls, value: object, target: str) -> MainState:
        if not isinstance(value, dict) or value.get("version") != 1 or value.get("target") != target:
            raise ContinuousError(f"invalid continuous state for {target}")
        stage = value.get("stage")
        repair_round = value.get("repair_round")
        session_id = value.get("session_id")
        context = value.get("context")
        rejection = value.get("rejection")
        history = value.get("history")
        if (
            stage not in STAGES
            or not isinstance(repair_round, int)
            or isinstance(repair_round, bool)
            or repair_round < 0
            or (session_id is not None and (not isinstance(session_id, str) or not session_id))
            or context not in ("original", "fresh")
            or (rejection is not None and not isinstance(rejection, str))
            or not isinstance(history, list)
        ):
            raise ContinuousError(f"invalid continuous state for {target}")
        return cls(
            stage=str(stage),
            repair_round=repair_round,
            session_id=session_id,
            context=str(context),
            rejection=rejection,
            history=[entry for entry in history if isinstance(entry, dict)],
        )


def state_path(work: Path) -> Path:
    return work / STATE_FILE


def load_state(work: Path, target: str) -> MainState | None:
    path = state_path(work)
    try:
        raw = json.loads(path.read_text())
    except FileNotFoundError:
        return None
    except (OSError, ValueError) as exc:
        raise ContinuousError(f"cannot read continuous state {path}: {exc}") from exc
    return MainState.from_object(raw, target)


def save_state(work: Path, target: str, state: MainState, event: str) -> None:
    state.history.append({"event": event, "stage": state.stage, "repair_round": state.repair_round, "at": _now()})
    path = state_path(work)
    path.parent.mkdir(parents=True, exist_ok=True)
    write_json(path, state.to_object(target))


def load_request(work: Path) -> dict[str, Any] | None:
    path = work / CONFIRMATION_REQUEST
    try:
        raw = json.loads(path.read_text())
    except FileNotFoundError:
        return None
    except (OSError, ValueError) as exc:
        raise ContinuousError(f"cannot read confirmation request {path}: {exc}") from exc
    if (
        not isinstance(raw, dict)
        or raw.get("status") not in REQUEST_STATUSES
        or not isinstance(raw.get("session_id"), str)
        or not raw["session_id"]
    ):
        raise ContinuousError(f"invalid confirmation request {path}")
    return raw


def save_request(work: Path, request: dict[str, Any]) -> None:
    request["updated_at"] = _now()
    write_json(work / CONFIRMATION_REQUEST, request)


def native_session(work: Path) -> str | None:
    """The native session id the adapter persisted for the main conversation."""
    path = _resume_state_path(work / "main.log")
    try:
        raw = json.loads(path.read_text())
    except FileNotFoundError:
        return None
    except (OSError, ValueError) as exc:
        raise ContinuousError(f"cannot read native session state {path}: {exc}") from exc
    session = raw.get("session_id") if isinstance(raw, dict) else None
    return session if isinstance(session, str) and session else None


def repair_snapshot_requests(work: Path) -> list[str]:
    """Request ids handed to the main session for its current repair round."""
    try:
        raw = json.loads((work / REPAIR_SNAPSHOT).read_text())
    except (OSError, ValueError):
        return []
    requests = raw.get("requests") if isinstance(raw, dict) else None
    return sorted(Path(name).stem for name in requests) if isinstance(requests, dict) else []


def resume_phase(phases: set[str]) -> str:
    """Interrupted phase an attach resumes; the controller positions each target."""
    if PHASE_KEY in phases and phases <= {PHASE_KEY, "bug_confirmation"}:
        return PHASE_KEY
    if phases in ({"bug_confirmation"}, {"bug_classification"}):
        return next(iter(phases))
    raise resumelib.ResumeError("unfinished conversations span multiple phases; pass --fresh-context to start over")


def has_unfinished_work(pipeline: Pipeline) -> bool:
    """Whether an attach without a live conversation still has controller work."""
    for name in pipeline.extract_names():
        try:
            state = load_state(Path(pipeline.get_work_dir(name)), name)
        except ContinuousError as exc:
            raise resumelib.ResumeError(str(exc)) from exc
        if state is not None and state.stage != "complete":
            return True
    return False


# ── prompts ────────────────────────────────────────────────────────────────


def compaction_continue_prompt(status: str, handoff: str, work: Path) -> str:
    return _continuation_prompt(
        f"Continue the same Specula main session. Context compaction {status}. "
        f"First read the saved handoff at {handoff}; then open only evidence needed for the next work. "
        "Keep unresolved counterexamples, invalidated results and pending checks pending. "
        "This was an internal pause, not finalization or a new run. "
        "If compaction failed, continue without repeatedly retrying it. Continue the workflow, and hand off "
        "to confirmation as instructed when validation is complete.\n",
        work_dir=work,
        notes=True,
    )


def _repair_context(name: str, work: Path, repair_round: int, requests: list[str]) -> str:
    spec = work / "spec"
    listed = ", ".join(requests) if requests else "every OPEN request"
    return f"""## Repair Round {repair_round}: Confirmation Results for {name}

Specula finished the confirmation batch you requested, in separate clean contexts. Confirmation judged some counterexamples to be spec, fault-model, or invariant artifacts rather than real bugs, and recorded each as a repair request. Continue this same session; do not restart completed work.

Read `{work}/confirmed-bugs.md` and the OPEN repair requests in `{spec}/repair-requests/` ({listed}). Process ONLY status OPEN. Use each request's cited evidence and cross-check the relevant implementation, tests, documentation, and declared failure model to revise the spec, fault model, or invariant so it faithfully expresses what the system permits and guarantees; do not optimize merely for making the artifact disappear.

Methodology — use these installed skills and follow them exactly:
- {prompt_skill_ids("bug-confirmation")} — apply its repair-request format, request state machine, and per-request repair procedure (how to repair each target, the full-trace soundness gate, and the OPEN → IN_REPAIR → CONSUMED transitions you own).
- {prompt_skill_ids("validation-workflow")} — repair and re-validate without overfitting, including the {prompt_skill_ids("tla-trace-workflow")} and {prompt_skill_ids("tla-checking-workflow")} skills it delegates to.

Run the complete conformance pass (full trace validation and model checking), update the existing evidence and each request's History, write the current violations to `{spec}/findings.json`, and mark each processed request CONSUMED. Do not run confirmation yourself, and do not edit `confirmed-bugs.md`. Then request confirmation again and follow the yield instruction; Specula confirms exactly the violations in `findings.json`.
"""


def _rejection_context(name: str, reason: str) -> str:
    return f"""## Confirmation Request Not Accepted

Specula did not start confirmation for {name} after your last handoff:

{reason}

Fix the reported problem, save the current deliverables, then request confirmation again and follow the yield instruction.
"""


def _existing_work(work: Path) -> list[str]:
    found: list[str] = []
    for relative in (
        "notes/INDEX.md",
        "modeling-brief.md",
        "analysis-report.md",
        "spec/base.tla",
        "spec/MC.tla",
        "spec/Trace.tla",
        "spec/instrumentation-spec.md",
        "harness/run.sh",
        "spec/changelog.md",
        "spec/bug-report.md",
        "spec/findings.json",
        "confirmed-bugs.md",
    ):
        if (work / relative).is_file():
            found.append(f"`{work / relative}`")
    traces = work / "traces"
    if traces.is_dir() and not traces.is_symlink():
        count = len(list(traces.rglob("*.ndjson")))
        if count:
            found.append(f"{count} trace file(s) under `{traces}`")
    return found


def _fresh_context_section(name: str, work: Path) -> str:
    existing = _existing_work(work)
    listed = "\n".join(f"- {item}" for item in existing) if existing else "- (no deliverables yet)"
    return f"""## Continue From Existing Work

An earlier main session for {name} in this run was abandoned so this run can continue with fresh context. Its workspace remains:

{listed}

These are the earlier session's results, not yours. Read `notes/INDEX.md` first if it exists. Check the existing artifacts against the source and the skills instead of trusting them, keep what is valid, and continue from the first stage whose deliverables are missing or invalid. Earlier confirmation reports are not results of this session.
"""


# ── the main-session launcher phase ────────────────────────────────────────


class ContinuousPhase(Phase):
    key = PHASE_KEY
    title = "Specula — Continuous Main Session"
    usage = r"""
Continuous main session: one agent per target performs code analysis, spec
generation, harness generation, and validation in a single native conversation,
then hands its findings to the controller for confirmation. Started by
`specula run`; not a standalone phase.

Usage:
  launch_continuous.sh [options] "name|github|lang|reference" [...]

Options:
  --dry-run           Print commands without executing
  --check             Only verify repos exist
  --max-parallel=N    Max concurrent agents (default: 1)
  --max-turns=N       Max agent turns (default: 0 = unlimited)
  --policy-retries=N  Policy-block continuation retries (default: 20; 0 disables)
  --transient-resumes=N  Transient provider/transport session resumes (default: 20; 0 disables)
  --agent=NAME        Agent adapter to use (default: claude-code)
  --claude-alias=NAME Claude CLI profile (default: claude)
  --model=NAME        Model forwarded to the selected adapter
  --effort=LEVEL      Reasoning effort forwarded to the selected adapter
  --artifact=PATH     Source code path

"""
    check_header = "Checking repositories..."
    check_fail_msg = (
        "ERROR: Some repositories are missing. Use --artifact=<path> or place repos under <name>/artifact/<repo>/."
    )
    check_ok_msg = "All repos OK."
    yield_message = "Main session yielded to the continuous controller."
    # Retry budgets are per controller step (initial pass, each repair round,
    # rejection resume, or attach); retries within one step still accumulate.
    carry_retry_budgets = False

    def target_name(self, target: str) -> str:
        return _trim(target.split("|", 1)[0])

    def check(self, ws: Workspace, names: list[str]) -> bool:
        ok = True
        for name in names:
            if ws.find_repo_dir(name):
                print(f"  OK  {name}")
            else:
                print(f"  MISSING  {name} — use --artifact=<path> or place repo at {name}/artifact/<repo>/")
                ok = False
        return ok

    def agent_files(self, ws: Workspace, name: str) -> AgentFiles:
        wd = ws.work_dir(name)
        return {"log": wd / "main.log", "pid": wd / "main.pid", "prompt": wd / ".main-prompt.md", "mkdirs": [wd]}

    def _main_prompt(self, ws: Workspace, target: str, *, notes_first: bool = True) -> str:
        parts = [_trim(x) for x in target.split("|", 3)]
        parts += [""] * (4 - len(parts))
        name, github, language, reference = parts
        work = ws.work_dir(name)
        prompt = render(
            "continuous",
            name=name,
            github=github,
            language=language,
            reference=reference,
            repo=ws.find_repo_dir(name),
            work_dir=str(work),
            spec_dir=str(work / "spec"),
            analysis_skill=prompt_skill_ids("code-analysis"),
            specgen_skill=prompt_skill_ids("spec-generation"),
            harness_skill=prompt_skill_ids("harness-generation"),
            validation_skill=prompt_skill_ids("validation-workflow"),
            trace_skill=prompt_skill_ids("tla-trace-workflow"),
            checking_skill=prompt_skill_ids("tla-checking-workflow"),
        )
        prompt += notes_section(work, first=notes_first)
        return self._with_extra(ws, name, prompt)

    def _resume_context(self, ws: Workspace, name: str) -> str:
        work = ws.work_dir(name)
        state = load_state(work, name)
        if state is None:
            return ""
        sections: list[str] = []
        if state.rejection:
            sections.append(_rejection_context(name, state.rejection))
        if state.repair_round > 0 and (work / REPAIR_SNAPSHOT).is_file():
            sections.append(_repair_context(name, work, state.repair_round, repair_snapshot_requests(work)))
        return "\n".join(sections)

    def _resumable(self, ws: Workspace, name: str) -> bool:
        if not resumelib.enabled():
            return False
        logical = ("phase", self.key, name)
        active = any(tuple(entry.get("logical", ())) == logical for entry in resumelib.active_entries())
        return active and _resume_state_path(self.agent_files(ws, name)["log"]).is_file()

    def build_prompt(self, ws: Workspace, target: str) -> str:
        name = self.target_name(target)
        work = ws.work_dir(name)
        context = self._resume_context(ws, name)
        if self._resumable(ws, name):
            return _continuation_prompt(
                context
                or (
                    f"Continue the Specula main session for {name} from where it stopped. Keep completed work, "
                    "finish the remaining stages, and hand off to confirmation as instructed."
                ),
                work_dir=work,
            )
        state = load_state(work, name)
        fresh = state is not None and state.context == "fresh"
        # A restarted session continues earlier notes rather than opening the area.
        prompt = self._main_prompt(ws, target, notes_first=not (fresh or context))
        if fresh or context:
            sections = [_fresh_context_section(name, work)] if _existing_work(work) else []
            if context:
                sections.append(context)
            return _continuation_prompt(prompt.rstrip("\n") + "\n\n" + "\n".join(sections), work_dir=work)
        return prompt

    def _manual_prompt_extra(self, ws: Workspace, name: str) -> str:
        extra = super()._manual_prompt_extra(ws, name)
        context = self._resume_context(ws, name)
        return extra + ("\n\n" + context if context else "")

    def finalize_outputs(
        self, ws: Workspace, names: list[str], *, adapter: Path, dry_run: bool
    ) -> list[tuple[str, int]]:
        if dry_run:
            return []
        for name in names:
            print(f"ERROR: {name}: the main session ended without a controller handoff")
        return [(name, 1) for name in names]

    def summarize(self, ws: Workspace, names: list[str]) -> None:
        print()
        print("========================================")
        print(" Results")
        print("========================================")
        for name in names:
            report = ws.work_dir(name) / "spec" / "bug-report.md"
            if report.is_file():
                print(f"  {name}: spec/bug-report.md ({_wc_l(report)} lines)")
            else:
                print(f"  {name}: no spec/bug-report.md (check log)")

    def monitor_line(self, ws: Workspace) -> str | None:
        return self._monitor(ws, "main.log", "  Monitor: tail -f */.specula-output/main.log")


# ── the controller ─────────────────────────────────────────────────────────


@contextlib.contextmanager
def _confirmation_environment() -> Iterator[None]:
    previous = os.environ.get(CONFIRMATION_ENV)
    os.environ[CONFIRMATION_ENV] = "1"
    try:
        yield
    finally:
        if previous is None:
            os.environ.pop(CONFIRMATION_ENV, None)
        else:
            os.environ[CONFIRMATION_ENV] = previous


class ContinuousRun:
    """Drive every target's main session through confirmation and repair."""

    def __init__(self, pipeline: Pipeline) -> None:
        self.p = pipeline
        self.names = pipeline.extract_names()
        self.descriptors = {pipeline._descriptor_name(target): target for target in pipeline.targets}

    def work(self, name: str) -> Path:
        return Path(self.p.get_work_dir(name))

    # ── entry ──
    def main(self) -> int:
        p = self.p
        p.print_run_header()
        print("Orchestration: continuous (one main session per target for analysis through validation;")
        print("               confirmation and classification run in separate clean contexts)")
        print()
        p.validate_agent_adapter()
        names = self.names
        if len(p.targets) == 1 and not names:
            _log(f"ERROR: no target name parsed from '{p.targets[0]}', aborting")
            raise SystemExit(1)
        if p.run_dir is None:
            _log("ERROR: continuous orchestration requires an isolated run directory")
            raise SystemExit(1)
        p.stage_guidance(names)
        p.prepare_source_snapshots(names)
        p.prepare_persistent_findings(names)
        p.initialize_resource_summaries(names)
        start = int(time.time())
        if p.dry_run:
            self._dry_run()
        else:
            try:
                self._drive()
            except (ContinuousError, resumelib.ResumeError) as exc:
                _log(f"ERROR: {exc}")
                return 1
        classified = not p.dry_run and all(self._load(name).stage in ("classified", "complete") for name in names)
        if not p.skip_confirmation and not p.dry_run and not classified:
            p.persist_findings(names)
        if p.skip_classification:
            _log("Skipping Phase 4b (--skip-classification)")
        elif classified:
            _log("Phase 4b already completed for every target; continuing with the summary")
        else:
            with p.resource_phase("phase4b", names):
                p.wait_for_phase_quota("classify")
                p.run_phase4b_classification()
            if not p.dry_run:
                # Durable before the summary: an interruption now must not repeat Phase 4b.
                for name in names:
                    self._advance(name, "classified")
        if not p.dry_run and p.run_dir is not None:
            try:
                active = resumelib.active_entries(p.run_dir)
            except resumelib.ResumeError as exc:
                _log(f"ERROR: cannot verify completed conversation state: {exc}")
                return 1
            if active:
                phases = ", ".join(sorted({str(entry.get("phase")) for entry in active}))
                _log(f"ERROR: pipeline cannot complete with unfinished conversation(s) in {phases}")
                return 1
        p.generate_summary()
        p._complete_resource_summaries(names)
        p.refresh_output_indexes()
        if not p.dry_run:
            for name in names:
                self._advance(name, "complete")
        elapsed = int(time.time()) - start
        print()
        _log(f"Pipeline completed in {elapsed // 60}m {elapsed % 60}s")
        return 0

    def _dry_run(self) -> None:
        p = self.p
        with p.resource_phase("main", self.names):
            p._phase(self._main_banner(0), LAUNCHER, p._phase_args(p.targets, phase="main"))
        if p.skip_confirmation:
            _log("Skipping Phase 4a (--skip-confirmation)")
            return
        with p.resource_phase("phase4a", self.names):
            p.run_phase4_confirmation()
        if p.skip_repair_loop:
            _log("Skipping repair loop (--skip-repair-loop)")
            return
        self._repair_loop_banner()
        _log(
            "[DRY RUN] OPEN repair requests resume the same main session; Specula then confirms its current violations"
        )

    @staticmethod
    def _main_banner(repair_round: int) -> str:
        if repair_round:
            return f"REPAIR ROUND {repair_round}: MAIN SESSION (resumed with confirmation results)"
        return "MAIN SESSION: analysis → spec → harness → validation (one continuous session per target)"

    def _repair_loop_banner(self) -> None:
        cap = int(self.p.max_repair_rounds)
        print()
        print("════════════════════════════════════════════════════════════")
        _log(f"REPAIR LOOP (main-session back-edge) — cap={'unlimited' if cap == 0 else f'{cap} rounds'}")
        print("════════════════════════════════════════════════════════════")

    # ── state helpers ──
    def _load(self, name: str) -> MainState:
        state = load_state(self.work(name), name)
        if state is None:
            raise ContinuousError(f"{name}: missing continuous state")
        return state

    def _save(self, name: str, state: MainState, event: str) -> None:
        save_state(self.work(name), name, state, event)

    def _advance(self, name: str, stage: str) -> None:
        state = self._load(name)
        if STAGES.index(state.stage) < STAGES.index(stage):
            state.stage = stage
            self._save(name, state, stage)

    def _close_conversation(self, name: str) -> None:
        resumelib.complete_turn(("phase", PHASE_KEY, name), allow_previous_owner=True)

    def _start(self) -> None:
        """Create missing state; a fresh-context invocation abandons the old session's records."""
        p = self.p
        if p.fresh_context:
            self._abandon_previous_sessions()
            return
        for name in self.names:
            work = self.work(name)
            if load_state(work, name) is None:
                if load_request(work) is not None:
                    raise ContinuousError(f"{name}: confirmation request exists without controller state")
                self._save(name, MainState(), "start")
        p.reconcile_deferred_state()
        p.regenerate_ledger()

    def _abandon_previous_sessions(self) -> None:
        p = self.p
        stamp = f"{time.time_ns()}"
        for name in self.names:
            work = self.work(name)
            archive = work / ABANDONED_DIR / stamp
            for relative in (STATE_FILE, CONFIRMATION_REQUEST):
                source = work / relative
                if source.is_file():
                    archive.mkdir(parents=True, exist_ok=True)
                    shutil.move(str(source), str(archive / source.name))
        # Recover like the phased pipeline: restore an uncommitted repair
        # snapshot to OPEN and finish any committed result before new work.
        recovered = p.prepare_repair_state()
        if recovered and (p.skip_confirmation or p.skip_repair_loop):
            disabled = "--skip-confirmation" if p.skip_confirmation else "--skip-repair-loop"
            raise ContinuousError(
                f"cannot use {disabled} while a committed repair result is pending; "
                "resume once without that flag so its exact findings can be reconciled"
            )
        if recovered:
            _log("Finishing the committed repair result of the abandoned session before the fresh main session")
            with p.resource_phase("phase4a", self.names), _confirmation_environment():
                p.process_pending_repair_results(recovered)
            p.regenerate_ledger()
        for name in self.names:
            self._save(name, MainState(context="fresh"), "fresh-context")
        if not p.skip_confirmation and not p.skip_repair_loop:
            needing = [name for name in self.names if self._open_requests(name)]
            if needing:
                self._reserve_repair_round(needing)

    def _position(self, name: str) -> MainState:
        """Reconcile one target's stage with its durable evidence (idempotent)."""
        work = self.work(name)
        state = self._load(name)
        if state.stage in ("closed", "classified", "complete"):
            self._close_conversation(name)
            return state
        request = load_request(work)
        if request is None:
            if state.stage == "confirm":
                raise ContinuousError(f"{name}: controller state expects a confirmation request that is missing")
            return state
        session = request["session_id"]
        native = native_session(work)
        if native is not None and native != session:
            raise ContinuousError(
                f"{name}: confirmation request belongs to native session {session}, but the main conversation "
                f"is {native}; pass --fresh-context to start over"
            )
        if state.session_id is not None and state.session_id != session:
            raise ContinuousError(
                f"{name}: confirmation request belongs to another main conversation; pass --fresh-context to start over"
            )
        status = request["status"]
        if status in ("pending", "confirming") and (state.stage != "confirm" or state.session_id != session):
            state.stage = "confirm"
            state.session_id = session
            state.rejection = None
            self._save(name, state, "yield")
        elif status == "rejected" and state.stage != "main":
            state.stage = "main"
            state.rejection = str(request.get("reason") or "the handoff was invalid")
            self._save(name, state, "rejected")
        return state

    def _open_requests(self, name: str) -> list[Path]:
        from specula.pipelinelib import rr_status

        return [path for path in self.p._rr_files(name) if rr_status(path) == "OPEN"]

    # ── the loop ──
    def _drive(self) -> None:
        self._start()
        while True:
            states = {name: self._position(name) for name in self.names}
            stalled = self._unfinished_reservations(states)
            if stalled:
                # A crash interrupted a round reservation: finish it before any
                # main session starts, so the round is not handed out again.
                self._reserve_repair_round(stalled)
                continue
            main_names = [name for name in self.names if states[name].stage == "main"]
            if main_names:
                self._run_main(main_names, states)
                continue
            confirm_names = [name for name in self.names if states[name].stage == "confirm"]
            if not confirm_names:
                return
            self._confirm(confirm_names, states)

    def _run_main(self, names: list[str], states: dict[str, MainState]) -> None:
        p = self.p
        repair_round = max(states[name].repair_round for name in names)
        banner = self._main_banner(repair_round)
        if all(states[name].rejection for name in names):
            banner = "MAIN SESSION (resumed after an unaccepted confirmation request)"
        p.wait_for_phase_quota("main")
        try:
            with p.resource_phase("main", names):
                p._phase(banner, LAUNCHER, p._phase_args([self.descriptors[name] for name in names], phase="main"))
        except SystemExit as exc:
            if exc.code != CONFIRMATION_YIELD_RC:
                raise
        else:
            raise ContinuousError("main session launcher returned without a controller handoff")
        for name in names:
            request = load_request(self.work(name))
            if request is None or request["status"] != "pending":
                raise ContinuousError(f"{name}: main session yielded without a pending confirmation request")

    def _confirm(self, names: list[str], states: dict[str, MainState]) -> None:
        requests = {name: load_request(self.work(name)) for name in names}
        dispatch = [name for name in names if (requests[name] or {}).get("status") in ("pending", "confirming")]
        if dispatch:
            self._dispatch(dispatch, states)
        self._decide(names, states)

    # ── confirmation dispatch ──
    def _handoff_error(self, name: str, state: MainState) -> str | None:
        """Repeat the phased end-of-phase artifact checks at the handoff."""
        p = self.p
        work = self.work(name)
        opts: dict[str, str | bool] = {"repair_round": str(state.repair_round)} if state.repair_round else {}
        ws = Workspace(p.targets, artifact=p.artifact, run_dir=p.run_dir, opts=opts)
        buffer = io.StringIO()
        with contextlib.redirect_stdout(buffer):
            accepted = SpecValidationPhase().check(ws, [name]) & BugConfirmationPhase().check(ws, [name])
            gate = stop_gate._accept_main(PHASE_KEY, str(work))
        report = buffer.getvalue()
        print()
        print("Checking handoff to bug_confirmation...")
        sys.stdout.write(report)
        if gate != 0:
            print("Acceptance gate:")
            print(f"  FAILED  {name}: see the message above")
        if not accepted:
            return "Confirmation prerequisites are missing:\n" + report.rstrip()
        if gate != 0:
            # Confirmation must never run beside a stray job of the main session
            # (e.g. after the stop-gate fuse opened or on an adapter without hooks).
            return (
                "The completion audit failed. Wait for every background job you started, harvest its results, "
                "and update the deliverables before requesting confirmation again:\n" + report.rstrip()
            )
        return None

    def _reject(self, name: str, reason: str) -> None:
        work = self.work(name)
        request = load_request(work)
        assert request is not None
        request.update({"status": "rejected", "reason": reason})
        save_request(work, request)
        state = self._load(name)
        state.stage = "main"
        state.rejection = reason
        self._save(name, state, "rejected")
        _log(f"ERROR: {name}: confirmation request not accepted: {reason.splitlines()[0]}")

    def _accept_repair(self, name: str, state: MainState) -> str | None:
        """Commit a repair-round handoff with the phased snapshot/commit proofs."""
        from specula.pipelinelib import rr_status

        p = self.p
        repair_round = state.repair_round
        loaded = p.load_open_repair_snapshot(name)
        commit = p.load_repair_phase3_commit(name)
        if commit is None:
            if loaded is None:
                raise ContinuousError(f"{name}: repair round {repair_round} has no durable repair snapshot")
            snapshot, snapshot_round, _token = loaded
            if snapshot_round != repair_round:
                raise ContinuousError(
                    f"{name}: repair snapshot is for round {snapshot_round}, not round {repair_round}"
                )
            unfinished = [path for path in snapshot if rr_status(path) != "CONSUMED"]
            if unfinished:
                detail = ", ".join(f"{path.stem}={rr_status(path) or '<missing>'}" for path in unfinished)
                return f"Repair requests handed to this session were not consumed: {detail}."
            try:
                p.publish_repair_phase3_commit(repair_round, [name])
            except RuntimeError as exc:
                return str(exc)
            commit = p.load_repair_phase3_commit(name)
            assert commit is not None
        elif int(commit["repair_round"]) != repair_round:
            raise ContinuousError(f"{name}: committed repair result is for another round")
        if loaded is not None:
            p.clear_repair_phase3_snapshot(name)
        round_, pending = p.load_repair_loop_state()
        if name in pending:
            pending.remove(name)
            p.save_repair_loop_state(round_, pending)
        work = self.work(name)
        request = load_request(work)
        assert request is not None
        request.update(
            {
                "status": "confirming",
                "kind": "scoped",
                "repair_round": repair_round,
                "commit_token": commit["commit_token"],
                "violation_ids": list(commit["violation_ids"]),
            }
        )
        save_request(work, request)
        return None

    def _dispatch(self, names: list[str], states: dict[str, MainState]) -> None:
        p = self.p
        full: list[str] = []
        scoped: list[str] = []
        rejected = False
        for name in names:
            request = load_request(self.work(name))
            assert request is not None
            if request["status"] == "confirming":
                (scoped if request.get("kind") == "scoped" else full).append(name)
                continue
            reason = self._handoff_error(name, states[name])
            if reason is None and states[name].repair_round:
                reason = self._accept_repair(name, states[name])
                if reason is None:
                    scoped.append(name)
            elif reason is None:
                full.append(name)
            if reason is not None:
                self._reject(name, reason)
                rejected = True
        if rejected:
            _log(
                "ERROR: the main session will resume with the reported problem; "
                "rerun with --run-id to continue (accepted handoffs stay queued)"
            )
            raise SystemExit(1)
        if p.skip_confirmation:
            for name in full + scoped:
                self._complete_request(name, skipped=True)
            _log("Skipping Phase 4a (--skip-confirmation)")
            return
        if full:
            self._dispatch_full(full)
        for name in scoped:
            self._dispatch_scoped(name)
        if scoped:
            for repair_round in sorted({states[name].repair_round for name in scoped}):
                p.snapshot_confirmed_bugs(repair_round)
        p.regenerate_ledger()

    def _dispatch_full(self, names: list[str]) -> None:
        p = self.p
        fresh = [name for name in names if (load_request(self.work(name)) or {}).get("status") == "pending"]
        if fresh:
            # As after a phased Phase 3: never reuse an earlier generation's cache.
            p.advance_confirmation_generation(0, fresh)
            for name in fresh:
                request = load_request(self.work(name))
                assert request is not None
                request.update({"status": "confirming", "kind": "full", "repair_round": 0})
                save_request(self.work(name), request)
        p.prepare_persistent_findings(names)
        with p.resource_phase("phase4a", names), _confirmation_environment():
            p.wait_for_phase_quota("confirm")
            p.run_phase4_confirmation_for(names)
        for name in names:
            self._complete_request(name)

    def _dispatch_scoped(self, name: str) -> None:
        p = self.p
        work = self.work(name)
        request = load_request(work)
        assert request is not None
        token = request.get("commit_token")
        if not isinstance(token, str) or re.fullmatch(r"[0-9a-f]{32}", token) is None:
            raise ContinuousError(f"{name}: scoped confirmation request has no valid commit token")
        commit = p.load_repair_phase3_commit(name)
        if commit is not None:
            if commit["commit_token"] != token:
                raise ContinuousError(f"{name}: committed repair result does not match its confirmation request")
            with p.resource_phase("phase4a", [name]), _confirmation_environment():
                p.process_pending_repair_results({name})
        # A missing commit proof with a matching dispatch record means the
        # scoped pass already succeeded before an interruption.
        self._complete_request(name)

    def _complete_request(self, name: str, *, skipped: bool = False) -> None:
        work = self.work(name)
        request = load_request(work)
        assert request is not None
        if request["status"] == "completed":
            return
        request["status"] = "completed"
        request.setdefault("repair_round", 0)
        if skipped:
            request["skipped"] = True
        save_request(work, request)

    # ── decisions after a completed batch ──
    def _decide(self, names: list[str], states: dict[str, MainState]) -> None:
        p = self.p
        needing: list[str] = []
        for name in names:
            request = load_request(self.work(name))
            if request is None or request["status"] != "completed":
                raise ContinuousError(f"{name}: confirmation did not complete")
            if p.skip_confirmation or p.skip_repair_loop or not self._open_requests(name):
                continue
            needing.append(name)
        if p.skip_repair_loop and not p.skip_confirmation and any(self._open_requests(name) for name in names):
            _log("Skipping repair loop (--skip-repair-loop)")
        reserved = self._reserve_repair_round(needing) if needing else []
        for name in names:
            # Targets the reserved round did not take wait, still in "confirm", for the next round.
            if reserved is None or name not in needing:
                state = self._load(name)
                state.stage = "closed"
                state.rejection = None
                self._save(name, state, "closed")
                self._close_conversation(name)

    def _unfinished_reservations(self, states: dict[str, MainState]) -> list[str]:
        """Targets reserved for the current round whose hand-over to the main session was interrupted."""
        p = self.p
        if p.skip_confirmation or p.skip_repair_loop:
            return []
        _round, pending = p.load_repair_loop_state()
        return [
            name
            for name in self.names
            if name in pending
            and states[name].stage == "confirm"
            and (load_request(self.work(name)) or {}).get("status") == "completed"
            and self._open_requests(name)
        ]

    def _reserve_repair_round(self, needing: list[str]) -> list[str] | None:
        """Reserve one global round (once) and hand the OPEN requests to the main sessions.

        Returns the targets handed a round, or None when the round cap deferred
        every OPEN request. A target joins each round at most once: while the
        current round still has reserved targets, only those are handed over
        and the other targets wait for the next round.
        """
        p = self.p
        cap = int(p.max_repair_rounds)
        round_, pending = p.load_repair_loop_state()
        current = sorted(set(pending) & set(needing))
        if current:
            needing = current
        else:
            self._repair_loop_banner()
            if cap != 0 and round_ >= cap:
                deferred = p.move_open_requests_to_deferred()
                p.regenerate_ledger()
                _log(f"Repair loop reached its {cap}-round cap; deferred {deferred} still-OPEN request(s).")
                return None
            round_ += 1
            p.save_repair_loop_state(round_, sorted(set(pending) | set(needing)))
        for name in needing:
            existing = p.load_open_repair_snapshot(name)
            if existing is None:
                p.persist_open_repair_snapshot(name, p.snapshot_open_repair_requests(name), round_)
            elif existing[1] != round_:
                raise ContinuousError(f"{name}: an unfinished repair snapshot belongs to round {existing[1]}")
            state = self._load(name)
            state.stage = "main"
            state.repair_round = round_
            state.rejection = None
            self._save(name, state, f"repair-round-{round_}")
            _log(f"{name}: resuming the main session for repair round {round_}")
        p.regenerate_ledger()
        return needing
