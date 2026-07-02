#!/usr/bin/env python3
"""Specula pipeline orchestrator — Python port of scripts/launch/launch_pipeline.sh.

Runs the full phase sequence (analysis → specgen → harness → validation →
confirmation [+ repair loop] → classification → summary) by invoking the
per-phase launchers as subprocesses, exactly like the bash did — the dry-run
command lines, the `main 2>&1 | tee pipeline.log` plumbing, the repair-request
state machine and the quota gate are all faithful ports, pinned by the
pipeline_*/repair_*/quota_* cases in tests/characterization/.

Usage:  python3 pipelinelib.py [options] "name|github|lang|reference" [...]

Lives in scripts/launch/ for now (no packaging dependency); moves into the
`specula/` package once that exists (migration step 2).
"""

from __future__ import annotations

import json
import locale
import os
import re
import subprocess
import sys
import time
from datetime import datetime
from pathlib import Path

# phaselib's import also adopts the ambient LC_COLLATE, so RR-file glob order
# matches bash pathname expansion (ledger rows, state signatures).
from phaselib import _wc_l

SCRIPT_DIR = Path(__file__).resolve().parent
SPECULA_ROOT = SCRIPT_DIR.parent.parent
USAGE_SCRIPT = SPECULA_ROOT / "scripts" / "exp" / "usage.sh"

USAGE = """
Full Specula pipeline: Code Analysis → Spec Generation → Harness Generation → Validation + Bug Hunting

Runs all phases with optional review agents between each phase.
All agent logs and review results are saved for inspection.

Usage:
  bash scripts/launch/launch_pipeline.sh [options] "name|github|lang|reference" [...]

Example (single system):
  bash scripts/launch/launch_pipeline.sh "cometbft|cometbft/cometbft|Go|Tendermint BFT"

Example (multiple systems):
  bash scripts/launch/launch_pipeline.sh \\
    "braft|brpc/braft|C++|Raft (Ongaro 2014)" \\
    "sofa-jraft|sofastack/sofa-jraft|Java|Raft (Ongaro 2014)"

Options:
  --dry-run              Print commands without executing
  --skip-analysis        Skip code analysis (use existing outputs)
  --skip-specgen         Skip spec generation (use existing outputs)
  --skip-harness         Skip harness generation (use existing harness/traces)
  --skip-validation      Skip validation
  --skip-confirmation    Skip Phase 4a bug confirmation
  --skip-classification  Skip Phase 4b severity classification
  --skip-repair-loop     Skip the confirmation back-edge repair loop (default: enabled)
  --max-repair-rounds=N  Per-request repair cap, enforced by re-check (default: 0 = unlimited)
  --enable-reviews        Enable review steps (disabled by default)
  --max-parallel=N       Max concurrent agents per phase (default: 1)
  --max-turns=N          Max agent turns (default: 0 = unlimited)
  --agent=NAME           Agent adapter to use (default: claude-code; e.g., claude-code, codex, copilot-cli)
  --claude-alias=NAME    Claude CLI profile (default: claude)
  --artifact=PATH        Path to system artifact/source code

Output structure (per system):
  .specula-output/
    ├── analysis-report.md          # Phase 1 output
    ├── modeling-brief.md           # Phase 1 output
    ├── agent.log                   # Phase 1 agent log
    ├── review-analysis.md          # Phase 1 review
    ├── review-analysis.log         # Phase 1 review agent log
    ├── spec/
    │   ├── base.tla                # Phase 2 output
    │   ├── MC.tla                  # Phase 2 output
    │   ├── Trace.tla               # Phase 2 output
    │   ├── instrumentation-spec.md # Phase 2 output
    │   ├── MC_hunt_*.cfg          # Phase 2 output (bug hunting configs)
    │   ├── changelog.md           # Phase 3 output
    │   ├── output/                # Phase 3 output (TLC results)
    │   └── bug-report.md          # Phase 3 output (bug hunting results)
    ├── harness/                     # Phase 2.5 output
    │   ├── src/                   # Trace module + test scenarios
    │   ├── apply.sh               # Apply instrumentation
    │   ├── run.sh                 # Build + run + collect traces
    │   └── INSTRUMENTATION.md     # Guide for adjusting instrumentation
    ├── traces/                      # Phase 2.5 output (NDJSON traces)
    ├── spec-gen.log                # Phase 2 agent log
    ├── harness-gen.log             # Phase 2.5 agent log
    └── pipeline.log                # This script's log

"""

DIVIDER = "════════════════════════════════════════════════════════════"


def log(msg: str) -> None:
    """Mirror bash `log() { echo "[$(date '+%H:%M:%S')] $*"; }`."""
    print(f"[{time.strftime('%H:%M:%S')}] {msg}")


def divider() -> None:
    print()
    print(DIVIDER)


def _date_iseconds() -> str:
    """Mirror `date -Iseconds` (local time, seconds precision, tz offset)."""
    return datetime.now().astimezone().isoformat(timespec="seconds")


def _b(flag: bool) -> str:
    """bash booleans print as the literal command names `true` / `false`."""
    return "true" if flag else "false"


# ──────────────────────────────────────────────────────────
# Repair-request primitives (confirmation back-edge)
#
# Repair requests live at <work_dir>/spec/repair-requests/RR-*.md. Their
# frontmatter `status:` is the single source of truth. See
# .claude/skills/bug-confirmation/references/repair-request-format.md.
# ──────────────────────────────────────────────────────────
def rr_field(path: str | Path, field: str) -> str:
    """First frontmatter `<field>:` value within the top 25 lines, trailing
    whitespace stripped — bash `sed -n "1,25{s/^field:[[:space:]]*//p}" | head -1`."""
    prefix = field + ":"
    try:
        lines = Path(path).read_text(errors="replace").splitlines()
    except OSError:
        return ""
    for ln in lines[:25]:
        if ln.startswith(prefix):
            return ln[len(prefix) :].strip()
    return ""


def rr_status(path: str | Path) -> str:
    """Status with ALL whitespace removed — bash `... | tr -d '[:space:]'`."""
    return re.sub(r"[ \t\n\r\f\v]", "", rr_field(path, "status"))


def rr_set_status(path: str | Path, new_status: str, note: str) -> None:
    """Set status + append a History bullet (read-modify-write one file). Same
    semantics as the bash-embedded python: only the first `status:` line within
    the top 25 is rewritten; the bullet is appended even if none was found; a
    missing trailing newline is repaired first."""
    p = Path(path)
    with open(p) as fh:
        lines = fh.readlines()
    for i, ln in enumerate(lines[:25]):
        if ln.startswith("status:"):
            lines[i] = f"status: {new_status}\n"
            break
    if lines and not lines[-1].endswith("\n"):
        lines[-1] += "\n"
    lines.append(f"- {note}\n")
    with open(p, "w") as fh:
        fh.writelines(lines)


# ──────────────────────────────────────────────────────────
# Quota gate
# ──────────────────────────────────────────────────────────
def _quota_check(usage_json: str, q5: str, q7: str) -> str | None:
    """The decision the bash embedded in a `python3 -c` heredoc: 'ok', an
    over-limit message, or None for any parse failure (the bash caught those as
    a non-zero exit → 'usage parse failed'). q5/q7 stay raw strings for display
    parity; numeric conversion happens inside the try so a garbage threshold is
    a parse failure (proceed), exactly like the bash interpolation was."""
    try:
        d = json.loads(usage_json)
        five = d.get("five_hour") or {}
        seven = d.get("seven_day") or {}
        u5 = five.get("utilization", 0) or 0
        u7 = seven.get("utilization", 0) or 0
        if u5 > float(q5):
            return f"5h={u5}% (limit {q5}%) resets_at={five.get('resets_at', '')}"
        if u7 > float(q7):
            return f"7d={u7}% (limit {q7}%) resets_at={seven.get('resets_at', '')}"
        return "ok"
    except Exception:
        return None


def _epoch(ts: str) -> int:
    """`date -d "$ts" +%s`; on unparseable input the bash arithmetic saw an empty
    substitution → a hugely negative wait → the 60s floor. 0 reproduces that."""
    try:
        return int(datetime.fromisoformat(ts.replace("Z", "+00:00")).timestamp())
    except ValueError:
        return 0


def wait_for_quota(
    usage_script: str | Path,
    q5: str,
    q7: str,
    max_waits: str,
    claude_alias: str,
    sleep_fn=time.sleep,
) -> int:
    """Block until usage is under both thresholds. 5h is checked before 7d,
    strictly `>`; fetch/parse failures WARN and proceed; over-limit waits until
    resets_at (+120s, 60s floor; 600s when absent), bounded by max_waits then
    the whole run aborts (exit 1) — budget pressure is WAIT, never auto-defer."""
    if not Path(usage_script).is_file():
        return 0
    waits = 0
    while True:
        env = dict(os.environ)
        env["CLAUDE_ALIAS"] = claude_alias
        try:
            r = subprocess.run(["bash", str(usage_script)], env=env, capture_output=True, text=True)
        except OSError:
            log("WARN: usage fetch failed, proceeding")
            return 0
        if r.returncode != 0:
            log("WARN: usage fetch failed, proceeding")
            return 0
        check = _quota_check(r.stdout, q5, q7)
        if check is None:
            log("WARN: usage parse failed, proceeding")
            return 0
        if check == "ok":
            return 0
        waits += 1
        if waits > int(max_waits):
            log(f"ERROR: quota still over limit after {max_waits} waits, aborting")
            raise SystemExit(1)
        m = re.search(r"resets_at=(\S+)", check)
        reset_at = m.group(1) if m else ""
        if reset_at:
            sleep_secs = _epoch(reset_at) - int(time.time()) + 120
            if sleep_secs < 60:
                sleep_secs = 60
        else:
            sleep_secs = 600
        log(f"Quota: {check} — sleeping {sleep_secs}s (wait {waits}/{max_waits})")
        sleep_fn(sleep_secs)


class Pipeline:
    """Parsed configuration + the phase sequencing of the bash `main`."""

    def __init__(self) -> None:
        self.max_parallel = "1"  # verbatim passthrough; the launchers validate
        self.max_turns = "0"  # deprecated verbatim passthrough
        self.dry_run = False
        self.skip_analysis = False
        self.skip_specgen = False
        self.skip_harness = False
        self.skip_validation = False
        self.skip_confirmation = False
        self.skip_classification = False
        self.skip_repair_loop = False
        # `or`: bash ${VAR:-default} treats an exported-but-empty var as unset
        self.max_repair_rounds = os.environ.get("MAX_REPAIR_ROUNDS") or "0"
        self.skip_reviews = True
        self.agent = "claude-code"
        self.claude_alias = os.environ.get("CLAUDE_ALIAS") or "claude"
        self.artifact = ""
        self.targets: list[str] = []
        self.quota_5h = os.environ.get("QUOTA_5H") or "85"
        self.quota_7d = os.environ.get("QUOTA_7D") or "95"
        self.quota_max_waits = os.environ.get("QUOTA_MAX_WAITS") or "6"

    # ── argument parsing (runs before the tee starts, like the bash top level) ──
    def parse_args(self, argv: list[str]) -> int | None:
        """Returns an exit code for the pre-tee exits (--help / unknown option),
        None to proceed."""
        for arg in argv:
            if arg == "--dry-run":
                self.dry_run = True
            elif arg == "--skip-analysis":
                self.skip_analysis = True
            elif arg == "--skip-specgen":
                self.skip_specgen = True
            elif arg == "--skip-harness":
                self.skip_harness = True
            elif arg == "--skip-validation":
                self.skip_validation = True
            elif arg == "--skip-confirmation":
                self.skip_confirmation = True
            elif arg == "--skip-classification":
                self.skip_classification = True
            elif arg == "--skip-repair-loop":
                self.skip_repair_loop = True
            elif arg.startswith("--max-repair-rounds="):
                self.max_repair_rounds = arg.split("=", 1)[1]
            elif arg == "--enable-reviews":
                self.skip_reviews = False
            elif arg.startswith("--max-parallel="):
                self.max_parallel = arg.split("=", 1)[1]
            elif arg.startswith("--max-turns="):
                self.max_turns = arg.split("=", 1)[1]
            elif arg.startswith("--agent="):
                self.agent = arg.split("=", 1)[1]
            elif arg.startswith("--claude-alias="):
                self.claude_alias = arg.split("=", 1)[1]
            elif arg.startswith("--artifact="):
                self.artifact = arg.split("=", 1)[1]
            elif arg in ("--help", "-h"):
                sys.stdout.write(USAGE)
                return 0
            elif arg.startswith("-"):
                print(f"Unknown option: {arg}")
                return 1
            else:
                self.targets.append(arg)
        if not self.targets:
            self.targets.append(Path.cwd().name)
        return None

    # ── utilities ──
    def extract_names(self) -> list[str]:
        """First '|' field of each target, trimmed. The bash flattened the list
        through `echo ${names[@]}` + `read -ra`, so a name with internal
        whitespace splits into several — reproduced by extend(split()). Names
        with quote characters were undefined behavior under `xargs` and stay
        out of contract."""
        names: list[str] = []
        for target in self.targets:
            names.extend(target.split("|", 1)[0].split())
        return names

    def validate_agent_adapter(self) -> None:
        adapter = SCRIPT_DIR / "adapters" / f"{self.agent}.sh"
        if not adapter.is_file():
            print(
                f"ERROR: Unknown agent '{self.agent}' — adapter not found at {adapter}",
                file=sys.stderr,
            )
            raise SystemExit(1)

    def get_work_dir(self, name: str) -> str:
        """$PWD is evaluated at call time — after the single-target cd."""
        if len(self.targets) == 1:
            return f"{os.getcwd()}/.specula-output"
        return f"{os.getcwd()}/{name}/.specula-output"

    def wait_for_quota(self) -> None:
        wait_for_quota(
            usage_script=USAGE_SCRIPT,
            q5=self.quota_5h,
            q7=self.quota_7d,
            max_waits=self.quota_max_waits,
            claude_alias=self.claude_alias,
        )

    # ── repair-loop helpers ──
    def repair_dir(self, name: str) -> str:
        return f"{self.get_work_dir(name)}/spec/repair-requests"

    def _rr_files(self, name: str) -> list[Path]:
        d = Path(self.repair_dir(name))
        if not d.is_dir():
            return []
        # bash `for f in "$d"/RR-*.md` — pathname expansion orders by LC_COLLATE
        return sorted(d.glob("RR-*.md"), key=lambda p: locale.strxfrm(p.name))

    def has_any_request(self) -> bool:
        return any(self._rr_files(n) for n in self.extract_names())

    def repair_work_remaining(self) -> bool:
        """True if any RR is not yet terminal (anything other than RESOLVED /
        DEFERRED). Repair handles OPEN/REOPENED, re-check handles RECHECK;
        reset_stale_in_repair recovers IN_REPAIR. The loop runs until none
        remain."""
        for n in self.extract_names():
            for f in self._rr_files(n):
                if rr_status(f) not in ("RESOLVED", "DEFERRED"):
                    return True
        return False

    def repair_state_sig(self) -> str:
        """Stable signature of every request's (id, status, round). A round that
        leaves this unchanged made no progress — stop, rather than spin (covers
        --dry-run and a misbehaving agent that never transitions a request)."""
        lines = []
        for n in self.extract_names():
            for f in self._rr_files(n):
                lines.append(f"{f.name}:{rr_status(f)}:{rr_field(f, 'round')}")
        return "\n".join(lines)

    def reset_stale_in_repair(self) -> None:
        """Crash recovery: a request stuck IN_REPAIR means its repair phase died
        mid-turn. Reset to OPEN so the next round retries it."""
        if self.dry_run:
            return
        for n in self.extract_names():
            for f in self._rr_files(n):
                if rr_status(f) == "IN_REPAIR":
                    rr_set_status(f, "OPEN", "reset (orchestrator): repair phase did not complete; retrying")
                    log(f"  reset {f.name} IN_REPAIR -> OPEN (crash recovery)")

    def regenerate_ledger(self) -> None:
        """Regenerate the human-readable rollup index per target."""
        if self.dry_run:
            return
        for n in self.extract_names():
            files = self._rr_files(n)
            if not files:
                continue
            ledger = Path(self.get_work_dir(n)) / "spec" / "repair-ledger.md"
            rows = [
                f"# Repair Ledger — {n}",
                "",
                f"Updated: {_date_iseconds()}",
                "",
                "| Request | Bug | Target | Status | Round |",
                "|---------|-----|--------|--------|-------|",
            ]
            for f in files:
                bug = rr_field(f, "bug_id").replace("|", "\\|")
                rows.append(
                    f"| {rr_field(f, 'id')} | {bug} | {rr_field(f, 'target')} | {rr_status(f)} | {rr_field(f, 'round')} |"
                )
            ledger.write_text("\n".join(rows) + "\n")

    # ── phase runners ──
    def _phase_args(self, positional: list[str], pre: list[str] | None = None, with_artifact: bool = True) -> list[str]:
        args = list(pre or [])
        args += [
            f"--max-parallel={self.max_parallel}",
            f"--max-turns={self.max_turns}",
            f"--agent={self.agent}",
            f"--claude-alias={self.claude_alias}",
        ]
        if with_artifact and self.artifact:
            args.append(f"--artifact={self.artifact}")
        args += positional
        return args

    def _run_launcher(self, script: str, args: list[str]) -> None:
        r = subprocess.run(["bash", str(SCRIPT_DIR / script), *args])
        if r.returncode != 0:
            raise SystemExit(r.returncode)  # bash set -e: a failing phase aborts the run

    def _phase(self, banner: str, script: str, args: list[str]) -> None:
        divider()
        log(banner)
        divider()
        if self.dry_run:
            log(f"[DRY RUN] bash scripts/launch/{script} {' '.join(args)}")
            return
        self._run_launcher(script, args)

    def run_phase1_analysis(self) -> None:
        self._phase("PHASE 1: CODE ANALYSIS", "launch_code_analysis.sh", self._phase_args(self.targets))

    def run_review(self, phase: str, names: list[str]) -> None:
        if self.skip_reviews:
            log(f"Skipping {phase} review (--skip-reviews)")
            return
        divider()
        log(f"REVIEW: {phase}")
        divider()
        args = [f"--agent={self.agent}", f"--claude-alias={self.claude_alias}", phase, *names]
        if self.dry_run:
            log(f"[DRY RUN] bash scripts/launch/launch_review.sh {' '.join(args)}")
            return
        self._run_launcher("launch_review.sh", args)

    def run_phase2_specgen(self) -> None:
        self._phase("PHASE 2: SPEC GENERATION", "launch_spec_generation.sh", self._phase_args(self.extract_names()))

    def run_phase2_5_harness(self) -> None:
        self._phase(
            "PHASE 2.5: HARNESS GENERATION (instrumentation + trace collection)",
            "launch_harness_generation.sh",
            self._phase_args(self.extract_names()),
        )

    def run_phase3_validation(self) -> None:
        self._phase(
            "PHASE 3: SPEC VALIDATION (trace validation + invariant checking + bug hunting)",
            "launch_spec_validation.sh",
            self._phase_args(self.extract_names()),
        )

    def run_phase4_confirmation(self) -> None:
        self._phase(
            "PHASE 4: BUG CONFIRMATION (consolidate + reproduce)",
            "launch_bug_confirmation.sh",
            self._phase_args(self.extract_names()),
        )

    def run_phase3_repair(self, round_: int) -> None:
        """Phase 3 in repair mode: consume OPEN/REOPENED requests, repair the
        spec, re-validate, transition each request to RECHECK."""
        self._phase(
            f"REPAIR ROUND {round_}: PHASE 3 (scoped spec/fault/invariant repair)",
            "launch_spec_validation.sh",
            self._phase_args(self.extract_names(), pre=["--repair"]),
        )

    def run_phase4_recheck(self, round_: int) -> None:
        """Phase 4 in re-check mode: consume RECHECK requests, settle each
        finding, transition to RESOLVED / REOPENED / DEFERRED (never RECHECK).
        --max-repair-rounds is a PER-REQUEST cap the re-check agent enforces;
        the agent, not the orchestrator, writes every RESOLVED / DEFERRED back
        to confirmed-bugs.md."""
        self._phase(
            f"REPAIR ROUND {round_}: PHASE 4 (re-check repair requests)",
            "launch_bug_confirmation.sh",
            self._phase_args(self.extract_names(), pre=["--recheck", f"--max-repair-rounds={self.max_repair_rounds}"]),
        )

    def run_phase4b_classification(self) -> None:
        self._phase(
            "PHASE 4b: BUG CLASSIFICATION (severity tier assignment)",
            "launch_bug_classification.sh",
            self._phase_args(self.extract_names(), with_artifact=False),
        )

    def run_repair_loop(self) -> None:
        """Confirmation back-edge: alternate Phase 3 repair and Phase 4 re-check
        until every request is terminal (RESOLVED / DEFERRED). Budget pressure is
        handled by wait_for_quota (WAIT, like every other phase) — the loop never
        mass-defers on quota, since dumping findings to DEFERRED under throttling
        would be an exploitable weakness. DEFERRED is only ever written by the
        re-check agent, per finding, with evidence. The orchestrator never edits
        confirmed-bugs.md."""
        divider()
        cap_disp = "unlimited" if self.max_repair_rounds == "0" else f"{self.max_repair_rounds} per request"
        log(f"REPAIR LOOP (confirmation back-edge) — cap={cap_disp}")
        divider()

        self.reset_stale_in_repair()  # recover crashed IN_REPAIR from a prior run
        if not self.has_any_request():
            log("No repair requests emitted by bug confirmation — repair loop is a no-op.")
            return

        round_ = 0
        while self.repair_work_remaining():
            round_ += 1
            sig_before = self.repair_state_sig()
            self.wait_for_quota()  # budget pressure -> WAIT, never auto-defer
            self.run_phase3_repair(round_)
            self.reset_stale_in_repair()  # recover if this round's repair phase died mid-turn
            self.wait_for_quota()
            self.run_phase4_recheck(round_)
            self.regenerate_ledger()
            if self.repair_state_sig() == sig_before:
                log(f"Repair loop made no progress in round {round_} (no request changed) — stopping to avoid spin.")
                break

        self.regenerate_ledger()
        log(f"Repair loop ended after {round_} round(s).")

    # ── final summary ──
    def generate_summary(self) -> None:
        names = self.extract_names()
        divider()
        log("PIPELINE SUMMARY")
        divider()

        pwd = os.getcwd()
        summary_file = Path(pwd) / ".specula-output" / "pipeline-summary.md"
        summary_file.parent.mkdir(parents=True, exist_ok=True)
        out: list[str] = []
        out += ["# Specula Pipeline Summary", "", f"Generated: {_date_iseconds()}", "", "## Systems Processed", ""]

        for name in names:
            work_dir = Path(self.get_work_dir(name))
            spec_dir = work_dir / "spec"
            out += [f"### {name}", ""]

            brief = work_dir / "modeling-brief.md"
            if brief.is_file():
                out.append(f"- **Phase 1 (Analysis)**: OK (modeling-brief: {_wc_l(brief)} lines)")
            else:
                out.append("- **Phase 1 (Analysis)**: MISSING")

            out.append(self._review_line("Analysis Review", work_dir / "review-analysis.md"))

            spec_count = sum(
                (spec_dir / f).is_file() for f in ("base.tla", "MC.tla", "Trace.tla", "instrumentation-spec.md")
            )
            if spec_count == 4:
                out.append(
                    f"- **Phase 2 (Spec Gen)**: OK ({spec_count}/4 files, base: {_wc_l(spec_dir / 'base.tla')} lines)"
                )
            elif spec_count > 0:
                out.append(f"- **Phase 2 (Spec Gen)**: INCOMPLETE ({spec_count}/4 files)")
            else:
                out.append("- **Phase 2 (Spec Gen)**: MISSING")

            out.append(self._review_line("Spec Gen Review", spec_dir / "review-specgen.md"))

            harness_dir = work_dir / "harness"
            traces_dir = work_dir / "traces"
            if (harness_dir / "run.sh").is_file():
                trace_count = len(list(traces_dir.rglob("*.ndjson"))) if traces_dir.is_dir() else 0
                instr_guide = "yes" if (harness_dir / "INSTRUMENTATION.md").is_file() else "no"
                out.append(f"- **Phase 2.5 (Harness)**: OK (traces: {trace_count}, INSTRUMENTATION.md: {instr_guide})")
            elif harness_dir.is_dir():
                out.append("- **Phase 2.5 (Harness)**: INCOMPLETE (harness/ exists but no run.sh)")
            else:
                out.append("- **Phase 2.5 (Harness)**: MISSING")

            changelog = spec_dir / "changelog.md"
            if changelog.is_file() and changelog.stat().st_size > 0:
                out.append(f"- **Phase 3 (Validation)**: changelog written ({_wc_l(changelog)} lines)")
            elif changelog.is_file():
                out.append("- **Phase 3 (Validation)**: changelog empty (check log)")
            else:
                out.append("- **Phase 3 (Validation)**: SKIPPED")

            out.append(self._review_line("Validation Review", spec_dir / "review-validation.md"))

            confirmed = spec_dir / "confirmed-bugs.md"
            if confirmed.is_file() and confirmed.stat().st_size > 0:
                out.append(f"- **Phase 4a (Bug Confirmation)**: confirmed-bugs.md written ({_wc_l(confirmed)} lines)")
            elif confirmed.is_file():
                out.append("- **Phase 4a (Bug Confirmation)**: empty (check log)")
            else:
                out.append("- **Phase 4a (Bug Confirmation)**: SKIPPED")

            rr_files = self._rr_files(name)
            if rr_files:
                # bash grep -lE scans the WHOLE file (unlike rr_status's 25-line
                # window) and matches the status as a prefix — kept faithfully
                rr_resolved = self._status_file_count(rr_files, "RESOLVED")
                rr_deferred = self._status_file_count(rr_files, "DEFERRED")
                out.append(
                    f"- **Repair loop**: {len(rr_files)} request(s) — {rr_resolved} resolved, {rr_deferred} deferred"
                )

            severity = spec_dir / "bug-severity.md"
            if severity.is_file() and severity.stat().st_size > 0:
                out.append(f"- **Phase 4b (Bug Classification)**: bug-severity.md written ({_wc_l(severity)} lines)")
            elif severity.is_file():
                out.append("- **Phase 4b (Bug Classification)**: empty (check log)")
            else:
                out.append("- **Phase 4b (Bug Classification)**: SKIPPED")

            out += ["", "**Logs:**"]
            for log_file in (
                work_dir / "agent.log",
                work_dir / "review-analysis.log",
                work_dir / "spec-gen.log",
                spec_dir / "review-specgen.log",
                spec_dir / "quick-mc.log",
                spec_dir / "review-validation.log",
                work_dir / "bug-confirmation.log",
                work_dir / "bug-classification.log",
            ):
                if log_file.is_file():
                    size = subprocess.run(["du", "-h", str(log_file)], capture_output=True, text=True).stdout.split(
                        "\t"
                    )[0]
                    rel = str(log_file)
                    if rel.startswith(pwd + "/"):
                        rel = rel[len(pwd) + 1 :]
                    out.append(f"- `{rel}` ({size})")
            out.append("")

        content = "\n".join(out) + "\n"
        summary_file.write_text(content)
        sys.stdout.write(content)  # bash: cat "$summary_file"
        print()
        log(f"Summary written to: {summary_file}")

    @staticmethod
    def _review_line(label: str, path: Path) -> str:
        if path.is_file() and path.stat().st_size > 0:
            return f"- **{label}**: written ({_wc_l(path)} lines)"
        if path.is_file():
            return f"- **{label}**: empty (check log)"
        return f"- **{label}**: SKIPPED"

    @staticmethod
    def _status_file_count(files: list[Path], status: str) -> int:
        """Files with ≥1 line matching ^status:[[:space:]]*<status> — bash
        `grep -lE ... | wc -l`."""
        n = 0
        for f in files:
            try:
                text = f.read_text(errors="replace")
            except OSError:
                continue
            if any(re.match(r"status:[ \t\f\v\r]*" + status, ln) for ln in text.splitlines()):
                n += 1
        return n

    # ── main (runs inside the tee) ──
    def main(self) -> int:
        print("╔══════════════════════════════════════════════════════════╗")
        print("║        Specula — Full Pipeline Runner                   ║")
        print("╚══════════════════════════════════════════════════════════╝")
        print()
        print(f"Targets:      {len(self.targets)}")
        print(f"Max parallel: {self.max_parallel}")
        print(f"Max turns:    {self.max_turns}")
        print(f"Agent:        {self.agent}  (claude-alias={self.claude_alias})")
        print()
        print(
            f"Skip phases:  analysis={_b(self.skip_analysis)} specgen={_b(self.skip_specgen)}"
            f" harness={_b(self.skip_harness)} validation={_b(self.skip_validation)}"
            f" confirmation={_b(self.skip_confirmation)} classification={_b(self.skip_classification)}"
            f" reviews={_b(self.skip_reviews)}"
        )
        cap = "unlimited" if self.max_repair_rounds == "0" else self.max_repair_rounds
        print(f"Repair loop:  skip={_b(self.skip_repair_loop)} per_request_cap={cap}")
        print()

        self.validate_agent_adapter()

        names = self.extract_names()

        # If running a single target, cd into its case-study directory so that
        # downstream scripts (which use $PWD/.specula-output) write into the
        # case study's own directory instead of polluting the repo root.
        if len(self.targets) == 1 and names:
            case_dir = SPECULA_ROOT / "case-studies" / names[0]
            if case_dir.is_dir():
                os.chdir(case_dir)
                log(f"Single target: cd to {case_dir}")

        start_time = int(time.time())

        if not self.skip_analysis:
            self.wait_for_quota()
            self.run_phase1_analysis()
            self.run_review("analysis", names)
        else:
            log("Skipping Phase 1 (--skip-analysis)")

        if not self.skip_specgen:
            self.wait_for_quota()
            self.run_phase2_specgen()
            self.run_review("specgen", names)
        else:
            log("Skipping Phase 2 (--skip-specgen)")

        if not self.skip_harness:
            self.wait_for_quota()
            self.run_phase2_5_harness()
        else:
            log("Skipping Phase 2.5 (--skip-harness)")

        if not self.skip_validation:
            self.wait_for_quota()
            self.run_phase3_validation()
            self.run_review("validation", names)
        else:
            log("Skipping Phase 3 (--skip-validation)")

        if not self.skip_confirmation:
            self.wait_for_quota()
            self.run_phase4_confirmation()
        else:
            log("Skipping Phase 4a (--skip-confirmation)")

        if not self.skip_confirmation and not self.skip_repair_loop:
            self.run_repair_loop()
        elif self.skip_repair_loop:
            log("Skipping repair loop (--skip-repair-loop)")

        if not self.skip_classification:
            self.wait_for_quota()
            self.run_phase4b_classification()
        else:
            log("Skipping Phase 4b (--skip-classification)")

        self.generate_summary()

        elapsed = int(time.time()) - start_time
        print()
        log(f"Pipeline completed in {elapsed // 60}m {elapsed % 60}s")
        return 0


def main(argv: list[str]) -> int:
    # bash echo flushed per line; python block-buffers when stdout is a pipe
    # (everything below runs through the tee), which would hold progress lines
    # in the buffer for the hours a phase blocks.
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(line_buffering=True)

    p = Pipeline()
    rc = p.parse_args(argv)
    if rc is not None:
        # --help / unknown option exit before the tee starts, like the bash
        # top-level parse: no .specula-output/, no pipeline.log.
        return rc

    # bash bottom line: mkdir -p "$PWD/.specula-output"; main 2>&1 | tee .../pipeline.log
    # The log lands in the LAUNCH cwd — main's single-target cd happens later,
    # after the tee is already open.
    out_dir = Path.cwd() / ".specula-output"
    out_dir.mkdir(parents=True, exist_ok=True)
    tee = subprocess.Popen(["tee", str(out_dir / "pipeline.log")], stdin=subprocess.PIPE)
    sys.stdout.flush()
    sys.stderr.flush()
    os.dup2(tee.stdin.fileno(), 1)  # fd-level: phase subprocesses inherit the tee
    os.dup2(tee.stdin.fileno(), 2)
    try:
        code = p.main()
    except SystemExit as e:
        code = e.code if isinstance(e.code, int) else 1
    finally:
        sys.stdout.flush()
        sys.stderr.flush()
        # release every write end of the pipe before waiting, or tee never EOFs
        devnull = os.open(os.devnull, os.O_WRONLY)
        os.dup2(devnull, 1)
        os.dup2(devnull, 2)
        os.close(devnull)
        tee.stdin.close()
        tee.wait()
    return code


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
