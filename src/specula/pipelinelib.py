#!/usr/bin/env python3
"""Specula pipeline orchestrator — Python port of scripts/launch/launch_pipeline.sh.

Runs the full phase sequence (analysis → specgen → harness → validation →
confirmation [+ repair loop] → classification → summary) by invoking the
per-phase launchers as subprocesses, exactly like the bash did — the dry-run
command lines, the `main 2>&1 | tee pipeline.log` plumbing, the repair-request
state machine and the quota gate are all faithful ports of the bash, covered by
tests/unit/test_pipelinelib.py and the end-to-end dry-run chain in tests/e2e.

Usage:  python3 pipelinelib.py [options] "name|github|lang|reference" [...]
"""

from __future__ import annotations

import contextlib
import json
import locale
import math
import os
import re
import secrets
import subprocess
import sys
import time
import traceback
from collections.abc import Callable
from datetime import datetime
from pathlib import Path

# The sibling import works in both invocation modes: as a package module
# (`from specula import pipelinelib`; src/ already importable) and as a file
# run by path (the launch_pipeline.sh shim, oracle specroot copies) — path
# invocation puts src/specula/ on sys.path but not src/, so add the package
# root first. In-process only: unlike PYTHONPATH it leaks into no child
# process (see scripts/launch/adapters/claude-code.sh for why that matters).
if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from specula.phaselib import _logical_cwd, _wc_l

# bash pathname expansion (`for f in "$d"/RR-*.md`) orders by the locale
# collating sequence — RR-file glob order feeds ledger rows and repair state
# signatures. Set LC_COLLATE explicitly (idempotent with phaselib's own
# module-level call) rather than relying on the import side effect.
with contextlib.suppress(locale.Error):
    locale.setlocale(locale.LC_COLLATE, "")

SCRIPT_DIR = Path(__file__).resolve().parent  # src/specula
SPECULA_ROOT = SCRIPT_DIR.parent.parent
# the launch_*.sh phase shims and the agent adapters stay under scripts/launch/
LAUNCH_DIR = SPECULA_ROOT / "scripts" / "launch"
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
  --legacy-confirm       Phase 4a: single-agent confirmation instead of the default parallel per-finding
  --max-repair-rounds=N  Per-request repair cap, enforced by re-check (default: 0 = unlimited)
  --enable-reviews        Enable review steps (disabled by default)
  --max-parallel=N       Max concurrent agents per phase (default: 1)
  --max-turns=N          Max agent turns (default: 0 = unlimited)
  --agent=NAME           Agent adapter to use (default: claude-code; e.g., claude-code, codex, copilot-cli)
  --claude-alias=NAME    Claude CLI profile (default: claude)
  --artifact=PATH        Path to system artifact/source code
  --isolate              Isolated workspace (the default): all outputs go to
                         runs/<run-id>/ — parallel-safe, keeps case-studies/
                         pristine. Sources are read from case-studies/<name>/artifact
                         or --artifact; the run root holds no code.
  --no-isolate           Legacy layout: outputs under $PWD/.specula-output
                         (a single target cd's into case-studies/<name>/ when
                         it exists)
  --run-id=ID            Attach to runs/ID — reuse an existing run's workspace,
                         e.g. to resume with --skip-* flags (implies --isolate)

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
# Workspace isolation (step 4): runs/<run-id>/<name>/.specula-output


def generate_run_id() -> str:
    """Sortable, human-readable, collision-safe: 20260703-153000-a1b2."""
    return time.strftime("%Y%m%d-%H%M%S") + "-" + secrets.token_hex(2)


def _valid_run_id(run_id: str) -> bool:
    """Attach ids become a path segment under runs/ — reject anything that
    could escape it (separators, `.`/`..`) or garble logs (whitespace)."""
    return bool(re.fullmatch(r"[A-Za-z0-9._-]+", run_id)) and run_id not in (".", "..")


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
    parity; parse_args validates them at startup (wart fix, step 7 — the bash
    let a garbage threshold read as a parse failure, silently disabling the
    gate), so the float() here only fails for callers that skip parse_args."""
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
    sleep_fn: Callable[[float], object] = time.sleep,
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
            r = subprocess.run(["bash", str(usage_script)], env=env, capture_output=True)
        except OSError:
            r = None  # spawn failure surfaces like the bash `$( ) ||` fetch failure
        if r is None or r.returncode != 0:
            log("WARN: usage fetch failed, proceeding")
            return 0
        check = None
        with contextlib.suppress(UnicodeDecodeError):
            # undecodable bytes broke the bash `python3 -c` heredoc the same way:
            # a parse failure, never an abort — the gate must not kill the run
            check = _quota_check(r.stdout.decode(), q5, q7)
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
        self.confirm_legacy = False  # --legacy-confirm: single-agent Phase 4a instead of the default parallel
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
        # workspace isolation (step 4; default since step 7d) — run_dir stays
        # None only in legacy mode (--no-isolate)
        self.isolate = True
        self._isolate_explicit = False  # an isolation flag was given (vs the default)
        self._no_isolate_given = False
        self.run_id = ""
        self._run_id_given = False  # `--run-id=` (empty) must error, not mint a fresh id
        self.run_dir: Path | None = None
        self.argv: list[str] = []

    # ── argument parsing (runs before the tee starts, like the bash top level) ──
    def parse_args(self, argv: list[str]) -> int | None:
        """Returns an exit code for the pre-tee exits (--help / unknown option),
        None to proceed."""
        self.argv = list(argv)  # recorded verbatim in run.json
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
            elif arg == "--legacy-confirm":
                self.confirm_legacy = True
            elif arg.startswith("--max-repair-rounds="):
                self.max_repair_rounds = arg.split("=", 1)[1]
            elif arg == "--enable-reviews":
                self.skip_reviews = False
            elif arg == "--isolate":
                self.isolate = True
                self._isolate_explicit = True
            elif arg == "--no-isolate":
                self.isolate = False
                self._isolate_explicit = True
                self._no_isolate_given = True
            elif arg.startswith("--run-id="):
                self.run_id = arg.split("=", 1)[1]
                self._run_id_given = True
                self.isolate = True  # attaching implies isolation
                self._isolate_explicit = True
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
            self.targets.append(_logical_cwd().name)  # bash `basename "$PWD"` (logical)
        # order-independent: the two are contradictory however they arrive
        # (e.g. scheduler-injected --run-id + a --no-isolate from queue flags)
        if self._run_id_given and self._no_isolate_given:
            print("ERROR: --no-isolate conflicts with --run-id", file=sys.stderr)
            return 1
        # wart fix (step 7): garbage quota config fails fast (pre-tee, like the
        # option errors). The bash pushed the values into the gate's arithmetic,
        # where a bad threshold read as "usage parse failed" and silently
        # DISABLED the gate, and a bad QUOTA_MAX_WAITS crashed mid-run.
        for label, val, conv in (
            ("QUOTA_5H", self.quota_5h, float),
            ("QUOTA_7D", self.quota_7d, float),
            ("QUOTA_MAX_WAITS", self.quota_max_waits, int),
        ):
            try:
                parsed = conv(val)
            except ValueError:
                print(f"ERROR: {label} must be numeric, got '{val}'", file=sys.stderr)
                return 1
            # inf/nan parse fine but make the gate's `usage > limit` comparison
            # never fire — the same silently-disabled gate this check prevents
            if conv is float and not math.isfinite(parsed):
                print(f"ERROR: {label} must be a finite number, got '{val}'", file=sys.stderr)
                return 1
        return None

    # ── workspace isolation (step 4; runs before the tee so pipeline.log can
    #    land in the run root) ──
    def resolve_run_dir(self) -> int | None:
        """Establish the per-run root. Returns an exit code for an invalid
        --run-id (pre-tee, like the option errors), None to proceed.

        Sources, in priority order: an explicit flag wins (--run-id attach,
        --isolate mint, --no-isolate legacy); then an ambient SPECULA_RUN_DIR
        (scheduler, outer script) is honored as-is; otherwise the default
        mints a fresh isolated run under SPECULA_ROOT/runs (the flip, step 7d
        — the $PWD-derived legacy layout now needs --no-isolate).
        """
        if not self.isolate:
            # explicit --no-isolate: guaranteed-legacy for the whole tree —
            # the phase children must not re-isolate off an ambient run dir
            os.environ.pop("SPECULA_RUN_DIR", None)
            return None
        env_dir = os.environ.get("SPECULA_RUN_DIR", "")
        attached_ambient = bool(env_dir) and not self._isolate_explicit
        if attached_ambient:
            self.run_dir = Path(env_dir)
            self.run_id = self.run_dir.name
        else:
            if self._run_id_given and not _valid_run_id(self.run_id):
                print(f"ERROR: invalid --run-id '{self.run_id}' (allowed: [A-Za-z0-9._-]+)", file=sys.stderr)
                return 1
            if not self._run_id_given:
                self.run_id = generate_run_id()
            self.run_dir = SPECULA_ROOT / "runs" / self.run_id
        self.run_dir.mkdir(parents=True, exist_ok=True)
        os.environ["SPECULA_RUN_DIR"] = str(self.run_dir)  # phase subprocesses inherit
        self._write_run_meta()
        if not attached_ambient:
            # runs/latest -> <run-id>; symlink+rename so readers never see a gap
            with contextlib.suppress(OSError):
                tmp = self.run_dir.parent / f".latest.{self.run_id}.tmp"
                tmp.symlink_to(self.run_id)
                tmp.replace(self.run_dir.parent / "latest")
        return None

    def _write_run_meta(self) -> None:
        """run.json: enough to audit a run after the fact (what ran, with what
        argv, against which artifact revision). Attach never rewrites the
        original record, and metadata must never kill a run."""
        assert self.run_dir is not None
        meta_file = self.run_dir / "run.json"
        if meta_file.exists():
            return
        artifact_sha: str | None = None
        if self.artifact:
            with contextlib.suppress(Exception):
                r = subprocess.run(
                    ["git", "-C", self.artifact, "rev-parse", "HEAD"],
                    capture_output=True,
                )
                if r.returncode == 0:
                    artifact_sha = r.stdout.decode(errors="replace").strip()
        meta = {
            "run_id": self.run_id,
            "created": _date_iseconds(),
            "argv": self.argv,
            "targets": self.targets,
            "agent": self.agent,
            "claude_alias": self.claude_alias,
            "artifact": self.artifact,
            "artifact_git_sha": artifact_sha,
        }
        with contextlib.suppress(OSError):
            meta_file.write_text(json.dumps(meta, indent=2) + "\n")

    # ── utilities ──
    def extract_names(self) -> list[str]:
        """First '|' field of each target, trimmed — one name per target. Wart
        fix (step 7): the bash flattened the list through `echo ${names[@]}` +
        `read -ra`, so a name with internal whitespace silently split into
        several phantom targets; a whitespace-only name still contributes
        nothing (the bash word-split dropped those too)."""
        names: list[str] = []
        for target in self.targets:
            # bash `IFS='|' read -r name _ _ _ <<< "$target"` reads only the
            # first line, so a newline terminates the name before the '|' split.
            first_line = target.split("\n", 1)[0]
            name = first_line.split("|", 1)[0].strip()
            if name:
                names.append(name)
        return names

    def validate_agent_adapter(self) -> None:
        adapter = LAUNCH_DIR / "adapters" / f"{self.agent}.sh"
        if not adapter.is_file():
            print(
                f"ERROR: Unknown agent '{self.agent}' — adapter not found at {adapter}",
                file=sys.stderr,
            )
            raise SystemExit(1)

    def get_work_dir(self, name: str) -> str:
        """Legacy: $PWD is evaluated at call time — after the single-target cd.
        Isolated: uniform batch-style layout under the run root (mirrors
        Workspace.work_dir; the isolation tests pin both against drift)."""
        if self.run_dir:
            return f"{self.run_dir}/{name}/.specula-output"
        if len(self.targets) == 1:
            return f"{_logical_cwd()}/.specula-output"
        return f"{_logical_cwd()}/{name}/.specula-output"

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
        r = subprocess.run(["bash", str(LAUNCH_DIR / script), *args])
        if r.returncode != 0:
            # bash set -e: a failing phase aborts the run. Signal death arrives
            # as a negative returncode — report 128+N like the bash did (143,
            # not the mod-256 wraparound 241), schedulers classify kills by it.
            code = 128 - r.returncode if r.returncode < 0 else r.returncode
            raise SystemExit(code)

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
        # launch_review.sh's contract is `<phase> <name...>`: it reads the phase
        # from the first positional (ReviewPhase.run: phase = argv[0]) and treats
        # every other non-flag arg as a target. The pre-migration bash emitted the
        # flags BEFORE the phase, so a real run parsed phase as "--agent=..." and
        # died with "Unknown phase" — invisible under --dry-run, which only logs
        # the command without executing it. Phase goes first: a deliberate
        # divergence from the buggy bash order (git history has the original).
        args = [phase, f"--agent={self.agent}", f"--claude-alias={self.claude_alias}", *names]
        self._phase(f"REVIEW: {phase}", "launch_review.sh", args)

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
        pre: list[str] = []
        if self.confirm_legacy:
            pre.append("--legacy-confirm")
        mode = "single-agent, legacy" if self.confirm_legacy else "parallel per-finding"
        self._phase(
            f"PHASE 4: BUG CONFIRMATION ({mode})",
            "launch_bug_confirmation.sh",
            self._phase_args(self.extract_names(), pre=pre or None),
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

        if self.run_dir:
            # run-scoped artifacts live at the run root, next to pipeline.log
            pwd = str(self.run_dir)  # base for the Logs section's relative paths
            summary_file = self.run_dir / "pipeline-summary.md"
        else:
            pwd = str(_logical_cwd())  # bash $PWD, matching get_work_dir and the tee log dir
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
                # bash `find "$traces_dir" -name '*.ndjson'` (default -P) does not
                # descend a symlinked start dir; is_dir() alone would follow it.
                trace_count = (
                    len(list(traces_dir.rglob("*.ndjson")))
                    if traces_dir.is_dir() and not traces_dir.is_symlink()
                    else 0
                )
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
            # wart fix (step 7): the bash candidate list skipped the phase-2.5
            # and phase-3 agent logs (harness-gen.log, spec-validation.log)
            for log_file in (
                work_dir / "agent.log",
                work_dir / "review-analysis.log",
                work_dir / "spec-gen.log",
                spec_dir / "review-specgen.log",
                work_dir / "harness-gen.log",
                work_dir / "spec-validation.log",
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
        """Files whose status (as the state machine reads it: rr_status's
        25-line frontmatter window, exact token) equals `status`. Wart fix
        (step 7): the bash summary used `grep -lE '^status:[[:space:]]*X' |
        wc -l` — whole file, prefix match — so it could disagree with the
        repair loop's own reads (a buried `status:` line counted here but not
        there) and RESOLVEDX counted as RESOLVED."""
        return sum(1 for f in files if rr_status(f) == status)

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
        if self.run_dir:
            print(f"Run:          {self.run_id}  ({self.run_dir})")
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
        # Isolated runs never cd — outputs go to the run root regardless.
        if len(self.targets) == 1:
            if not names:
                # bash died here (`names[0]: unbound variable` under set -u):
                # fail fast before any phase runs on a nameless target.
                log(f"ERROR: no target name parsed from '{self.targets[0]}', aborting")
                raise SystemExit(1)
            if not self.run_dir:
                # string concat like the bash — a pathlib join would let an absolute
                # name discard the case-studies prefix and cd anywhere
                case_dir = Path(f"{SPECULA_ROOT}/case-studies/{names[0]}")
                if case_dir.is_dir():
                    os.chdir(case_dir)
                    os.environ["PWD"] = str(case_dir)  # bash cd exports the new $PWD
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
    rc = p.resolve_run_dir()
    if rc is not None:
        return rc  # invalid --run-id: pre-tee exit, like the option errors

    if p.run_dir:
        # isolated: the log is a run-scoped artifact, it lives at the run root
        log_path = p.run_dir / "pipeline.log"
    else:
        # bash bottom line: mkdir -p "$PWD/.specula-output"; main 2>&1 | tee .../pipeline.log
        # The log lands in the LAUNCH cwd — main's single-target cd happens later,
        # after the tee is already open.
        out_dir = _logical_cwd() / ".specula-output"
        out_dir.mkdir(parents=True, exist_ok=True)
        log_path = out_dir / "pipeline.log"
    tee = subprocess.Popen(["tee", str(log_path)], stdin=subprocess.PIPE)
    assert tee.stdin is not None  # stdin=PIPE
    tee_in = tee.stdin
    sys.stdout.flush()
    sys.stderr.flush()
    os.dup2(tee_in.fileno(), 1)  # fd-level: phase subprocesses inherit the tee
    os.dup2(tee_in.fileno(), 2)
    try:
        code = p.main()
    except SystemExit as e:
        code = e.code if isinstance(e.code, int) else 1
    except BaseException as e:
        # Print while fd 2 still feeds the tee: after the finally below it is
        # /dev/null, and an escaping exception would die with no diagnostics
        # anywhere. bash `set -e` left the failing command's stderr in the log.
        traceback.print_exc()
        code = 130 if isinstance(e, KeyboardInterrupt) else 1  # 128+SIGINT, like bash
    finally:
        sys.stdout.flush()
        sys.stderr.flush()
        # release every write end of the pipe before waiting, or tee never EOFs
        devnull = os.open(os.devnull, os.O_WRONLY)
        os.dup2(devnull, 1)
        os.dup2(devnull, 2)
        os.close(devnull)
        tee_in.close()
        # bash pipefail: the pipeline's status is the rightmost command to exit
        # non-zero, so a failing tee (unwritable/full log) wins even when main
        # also failed — verified: `set -o pipefail; (exit 2)|(exit 1)` exits 1.
        tee_rc = tee.wait()
        if tee_rc != 0:
            code = tee_rc
    return code


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
