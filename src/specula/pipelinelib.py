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
import signal
import subprocess
import sys
import time
import traceback
from collections.abc import Callable
from datetime import datetime
from pathlib import Path
from typing import Any

# The sibling import works in both invocation modes: as a package module
# (`from specula import pipelinelib`; src/ already importable) and as a file
# run by path (the launch_pipeline.sh shim, oracle specroot copies) — path
# invocation puts src/specula/ on sys.path but not src/, so add the package
# root first. In-process only: unlike PYTHONPATH it leaks into no child
# process (see scripts/launch/adapters/claude-code.sh for why that matters).
if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from specula import quota as _quota
from specula.phaselib import (
    DEFAULT_POLICY_RETRIES,
    _logical_cwd,
    _normalize_artifact_dir,
    _parse_policy_retries,
    _wc_l,
)
from specula.tlc_resources import (
    MEMORY_LIMIT_ENV,
    RUN_POLICY_FILENAME,
    SCOPE_ENV,
    WORKER_LIMIT_ENV,
    parse_memory_limit,
    parse_worker_limit,
)

RATE_LIMIT_FALLBACK_SECONDS = _quota.RATE_LIMIT_FALLBACK_SECONDS
RATE_LIMIT_RC = _quota.RATE_LIMIT_RC
RATE_LIMIT_RETRIES = _quota.RATE_LIMIT_RETRIES
_epoch = _quota._epoch
_quota_check = _quota._quota_check
_wait_for_quota = _quota.wait_for_quota

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
PHASE_TERMINATION_GRACE_SECONDS = 3.0

USAGE = """
Full Specula pipeline: Code Analysis → Spec Generation → Harness Generation → Validation + Bug Hunting

Runs all phases with optional review agents between each phase.
All agent logs and review results are saved for inspection.

Usage:
  specula run [options] "name|github|lang|reference" [...]

Example (single system):
  specula run "cometbft|cometbft/cometbft|Go|Tendermint BFT"

Example (multiple systems):
  specula run \\
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
  --confirm-debate       Phase 4a: add the adversarial Challenger debate (parallel mode; default off)
  --max-repair-rounds=N  Global repair-loop round cap; unresolved requests are then filed under deferred/ (default: 10; 0 = unlimited)
  --enable-reviews        Enable review steps (disabled by default)
  --max-parallel=N       Hard limit for concurrent agents. When omitted, ordinary phases run 1 target
                         agent at a time and per-finding bug confirmation runs up to 4 at a time
  --max-turns=N          Max agent turns (default: 0 = unlimited)
  --policy-retries=N     Policy-block continuation retries after the initial attempt (default: 20; 0 disables)
  --agent=NAME           Agent adapter to use (default: claude-code; e.g., claude-code, codex, copilot-cli, opencode, pi)
  --claude-alias=NAME    Claude CLI profile (default: claude)
  --model=NAME           Model forwarded to every agent adapter
  --effort=LEVEL         Reasoning effort forwarded to every agent adapter
  --artifact=PATH        Path to system artifact/source code
  --tlc-memory-limit=SIZE
                         Aggregate -m + -M budget for TLCs in this run (default: auto,
                         80% of effective available memory at the first TLC start)
  --tlc-worker-limit=N   Optional aggregate TLC worker bound (default: unset; report only)
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
# the bug-confirmation skill's repair-request format.
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
def wait_for_quota(
    usage_script: str | Path,
    q5: str,
    q7: str,
    max_waits: str,
    claude_alias: str,
    sleep_fn: Callable[[float], object] = time.sleep,
    *,
    reactive: bool = False,
    fallback_seconds: float | None = None,
) -> int:
    """Compatibility wrapper retaining pipelinelib's timestamped logging."""
    return _wait_for_quota(
        usage_script=usage_script,
        q5=q5,
        q7=q7,
        max_waits=max_waits,
        claude_alias=claude_alias,
        sleep_fn=sleep_fn,
        log_fn=log,
        reactive=reactive,
        fallback_seconds=fallback_seconds,
    )


class Pipeline:
    """Parsed configuration + the phase sequencing of the bash `main`."""

    def __init__(self) -> None:
        # None means the user omitted the flag, so each phase applies its own
        # default (1 normally; 4 for per-finding bug confirmation). A string,
        # including "", is an explicit value forwarded for launcher validation.
        self.max_parallel: str | None = None
        self.max_turns = "0"  # deprecated verbatim passthrough
        self.policy_retries = DEFAULT_POLICY_RETRIES
        self.dry_run = False
        self.skip_analysis = False
        self.skip_specgen = False
        self.skip_harness = False
        self.skip_validation = False
        self.skip_confirmation = False
        self.skip_classification = False
        self.skip_repair_loop = False
        self.confirm_legacy = False  # --legacy-confirm: single-agent Phase 4a instead of the default parallel
        self.confirm_debate = False  # --confirm-debate: add the adversarial Challenger (parallel mode)
        # `or`: bash ${VAR:-default} treats an exported-but-empty var as unset
        self.max_repair_rounds = os.environ.get("MAX_REPAIR_ROUNDS") or "10"
        self.skip_reviews = True
        self.agent = "claude-code"
        self.claude_alias = os.environ.get("CLAUDE_ALIAS") or "claude"
        # None means no pipeline CLI override: phase launchers may consult
        # SPECULA_MODEL / SPECULA_EFFORT.  "" is an explicit empty flag and
        # must survive into the child so it can clear those environment values.
        self.model: str | None = None
        self.effort: str | None = None
        self.artifact = ""
        self._artifact_given = False
        self.tlc_memory_limit: str | None = None
        self.tlc_worker_limit: str | None = None
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
        self.tlc_scope = ""
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
            elif arg == "--confirm-debate":
                self.confirm_debate = True
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
            elif arg.startswith("--policy-retries="):
                raw = arg.split("=", 1)[1]
                try:
                    self.policy_retries = _parse_policy_retries(raw)
                except ValueError:
                    print(
                        f"ERROR: --policy-retries must be a non-negative integer, got '{raw}'",
                        file=sys.stderr,
                    )
                    return 1
            elif arg.startswith("--agent="):
                self.agent = arg.split("=", 1)[1]
            elif arg.startswith("--claude-alias="):
                self.claude_alias = arg.split("=", 1)[1]
            elif arg.startswith("--model="):
                self.model = arg.split("=", 1)[1]
            elif arg.startswith("--effort="):
                self.effort = arg.split("=", 1)[1]
            elif arg.startswith("--artifact="):
                self.artifact = arg.split("=", 1)[1]
                self._artifact_given = True
            elif arg.startswith("--tlc-memory-limit="):
                self.tlc_memory_limit = arg.split("=", 1)[1]
            elif arg.startswith("--tlc-worker-limit="):
                self.tlc_worker_limit = arg.split("=", 1)[1]
            elif arg in ("--help", "-h"):
                sys.stdout.write(USAGE)
                return 0
            elif arg.startswith("-"):
                print(f"Unknown option: {arg}")
                return 1
            else:
                self.targets.append(arg)
        if self.confirm_legacy and self.confirm_debate:
            print("ERROR: --legacy-confirm conflicts with --confirm-debate", file=sys.stderr)
            return 1
        if not self.targets:
            self.targets.append(_logical_cwd().name)  # bash `basename "$PWD"` (logical)
        # order-independent: the two are contradictory however they arrive
        # (e.g. scheduler-injected --run-id + a --no-isolate from queue flags)
        if self._run_id_given and self._no_isolate_given:
            print("ERROR: --no-isolate conflicts with --run-id", file=sys.stderr)
            return 1
        if self._artifact_given:
            normalized_artifact = _normalize_artifact_dir(self.artifact)
            if normalized_artifact is None:
                print(f"ERROR: --artifact must be an existing directory: {self.artifact}", file=sys.stderr)
                return 1
            # The legacy single-target flow may chdir before launching phases.
            # Stabilize a relative CLI path while it still refers to the caller's cwd.
            self.artifact = normalized_artifact

        memory_limit = self.tlc_memory_limit
        if memory_limit is None:
            memory_limit = os.environ.get(MEMORY_LIMIT_ENV) or None
        worker_limit = self.tlc_worker_limit
        if worker_limit is None:
            worker_limit = os.environ.get(WORKER_LIMIT_ENV) or None
        try:
            if memory_limit is not None:
                parse_memory_limit(memory_limit)
            if worker_limit is not None:
                parse_worker_limit(worker_limit)
        except ValueError as exc:
            print(f"ERROR: {exc}", file=sys.stderr)
            return 1

        # Validate the repair budget before any phase starts.  int() in
        # run_repair_loop used to make malformed values fail only after the
        # expensive foreground phases had completed, while a negative value
        # silently skipped every round and immediately deferred all OPEN work.
        if not re.fullmatch(r"[0-9]+", self.max_repair_rounds):
            print(
                "ERROR: MAX_REPAIR_ROUNDS/--max-repair-rounds must be a non-negative integer, "
                f"got '{self.max_repair_rounds}'",
                file=sys.stderr,
            )
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
            # Legacy targets have different SPECULA_WORK_DIR values. Give the
            # whole top-level invocation one absolute, unique resource scope so
            # concurrent TLCs across those targets still share one budget.
            scope_name = f".specula-tlc-scope-{os.getpid()}-{secrets.token_hex(8)}"
            self.tlc_scope = str((_logical_cwd() / scope_name).resolve())
            os.environ[SCOPE_ENV] = self.tlc_scope
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
        self.tlc_scope = str(self.run_dir.resolve())
        os.environ[SCOPE_ENV] = self.tlc_scope
        resource_rc = self._restore_run_resource_config()
        if resource_rc is not None:
            return resource_rc
        self._write_run_meta()
        if not attached_ambient:
            # runs/latest -> <run-id>; symlink+rename so readers never see a gap
            with contextlib.suppress(OSError):
                tmp = self.run_dir.parent / f".latest.{self.run_id}.tmp"
                tmp.symlink_to(self.run_id)
                tmp.replace(self.run_dir.parent / "latest")
        return None

    def _restore_run_resource_config(self) -> int | None:
        """Create or restore the immutable, durable TLC policy for a run."""
        assert self.run_dir is not None
        policy_file = self.run_dir / RUN_POLICY_FILENAME
        meta_file = self.run_dir / "run.json"
        current_memory = self.tlc_memory_limit
        if current_memory is None:
            current_memory = os.environ.get(MEMORY_LIMIT_ENV) or None
        current_workers = self.tlc_worker_limit
        if current_workers is None:
            current_workers = os.environ.get(WORKER_LIMIT_ENV) or None

        source = policy_file
        policy: object
        publish_policy = not policy_file.exists()
        if not publish_policy:
            try:
                policy = json.loads(policy_file.read_text())
            except (OSError, json.JSONDecodeError) as exc:
                print(f"ERROR: cannot restore TLC resource config from {policy_file}: {exc}", file=sys.stderr)
                return 1
        else:
            stored_memory: object = current_memory or "auto"
            stored_workers: object = current_workers
            if meta_file.exists():
                try:
                    loaded_meta = json.loads(meta_file.read_text())
                    if not isinstance(loaded_meta, dict):
                        raise ValueError("expected an object")
                    candidate_memory = loaded_meta.get("tlc_memory_limit", stored_memory)
                    candidate_workers = loaded_meta.get("tlc_worker_limit", stored_workers)
                    if not isinstance(candidate_memory, str) or (
                        candidate_workers is not None and not isinstance(candidate_workers, str)
                    ):
                        raise ValueError("invalid TLC resource fields")
                    parse_memory_limit(candidate_memory)
                    if candidate_workers is not None:
                        parse_worker_limit(candidate_workers)
                    stored_memory = candidate_memory
                    stored_workers = candidate_workers
                except (OSError, json.JSONDecodeError, ValueError) as exc:
                    print(
                        f"WARNING: ignoring TLC resource fields in audit metadata {meta_file}: {exc}",
                        file=sys.stderr,
                    )
            policy = {
                "version": 1,
                "memory_limit": stored_memory,
                "worker_limit": stored_workers,
            }

        if not isinstance(policy, dict) or policy.get("version") != 1:
            print(f"ERROR: invalid TLC resource config in {source}", file=sys.stderr)
            return 1
        stored_memory = policy.get("memory_limit")
        stored_workers = policy.get("worker_limit")
        if not isinstance(stored_memory, str) or (stored_workers is not None and not isinstance(stored_workers, str)):
            print(f"ERROR: invalid TLC resource config in {source}", file=sys.stderr)
            return 1
        try:
            stored_memory_value = parse_memory_limit(stored_memory)
            stored_worker_value = parse_worker_limit(stored_workers) if stored_workers is not None else None
        except ValueError as exc:
            print(f"ERROR: invalid TLC resource config in {source}: {exc}", file=sys.stderr)
            return 1

        if current_memory is None:
            self.tlc_memory_limit = stored_memory
        elif parse_memory_limit(current_memory) != stored_memory_value:
            print(
                f"ERROR: this Specula run already uses TLC memory limit {stored_memory}; "
                "the limit cannot change when resuming",
                file=sys.stderr,
            )
            return 1
        if current_workers is None:
            self.tlc_worker_limit = stored_workers
        elif stored_worker_value is None or parse_worker_limit(current_workers) != stored_worker_value:
            label = "unbounded" if stored_workers is None else stored_workers
            print(
                f"ERROR: this Specula run already uses TLC worker limit {label}; the limit cannot change when resuming",
                file=sys.stderr,
            )
            return 1
        if publish_policy:
            try:
                self._atomic_publish_text_no_replace(policy_file, json.dumps(policy, indent=2) + "\n")
            except FileExistsError:
                # A simultaneous attach won creation. Reload its policy and
                # compare instead of overwriting the run-wide bound.
                return self._restore_run_resource_config()
            except OSError as exc:
                print(f"ERROR: cannot persist TLC resource config to {policy_file}: {exc}", file=sys.stderr)
                return 1
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
        model, effort = self._resolved_run_tuning()
        meta = {
            "run_id": self.run_id,
            "created": _date_iseconds(),
            "argv": self.argv,
            "targets": self.targets,
            "agent": self.agent,
            "model": model,
            "effort": effort,
            "policy_retries": self.policy_retries,
            "claude_alias": self.claude_alias,
            "artifact": self.artifact,
            "artifact_git_sha": artifact_sha,
            "tlc_memory_limit": self.tlc_memory_limit or os.environ.get(MEMORY_LIMIT_ENV) or "auto",
            "tlc_worker_limit": self.tlc_worker_limit or os.environ.get(WORKER_LIMIT_ENV) or None,
        }
        with contextlib.suppress(OSError):
            meta_file.write_text(json.dumps(meta, indent=2) + "\n")

    def _resolved_run_tuning(self) -> tuple[str | None, str | None]:
        """Return model/effort values that are knowable at run creation.

        Pipeline flags win even when explicitly empty. An empty flag resets the
        adapter to its own configuration, whose resulting value is unknown here
        and therefore recorded as null. Otherwise mirror the phase and adapter
        environment fallbacks; never guess values selected by CLI config files.
        """
        if self.model is not None:
            model = self.model or None
        else:
            model = os.environ.get("SPECULA_MODEL") or None
            if model is None:
                adapter_model_env = {
                    "claude-code": "CLAUDE_MODEL",
                    "codex": "CODEX_MODEL",
                    "copilot-cli": "COPILOT_MODEL",
                    "opencode": "OPENCODE_MODEL",
                    "pi": "PI_MODEL",
                }.get(self.agent)
                if adapter_model_env is not None:
                    model = os.environ.get(adapter_model_env) or None

        if self.effort is not None:
            effort = self.effort or None
        else:
            effort = os.environ.get("SPECULA_EFFORT") or None
            if effort is None:
                if self.agent == "claude-code":
                    # Phase launchers explicitly pass max, overriding any
                    # ambient CLAUDE_EFFORT value.
                    effort = "max"
                else:
                    effort_env = {
                        "codex": "CODEX_EFFORT",
                        "opencode": "OPENCODE_EFFORT",
                        "pi": "PI_EFFORT",
                    }.get(self.agent)
                    if effort_env is not None:
                        effort = os.environ.get(effort_env) or None

        # The Claude adapter omits --effort for this explicit reset sentinel.
        if self.agent == "claude-code" and effort == "default":
            effort = None
        return model, effort

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

    def wait_for_quota(self, *, reactive: bool = False) -> None:
        wait_for_quota(
            usage_script=USAGE_SCRIPT,
            q5=self.quota_5h,
            q7=self.quota_7d,
            max_waits=self.quota_max_waits,
            claude_alias=self.claude_alias,
            reactive=reactive,
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

    def _deferred_rr_files(self, name: str) -> list[Path]:
        d = Path(self.repair_dir(name)) / "deferred"
        if not d.is_dir():
            return []
        return sorted(d.glob("RR-*.md"), key=lambda p: locale.strxfrm(p.name))

    def has_any_request(self) -> bool:
        return any(self._rr_files(n) for n in self.extract_names())

    def has_open_repair_requests(self) -> bool:
        """True if any repair request in the active queue still needs repair
        (status != CONSUMED). Requests already filed under deferred/ are excluded
        — the RR-*.md glob is not recursive. The loop runs until none remain, or
        the global round cap is hit (after which the orchestrator defers them)."""
        for n in self.extract_names():
            for f in self._rr_files(n):
                if rr_status(f) != "CONSUMED":
                    return True
        return False

    def names_with_open_repair_requests(self) -> list[str]:
        """Targets whose active queue contains a non-terminal request."""
        return [n for n in self.extract_names() if any(rr_status(f) != "CONSUMED" for f in self._rr_files(n))]

    def repair_state_sig(self) -> str:
        """Stable signature of every request's (id, status, round). A round that
        leaves this unchanged made no progress — stop, rather than spin (covers
        --dry-run and a misbehaving agent that never transitions a request)."""
        lines = []
        for n in self.extract_names():
            for f in self._rr_files(n):
                lines.append(f"{f.name}:{rr_status(f)}:{rr_field(f, 'round')}")
        return "\n".join(lines)

    def reset_stale_in_repair(self, name: str | None = None) -> None:
        """Crash recovery: a request stuck IN_REPAIR means its repair phase died
        mid-turn. Reset to OPEN so the next round retries it."""
        if self.dry_run:
            return
        names = [name] if name is not None else self.extract_names()
        for n in names:
            for f in self._rr_files(n):
                if rr_status(f) == "IN_REPAIR":
                    text = f.read_text(errors="replace")
                    if not self._repair_request_is_executable(text, f.stem):
                        log(
                            f"ERROR: stale {f.name} is malformed and has no durable Phase 3 snapshot; "
                            "refusing to reset it to OPEN."
                        )
                        raise SystemExit(1)
                    recovered = self._repair_request_text_with_status(
                        text,
                        "OPEN",
                        "reset (orchestrator): repair phase did not complete; retrying",
                    )
                    self._atomic_replace_text(f, recovered)
                    log(f"  reset {f.name} IN_REPAIR -> OPEN (crash recovery)")

    def snapshot_open_repair_requests(self, name: str | None = None) -> dict[Path, str]:
        """Capture the exact requests a repair Phase 3 is responsible for.

        A failing agent may update a request to CONSUMED before its process
        exits non-zero. The snapshot lets recovery recreate a deleted/corrupt
        request, while a surviving request keeps the failed attempt's history.
        """
        names = [name] if name is not None else self.extract_names()
        return {f: f.read_text() for n in names for f in self._rr_files(n) if rr_status(f) == "OPEN"}

    def repair_phase3_snapshot_path(self, name: str) -> Path:
        return Path(self.get_work_dir(name)) / "spec" / ".repair-phase3-snapshot.json"

    def persist_open_repair_snapshot(self, name: str, snapshot: dict[Path, str], round_: int) -> None:
        """Durably publish the OPEN inputs before a repair subprocess starts.

        The unique commit token is copied into confirmation-generation.json
        only after the repair launcher returns success.  Recovery can therefore
        distinguish a completed Phase 3 whose snapshot cleanup was interrupted
        from an attempt killed after merely writing CONSUMED into its requests.
        """
        if self.dry_run:
            return
        rr_dir = Path(self.repair_dir(name))
        requests: dict[str, str] = {}
        for path, text in snapshot.items():
            if path.parent != rr_dir or re.fullmatch(r"RR-\d+\.md", path.name) is None:
                raise RuntimeError(f"invalid repair snapshot path for {name}: {path}")
            if (
                not self._repair_request_is_executable(text, path.stem)
                or self._repair_request_field(text, "status") != "OPEN"
            ):
                raise RuntimeError(f"refusing to snapshot malformed/non-OPEN repair request: {path}")
            requests[path.name] = text
        if not requests:
            raise RuntimeError(f"refusing to publish an empty repair snapshot for {name}")
        marker = self.repair_phase3_snapshot_path(name)
        payload = (
            json.dumps(
                {
                    "version": 2,
                    "round": round_,
                    "commit_token": secrets.token_hex(16),
                    "requests": requests,
                },
                ensure_ascii=False,
                sort_keys=True,
            )
            + "\n"
        )
        try:
            self._publish_deferred_no_replace(marker, payload)
        except FileExistsError:
            log(f"ERROR: durable Phase 3 snapshot already exists for {name}: {marker}")
            raise SystemExit(1) from None

    def load_open_repair_snapshot(self, name: str) -> tuple[dict[Path, str], int, str | None] | None:
        marker = self.repair_phase3_snapshot_path(name)
        if not marker.is_file():
            return None
        try:
            doc = json.loads(marker.read_text())
            version = doc.get("version") if isinstance(doc, dict) else None
            round_ = doc.get("round") if isinstance(doc, dict) else None
            requests = doc.get("requests") if isinstance(doc, dict) else None
            commit_token = doc.get("commit_token") if isinstance(doc, dict) else None
            if version not in {1, 2} or not isinstance(round_, int) or isinstance(round_, bool) or round_ < 1:
                raise ValueError("invalid version/round")
            if version == 1:
                # Version 1 had no attempt identity, so an old generation
                # marker cannot prove that this exact snapshot committed.
                commit_token = None
            elif not isinstance(commit_token, str) or re.fullmatch(r"[0-9a-f]{32}", commit_token) is None:
                raise ValueError("invalid commit token")
            if not isinstance(requests, dict) or not requests:
                raise ValueError("requests must be a non-empty object")
            snapshot: dict[Path, str] = {}
            rr_dir = Path(self.repair_dir(name))
            for filename, text in requests.items():
                if not isinstance(filename, str) or re.fullmatch(r"RR-\d+\.md", filename) is None:
                    raise ValueError(f"unsafe request filename {filename!r}")
                if not isinstance(text, str) or not self._repair_request_is_executable(text, Path(filename).stem):
                    raise ValueError(f"malformed request snapshot {filename}")
                if self._repair_request_field(text, "status") != "OPEN":
                    raise ValueError(f"snapshot request {filename} is not OPEN")
                snapshot[rr_dir / filename] = text
        except (OSError, ValueError, json.JSONDecodeError) as exc:
            log(f"ERROR: invalid durable Phase 3 snapshot for {name}: {marker} ({exc})")
            raise SystemExit(1) from exc
        return snapshot, round_, commit_token

    def clear_open_repair_snapshot(self, name: str) -> None:
        if not self.dry_run:
            self.repair_phase3_snapshot_path(name).unlink(missing_ok=True)

    def recover_interrupted_phase3(self) -> set[str]:
        """Finalize a committed attempt or restore one killed before commit.

        Return the exact targets whose Phase-3 commit was recovered. Callers
        must not treat one target's commit as coverage for any other target.
        """
        if self.dry_run:
            return set()
        recovered_commits: set[str] = set()
        for name in self.extract_names():
            loaded = self.load_open_repair_snapshot(name)
            if loaded is None:
                continue
            snapshot, round_, commit_token = loaded
            if self._repair_phase3_snapshot_committed(name, snapshot, round_, commit_token):
                self.clear_open_repair_snapshot(name)
                recovered_commits.add(name)
                log(f"  finalized committed repair Phase 3 for {name} after interrupted snapshot cleanup")
                continue
            self.restore_open_repair_requests(snapshot, round_)
            self.clear_open_repair_snapshot(name)
            log(f"  recovered durable Phase 3 snapshot for {name} after interrupted repair")
        return recovered_commits

    def _repair_phase3_snapshot_committed(
        self,
        name: str,
        snapshot: dict[Path, str],
        round_: int,
        commit_token: str | None,
    ) -> bool:
        """Whether the exact snapshotted attempt crossed its durable commit point.

        CONSUMED alone is not proof: an agent can write it before failing.  The
        generation marker is published by the orchestrator only after a zero
        exit, and contains the snapshot's unique attempt token.
        Complete, executable CONSUMED requests are required as a second guard.
        """
        if commit_token is None:
            return False
        marker = Path(self.get_work_dir(name)) / "spec" / "confirmation-generation.json"
        try:
            doc = json.loads(marker.read_text())
        except (OSError, json.JSONDecodeError):
            return False
        if not isinstance(doc, dict):
            return False
        if doc.get("repair_round") != round_ or doc.get("repair_phase3_commit") != commit_token:
            return False
        for path in snapshot:
            try:
                current = path.read_text()
            except OSError:
                return False
            if self._repair_request_field(current, "status") != "CONSUMED" or not self._repair_request_is_executable(
                current, path.stem
            ):
                return False
        return True

    def restore_open_repair_requests(self, snapshot: dict[Path, str], round_: int) -> None:
        """Make one failed target's original OPEN set retryable without lying.

        Phase 3 may have partially edited the spec/output before it exits
        non-zero. Those arbitrary filesystem changes cannot be rolled back by
        rewriting the RR alone. Restore the snapshot's complete executable
        semantics, merge only newly appended audit bullets from an identifiable
        current file, reset it to OPEN, and note that partial artifacts remain.
        """
        if self.dry_run:
            return
        reason = (
            f"reset (orchestrator): repair round {round_} Phase 3 failed; "
            "partial spec/output changes were retained for inspection; retrying OPEN"
        )
        for f, original in snapshot.items():
            f.parent.mkdir(parents=True, exist_ok=True)
            current = ""
            with contextlib.suppress(OSError):
                current = f.read_text(errors="replace")
            base = original
            if current and self._repair_request_field(current, "id") == f.stem:
                original_history = set(self._repair_request_history_bullets(original))
                additions = [
                    line for line in self._repair_request_history_bullets(current) if line not in original_history
                ]
                if additions:
                    base = original.rstrip("\n") + "\n" + "\n".join(additions) + "\n"
            restored = self._repair_request_text_with_status(base, "OPEN", reason)
            self._atomic_replace_text(f, restored)
            log(f"  reset {f.name} to OPEN after failed repair Phase 3 (partial artifacts retained)")

    @staticmethod
    def _repair_request_history_bullets(text: str) -> list[str]:
        """Single-line audit entries after the request's History heading."""
        match = re.search(r"(?m)^##\s+History\s*$", text)
        if match is None:
            return []
        return [line for line in text[match.end() :].splitlines() if line.startswith("- ")]

    @staticmethod
    def _repair_request_field(text: str, key: str) -> str:
        lines = text.splitlines()
        if lines and lines[0] == "---":
            try:
                lines = lines[1 : lines.index("---", 1)]
            except ValueError:
                return ""
        else:
            lines = lines[:25]
        prefix = key + ":"
        for line in lines:
            if line.startswith(prefix):
                return line[len(prefix) :].strip()
        return ""

    @classmethod
    def _repair_request_is_executable(cls, text: str, expected_id: str) -> bool:
        """Minimum dispatcher-owned lifecycle shape for a repair request."""
        lines = text.splitlines()
        if not lines or lines[0] != "---":
            return False
        try:
            lines.index("---", 1)
        except ValueError:
            return False
        if cls._repair_request_field(text, "id") != expected_id:
            return False
        if cls._repair_request_field(text, "status") not in {"OPEN", "IN_REPAIR", "CONSUMED"}:
            return False
        return cls._repair_request_field(text, "round").isdigit()

    @staticmethod
    def _repair_request_text_with_status(text: str, status: str, note: str) -> str:
        """Return a complete request with a canonical status and history note."""
        lines = text.splitlines(keepends=True)
        found = False
        for i, line in enumerate(lines[:25]):
            if line.startswith("status:"):
                lines[i] = f"status: {status}\n"
                found = True
                break
        if not found:
            insert_at = 1 if lines and lines[0].strip() == "---" else 0
            lines.insert(insert_at, f"status: {status}\n")
        if lines and not lines[-1].endswith("\n"):
            lines[-1] += "\n"
        lines.append(f"- {note}\n")
        return "".join(lines)

    @staticmethod
    def _atomic_replace_text(path: Path, text: str) -> None:
        """Publish text atomically, replacing only the named mutable artifact."""
        path.parent.mkdir(parents=True, exist_ok=True)
        tmp = path.with_name(f".{path.name}.{os.getpid()}.{secrets.token_hex(4)}.tmp")
        try:
            with tmp.open("x") as fh:
                fh.write(text)
                fh.flush()
                os.fsync(fh.fileno())
            os.replace(tmp, path)
        finally:
            with contextlib.suppress(OSError):
                tmp.unlink(missing_ok=True)

    @staticmethod
    def _atomic_publish_text_no_replace(path: Path, text: str) -> None:
        """Atomically publish complete text, failing if the path exists."""
        path.parent.mkdir(parents=True, exist_ok=True)
        tmp = path.with_name(f".{path.name}.{os.getpid()}.{secrets.token_hex(4)}.tmp")
        try:
            with tmp.open("x") as fh:
                fh.write(text)
                fh.flush()
                os.fsync(fh.fileno())
            # A same-directory hard-link is an atomic, non-overwriting publish:
            # readers see either no destination or the complete fsynced file.
            os.link(tmp, path)
        finally:
            with contextlib.suppress(OSError):
                tmp.unlink(missing_ok=True)

    @staticmethod
    def _publish_deferred_no_replace(path: Path, text: str) -> None:
        """Atomically publish a complete deferred request without overwriting."""
        Pipeline._atomic_publish_text_no_replace(path, text)

    def repair_defer_intent_path(self) -> Path:
        root = self.run_dir if self.run_dir else Path(_logical_cwd()) / ".specula-output"
        return root / ".repair-defer-intent.json"

    def _persist_defer_intent(self, moves: list[tuple[str, Path, Path]]) -> None:
        if self.dry_run or not moves:
            return
        targets: dict[str, dict[str, str]] = {}
        for name, source, _destination in moves:
            targets.setdefault(name, {})[source.name] = source.read_text()
        payload = json.dumps({"version": 1, "targets": targets}, ensure_ascii=False, sort_keys=True) + "\n"
        marker = self.repair_defer_intent_path()
        try:
            self._publish_deferred_no_replace(marker, payload)
        except FileExistsError:
            log(f"ERROR: durable defer intent already exists: {marker}")
            raise SystemExit(1) from None

    def _load_defer_intent(self) -> dict[str, dict[str, str]] | None:
        marker = self.repair_defer_intent_path()
        if not marker.is_file():
            return None
        try:
            doc = json.loads(marker.read_text())
            targets = doc.get("targets") if isinstance(doc, dict) and doc.get("version") == 1 else None
            if not isinstance(targets, dict) or not targets:
                raise ValueError("targets must be a non-empty object")
            known = set(self.extract_names())
            result: dict[str, dict[str, str]] = {}
            for name, requests in targets.items():
                if name not in known or not isinstance(requests, dict) or not requests:
                    raise ValueError(f"invalid target entry {name!r}")
                parsed: dict[str, str] = {}
                for filename, text in requests.items():
                    if not isinstance(filename, str) or re.fullmatch(r"RR-\d+\.md", filename) is None:
                        raise ValueError(f"unsafe request filename {filename!r}")
                    if not isinstance(text, str) or not self._repair_request_is_executable(text, Path(filename).stem):
                        raise ValueError(f"malformed request intent {name}/{filename}")
                    if self._repair_request_field(text, "status") != "OPEN":
                        raise ValueError(f"intent request {name}/{filename} is not OPEN")
                    parsed[filename] = text
                result[name] = parsed
        except (OSError, ValueError) as exc:
            log(f"ERROR: invalid durable defer intent: {marker} ({exc})")
            raise SystemExit(1) from exc
        return result

    def _complete_defer_intent(self) -> int:
        """Idempotently finish every move named by the durable cap intent."""
        targets = self._load_defer_intent()
        if targets is None:
            return 0
        completed = 0
        note = "deferred (orchestrator): repair loop round cap reached"
        for name, requests in targets.items():
            rr_dir = Path(self.repair_dir(name))
            deferred_dir = rr_dir / "deferred"
            for filename, source_text in requests.items():
                source = rr_dir / filename
                destination = deferred_dir / filename
                expected = self._repair_request_text_with_status(source_text, "DEFERRED", note)
                source_exists = source.is_file()
                destination_exists = destination.is_file()
                if source_exists and source.read_text() != source_text:
                    log(f"ERROR: active request diverged from durable defer intent: {source}")
                    raise SystemExit(1)
                if destination_exists and destination.read_text() != expected:
                    log(f"ERROR: deferred request diverged from durable defer intent: {destination}")
                    raise SystemExit(1)
                if not source_exists and not destination_exists:
                    log(f"ERROR: defer intent lost both source and destination: {name}/{filename}")
                    raise SystemExit(1)
                if not destination_exists:
                    self._publish_deferred_no_replace(destination, expected)
                if source_exists:
                    source.unlink()
                completed += 1
                log(f"  deferred {filename} -> {destination.parent} (repair loop exhausted)")
        self.repair_defer_intent_path().unlink()
        return completed

    def _reconcile_interrupted_deferred_moves(self) -> None:
        """Finish the publish-then-unlink crash window for deferred requests.

        A SIGKILL after the complete deferred file is published but before the
        active OPEN source is unlinked leaves both names present. Only collapse
        the pair when the deferred bytes are exactly the canonical transform of
        the active bytes; divergent pairs remain a real conflict.
        """
        note = "deferred (orchestrator): repair loop round cap reached"
        for n in self.extract_names():
            active = {f.name: f for f in self._rr_files(n)}
            deferred = {f.name: f for f in self._deferred_rr_files(n)}
            for name in sorted(active.keys() & deferred.keys()):
                source = active[name]
                destination = deferred[name]
                try:
                    expected = self._repair_request_text_with_status(source.read_text(), "DEFERRED", note)
                    actual = destination.read_text()
                except OSError:
                    continue
                if rr_status(source) != "OPEN" or rr_status(destination) != "DEFERRED" or actual != expected:
                    continue
                source.unlink()
                log(f"  completed interrupted defer move for {n}: {name}")

    def _assert_no_active_deferred_conflicts(self) -> None:
        conflicts: list[tuple[str, Path, Path]] = []
        for n in self.extract_names():
            active = {f.name: f for f in self._rr_files(n)}
            deferred = {f.name: f for f in self._deferred_rr_files(n)}
            conflicts.extend((n, active[name], deferred[name]) for name in sorted(active.keys() & deferred.keys()))
        if conflicts:
            detail = ", ".join(f"{n}: {active} conflicts with {deferred}" for n, active, deferred in conflicts)
            log(f"ERROR: active/deferred repair request name conflict; refusing to overwrite: {detail}")
            raise SystemExit(1)

    @staticmethod
    def _reconcile_disposition_counts(text: str) -> str:
        """Make the disposition summary agree with the report's status table."""
        statuses: list[str] = []
        in_table = False
        for line in text.splitlines():
            cells = line.split("|")
            if len(cells) >= 5 and cells[1].strip() == "Bug" and cells[3].strip() == "Status":
                in_table = True
                continue
            if not in_table:
                continue
            if not line.lstrip().startswith("|"):
                break
            if len(cells) >= 5 and cells[1].strip().isdigit():
                statuses.append(cells[3].strip())
        if not statuses:
            return text
        pending = sum(status.startswith("PENDING REPAIR") for status in statuses)
        deferred = sum(status.startswith("DEFERRED") for status in statuses)
        pattern = re.compile(
            r"(?m)^(Dispositions: .*? \+ )\d+ pending-repair"
            r"( \+ \d+ incomplete)?(?: \+ \d+ deferred)?\s*$"
        )
        return pattern.sub(
            lambda match: f"{match.group(1)}{pending} pending-repair{match.group(2) or ''} + {deferred} deferred",
            text,
            count=1,
        )

    def reconcile_deferred_state(self) -> None:
        """Idempotently finish interrupted defer publication.

        The deferred directory is authoritative. Legacy files can still say
        OPEN, and a prior report write may have failed after the source was
        moved; normalize both before the repair loop makes any decision.
        """
        if self.dry_run:
            return
        self._complete_defer_intent()
        self._reconcile_interrupted_deferred_moves()
        self._assert_no_active_deferred_conflicts()
        for n in self.extract_names():
            deferred = self._deferred_rr_files(n)
            for f in deferred:
                if rr_status(f) != "DEFERRED":
                    text = self._repair_request_text_with_status(
                        f.read_text(),
                        "DEFERRED",
                        "reconciled (orchestrator): deferred directory is authoritative",
                    )
                    self._atomic_replace_text(f, text)
                    log(f"  reconciled legacy deferred status: {f}")

            report = Path(self.get_work_dir(n)) / "spec" / "confirmed-bugs.md"
            if not report.is_file():
                continue
            old_text = report.read_text()
            new_text = old_text
            for f in deferred:
                rid = rr_field(f, "id") or f.stem
                new_text = new_text.replace(
                    f"PENDING REPAIR ({rid})",
                    f"DEFERRED (repair loop exhausted; {rid} in deferred/)",
                )
            new_text = self._reconcile_disposition_counts(new_text)
            if new_text != old_text:
                self._atomic_replace_text(report, new_text)
                log(f"  reconciled deferred statuses in {report}")

    def regenerate_ledger(self) -> None:
        """Regenerate the human-readable rollup index per target.

        Deferred requests remain part of the audit trail, so the ledger is
        rebuilt from both the active queue and deferred/.  Conversely, when no
        request exists in either place, remove an old ledger rather than leave
        a stale snapshot behind.
        """
        if self.dry_run:
            return
        for n in self.extract_names():
            active = self._rr_files(n)
            deferred = self._deferred_rr_files(n)
            ledger = Path(self.get_work_dir(n)) / "spec" / "repair-ledger.md"
            files = [(f, False) for f in active] + [(f, True) for f in deferred]
            if not files:
                ledger.unlink(missing_ok=True)
                continue
            rows = [
                f"# Repair Ledger — {n}",
                "",
                f"Updated: {_date_iseconds()}",
                "",
                "| Request | Bug | Target | Status | Round |",
                "|---------|-----|--------|--------|-------|",
            ]
            for f, is_deferred in files:
                bug = rr_field(f, "bug_id").replace("|", "\\|")
                target = rr_field(f, "target").replace("|", "\\|")
                # Legacy versions moved an OPEN file into deferred/ without
                # changing its frontmatter.  Location is authoritative for
                # those historical files; new moves also stamp DEFERRED.
                status = "DEFERRED" if is_deferred else rr_status(f)
                rows.append(f"| {rr_field(f, 'id')} | {bug} | {target} | {status} | {rr_field(f, 'round')} |")
            ledger.write_text("\n".join(rows) + "\n")

    def prepare_repair_state(self) -> set[str]:
        """Reconcile startup state and return exactly recovered commit targets."""
        self.reconcile_deferred_state()
        recovered_commits = self.recover_interrupted_phase3()
        self.reset_stale_in_repair()
        self.regenerate_ledger()
        return recovered_commits

    def advance_confirmation_generation(self, repair_round: int, names: list[str] | None = None) -> None:
        """Atomically advance the Phase-4 cache generation for selected targets.

        This marker is written after every successful Phase 3, both normal and
        repair runs, and before the corresponding Phase 4. Confirmation cache
        fingerprints include its contents, so a resumed validation or repair
        can never reuse a verdict or candidate set from an earlier generation.
        For repair Phase 3, it also commits the durable snapshot's unique token;
        that token proves success if the process dies before snapshot cleanup.
        """
        if self.dry_run:
            return
        for n in names if names is not None else self.extract_names():
            marker = Path(self.get_work_dir(n)) / "spec" / "confirmation-generation.json"
            repair_commit: str | None = None
            if repair_round > 0:
                loaded = self.load_open_repair_snapshot(n)
                if loaded is not None:
                    _snapshot, snapshot_round, commit_token = loaded
                    if snapshot_round == repair_round:
                        repair_commit = commit_token
            previous = 0
            if marker.is_file():
                try:
                    doc = json.loads(marker.read_text())
                    value = doc.get("generation") if isinstance(doc, dict) else None
                    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
                        raise ValueError("generation is not a non-negative integer")
                    previous = value
                except (OSError, ValueError) as exc:
                    # A damaged legacy marker must not block a completed repair
                    # from reaching Phase 4. Replacing it changes the cache key,
                    # and subsequent generations continue monotonically from 1.
                    log(f"  WARNING: replacing invalid confirmation generation marker for {n}: {exc}")
            marker.parent.mkdir(parents=True, exist_ok=True)
            payload = {
                "generation": previous + 1,
                "repair_round": repair_round,
                "updated_at": _date_iseconds(),
            }
            if repair_commit is not None:
                payload["repair_phase3_commit"] = repair_commit
            self._atomic_replace_text(marker, json.dumps(payload, indent=2, sort_keys=True) + "\n")

    # ── phase runners ──
    def _model_effort_args(self) -> list[str]:
        """Explicit pipeline tuning flags, preserving an explicit empty value.

        An absent flag stays absent so phase launchers can apply their run-wide
        SPECULA_* fallback and adapter-specific defaults.  An explicit empty
        flag must be forwarded to override (and clear) those fallbacks.
        """
        args: list[str] = []
        if self.model is not None:
            args.append(f"--model={self.model}")
        if self.effort is not None:
            args.append(f"--effort={self.effort}")
        return args

    def _max_parallel_summary(self) -> str:
        if self.max_parallel is not None:
            return self.max_parallel
        confirmation_default = (
            "legacy confirmation 1 at a time" if self.confirm_legacy else "per-finding confirmation 4 at a time"
        )
        return f"phase defaults (ordinary phases 1 at a time; {confirmation_default})"

    def _phase_args(self, positional: list[str], pre: list[str] | None = None, with_artifact: bool = True) -> list[str]:
        args = list(pre or [])
        if self.max_parallel is not None:
            args.append(f"--max-parallel={self.max_parallel}")
        args += [
            f"--max-turns={self.max_turns}",
            f"--policy-retries={self.policy_retries}",
            f"--agent={self.agent}",
            f"--claude-alias={self.claude_alias}",
            *self._model_effort_args(),
        ]
        if with_artifact and self._artifact_given:
            args.append(f"--artifact={self.artifact}")
        args += positional
        return args

    def _run_launcher(self, script: str, args: list[str]) -> None:
        env = os.environ.copy()
        env.update(
            {
                "SPECULA_RATE_LIMIT_REACTIVE": "1",
                "SPECULA_RATE_LIMIT_RETRIES": str(RATE_LIMIT_RETRIES),
                "SPECULA_QUOTA_5H": self.quota_5h,
                "SPECULA_QUOTA_7D": self.quota_7d,
                "SPECULA_QUOTA_MAX_WAITS": self.quota_max_waits,
                "SPECULA_CLAUDE_ALIAS": self.claude_alias,
            }
        )
        if self.tlc_memory_limit is not None:
            env[MEMORY_LIMIT_ENV] = self.tlc_memory_limit
        if self.tlc_worker_limit is not None:
            env[WORKER_LIMIT_ENV] = self.tlc_worker_limit
        if self.tlc_scope:
            env[SCOPE_ENV] = self.tlc_scope

        proc: subprocess.Popen[bytes] | None = None
        received: list[tuple[int, float]] = []

        def forward(signum: int, _frame: Any) -> None:
            received.append((signum, time.monotonic()))
            if proc is not None:
                with contextlib.suppress(ProcessLookupError):
                    os.killpg(proc.pid, signum)

        installed: list[tuple[int, Any]] = []
        for name in ("SIGINT", "SIGTERM", "SIGHUP"):
            signum = getattr(signal, name, None)
            if signum is None:  # pragma: no cover - non-POSIX
                continue
            with contextlib.suppress(ValueError, OSError):
                installed.append((signum, signal.signal(signum, forward)))
        forwarded_exit: int | None = None
        try:
            proc = subprocess.Popen(
                ["bash", str(LAUNCH_DIR / script), *args],
                env=env,
                start_new_session=True,
            )
            if received:
                with contextlib.suppress(ProcessLookupError):
                    os.killpg(proc.pid, received[-1][0])
            while True:
                try:
                    returncode = proc.wait(timeout=0.1)
                    break
                except subprocess.TimeoutExpired:
                    if received and time.monotonic() >= received[0][1] + PHASE_TERMINATION_GRACE_SECONDS:
                        with contextlib.suppress(ProcessLookupError):
                            os.killpg(proc.pid, signal.SIGKILL)
                        returncode = proc.wait()
                        break
            if received:
                deadline = received[0][1] + PHASE_TERMINATION_GRACE_SECONDS
                while time.monotonic() < deadline:
                    try:
                        os.killpg(proc.pid, 0)
                    except ProcessLookupError:
                        break
                    time.sleep(0.05)
                else:
                    with contextlib.suppress(ProcessLookupError):
                        os.killpg(proc.pid, signal.SIGKILL)
                forwarded_exit = 128 + received[0][0]
        finally:
            for signum, previous in installed:
                with contextlib.suppress(ValueError, OSError):
                    signal.signal(signum, previous)

        if forwarded_exit is not None:
            raise SystemExit(forwarded_exit)
        if returncode == 0:
            return
        # Target-local rate-limit retry belongs to phaselib. Re-running this
        # launcher would also re-run successful targets and can starve later
        # targets forever when each quota window only covers a batch prefix.
        code = 128 - returncode if returncode < 0 else returncode
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
        args = [
            phase,
            f"--agent={self.agent}",
            f"--claude-alias={self.claude_alias}",
            f"--policy-retries={self.policy_retries}",
            *self._model_effort_args(),
            *names,
        ]
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
        self.advance_confirmation_generation(0)

    def run_phase4_confirmation(self) -> None:
        pre: list[str] = []
        if self.confirm_legacy:
            pre.append("--legacy-confirm")
        if self.confirm_debate:
            pre.append("--debate")
        mode = "single-agent, legacy" if self.confirm_legacy else "parallel per-finding"
        debate = " + debate" if self.confirm_debate and not self.confirm_legacy else ""
        self._phase(
            f"PHASE 4: BUG CONFIRMATION ({mode}{debate})",
            "launch_bug_confirmation.sh",
            # Confirmation distinguishes an omitted generic default from an
            # explicit --max-parallel=1: omitted fans findings out to four,
            # while explicit 1 deliberately runs them serially. Other phases
            # still receive Pipeline's implicit default of one.
            self._phase_args(self.extract_names(), pre=pre or None),
        )

    def run_phase3_repair(self, round_: int, names: list[str] | None = None) -> None:
        """Phase 3 in repair mode: consume OPEN repair requests, repair the spec,
        re-run MC, and mark each repaired request CONSUMED. Whether the repair
        settled the finding is answered by the next Phase 4 pass — a repaired
        artifact no longer appears in the fresh output; a surviving or new
        violation is confirmed fresh. There is no separate re-check pass."""
        selected = names if names is not None else self.extract_names()
        self._phase(
            f"REPAIR ROUND {round_}: PHASE 3 (scoped spec/fault/invariant repair)",
            "launch_spec_validation.sh",
            self._phase_args(selected, pre=["--repair"]),
        )
        self.advance_confirmation_generation(round_, selected)

    def run_phase4b_classification(self) -> None:
        self._phase(
            "PHASE 4b: BUG CLASSIFICATION (severity tier assignment)",
            "launch_bug_classification.sh",
            self._phase_args(self.extract_names(), with_artifact=False),
        )

    def run_repair_loop(self, prepared_commits: set[str] | None = None) -> set[str]:
        """Confirmation back-edge: repeat {Phase 3 repairs the spec per OPEN
        repair requests and re-runs MC; Phase 4 confirms the fresh output
        normally} until no open request remains or the global round cap is hit. A
        repaired artifact simply no longer appears in the next Phase 4 output; a
        surviving or new violation is confirmed fresh. There is no re-check pass
        and no per-finding DEFERRED verdict — when the cap is reached the
        orchestrator (not an agent) files any still-open request under
        repair-requests/deferred/. Budget pressure -> wait_for_quota (WAIT), never
        a mass-defer.

        A caller that already ran startup reconciliation passes its exact
        committed-target set. A direct caller leaves it unset; this method then
        reconciles and consumes any recovered commit with its pending fresh
        Phase 4. The returned set is exactly the targets covered by a recovered
        or newly successful repair Phase 3 during this invocation.
        """
        divider()
        # parse_args validates normal CLI/environment input.  Keep this guard
        # for embedders and tests that configure Pipeline directly.
        if not re.fullmatch(r"[0-9]+", self.max_repair_rounds):
            log(f"ERROR: repair loop cap must be a non-negative integer; got '{self.max_repair_rounds}'")
            raise SystemExit(1)
        cap = int(self.max_repair_rounds)
        cap_disp = "unlimited" if cap == 0 else f"{cap} rounds"
        log(f"REPAIR LOOP (confirmation back-edge) — cap={cap_disp}")
        divider()

        recovered_commits = self.prepare_repair_state() if prepared_commits is None else set(prepared_commits)
        phase3_targets = set(recovered_commits)
        if not self.has_open_repair_requests():
            if recovered_commits:
                self.wait_for_quota()
                self.run_phase4_confirmation()
                self.regenerate_ledger()
                names = ", ".join(sorted(recovered_commits))
                log(f"Recovered committed repair Phase 3 for {names}; completed its pending fresh Phase 4.")
                if self.has_open_repair_requests():
                    log("Fresh Phase 4 opened repair requests; continuing the repair loop.")
                else:
                    return phase3_targets
            else:
                log("No OPEN repair requests — repair loop is a no-op.")
                return phase3_targets

        round_ = 0
        while self.has_open_repair_requests():
            if cap != 0 and round_ >= cap:
                deferred = self.move_open_requests_to_deferred()
                self.regenerate_ledger()
                log(f"Repair loop reached its {cap}-round cap; deferred {deferred} still-OPEN request(s).")
                return phase3_targets

            round_ += 1
            sig_before = self.repair_state_sig()
            repaired_names: list[str] = []
            for name in self.names_with_open_repair_requests():
                try:
                    self.wait_for_quota()  # budget pressure -> WAIT, never auto-defer
                except BaseException as exc:
                    detail = f"exit {exc.code}" if isinstance(exc, SystemExit) else f"{type(exc).__name__}: {exc}"
                    log(
                        f"ERROR: repair loop stopped in round {round_} for {name} before Phase 3 ({detail}); "
                        "repair requests were left unchanged."
                    )
                    raise
                open_before = self.snapshot_open_repair_requests(name)
                if not open_before:
                    states = ", ".join(f"{f.name}={rr_status(f) or '<missing>'}" for f in self._rr_files(name))
                    log(f"ERROR: {name} has no repairable OPEN request ({states}); refusing Phase 3.")
                    raise SystemExit(1)
                self.persist_open_repair_snapshot(name, open_before, round_)
                try:
                    self.run_phase3_repair(round_, [name])  # OPEN -> CONSUMED, repair spec, re-run MC
                    if not self.dry_run:
                        unfinished = [f for f in open_before if rr_status(f) != "CONSUMED"]
                        if unfinished:
                            detail = ", ".join(f"{f.name}={rr_status(f) or '<missing>'}" for f in unfinished)
                            raise RuntimeError(f"Phase 3 returned success without consuming {detail}")
                except BaseException as exc:
                    self.restore_open_repair_requests(open_before, round_)
                    try:
                        self.clear_open_repair_snapshot(name)
                    except OSError as cleanup_exc:
                        log(f"ERROR: could not clear durable Phase 3 snapshot for {name}: {cleanup_exc}")
                    self.reset_stale_in_repair(name)
                    self.regenerate_ledger()
                    detail = f"exit {exc.code}" if isinstance(exc, SystemExit) else f"{type(exc).__name__}: {exc}"
                    log(
                        f"ERROR: repair loop failed in round {round_} for {name} during Phase 3 ({detail}); "
                        "only that target was reset OPEN, with partial artifacts/history retained."
                    )
                    raise
                try:
                    self.clear_open_repair_snapshot(name)
                except OSError as cleanup_exc:
                    # Phase 3 already crossed its tokenized durable commit
                    # point. Never turn cleanup failure into repair failure:
                    # retain CONSUMED + snapshot so startup can finalize the
                    # exact commit and continue with fresh Phase 4.
                    self.regenerate_ledger()
                    log(
                        f"ERROR: committed repair Phase 3 for {name}, but could not clear its durable snapshot "
                        f"({cleanup_exc}); CONSUMED state was retained for startup recovery."
                    )
                    raise
                repaired_names.append(name)
                phase3_targets.add(name)

            try:
                self.wait_for_quota()
                self.run_phase4_confirmation()  # normal Phase 4 on the fresh bug-report
            except BaseException as exc:
                self.regenerate_ledger()
                detail = f"exit {exc.code}" if isinstance(exc, SystemExit) else type(exc).__name__
                names = ", ".join(repaired_names) or "none"
                log(
                    f"ERROR: repair loop failed in round {round_} during Phase 4 ({detail}); "
                    f"successful Phase 3 request states were retained for: {names}. "
                    "Rerun the pipeline; startup recovery will retry Phase 4 safely."
                )
                raise
            self.snapshot_confirmed_bugs(round_)
            self.regenerate_ledger()
            if self.repair_state_sig() == sig_before:
                if self.dry_run:
                    log(f"[DRY RUN] Repair state is unchanged after simulated round {round_}; leaving requests OPEN.")
                    return phase3_targets
                log(
                    f"ERROR: repair loop made no progress in round {round_} (no request changed); "
                    "OPEN requests were retained for retry."
                )
                raise SystemExit(1)

        self.regenerate_ledger()
        log(f"Repair loop resolved all requests after {round_} round(s).")
        return phase3_targets

    def snapshot_confirmed_bugs(self, round_: int) -> None:
        """Preserve each round's result: copy `confirmed-bugs.md` to
        `confirmed-bugs-round-N.md`. The latest also stays as `confirmed-bugs.md`
        for downstream Phase 4b."""
        if self.dry_run:
            return
        for n in self.extract_names():
            cb = Path(self.get_work_dir(n)) / "spec" / "confirmed-bugs.md"
            if cb.is_file():
                (cb.parent / f"confirmed-bugs-round-{round_}.md").write_text(cb.read_text())

    def move_open_requests_to_deferred(self) -> int:
        """File legal OPEN requests under deferred/ after the cap is reached.

        The move is deliberately strict: CONSUMED requests stay in the active
        audit trail, while IN_REPAIR/malformed/unknown states are an execution
        error rather than exhaustion.  Existing destinations are rejected so a
        reused RR id can never overwrite historical evidence.
        """
        if self.dry_run:
            return 0

        self._assert_no_active_deferred_conflicts()

        moves: list[tuple[str, Path, Path]] = []
        invalid: list[tuple[Path, str]] = []
        for n in self.extract_names():
            dd = Path(self.repair_dir(n)) / "deferred"
            for f in self._rr_files(n):
                status = rr_status(f)
                if status == "OPEN":
                    moves.append((n, f, dd / f.name))
                elif status != "CONSUMED":
                    invalid.append((f, status))

        if invalid:
            detail = ", ".join(f"{f.name}={status or '<missing>'}" for f, status in invalid)
            log(f"ERROR: refusing to defer repair requests in non-OPEN states: {detail}")
            raise SystemExit(1)

        self._persist_defer_intent(moves)
        moved = self._complete_defer_intent()
        if moved != len(moves):
            raise RuntimeError(f"durable defer intent completed {moved} requests; expected {len(moves)}")

        # Statuses are already complete in each published destination. This
        # final reconciliation updates reports; if it fails, the next repair
        # loop startup repeats it idempotently from the authoritative directory.
        self.reconcile_deferred_state()
        return moved

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
            deferred_files = self._deferred_rr_files(name)
            rr_deferred = len(deferred_files)
            if rr_files or rr_deferred:
                rr_consumed = self._status_file_count(rr_files, "CONSUMED")
                rr_open = self._status_file_count(rr_files, "OPEN")
                rr_in_repair = self._status_file_count(rr_files, "IN_REPAIR")
                rr_invalid = len(rr_files) - rr_consumed - rr_open - rr_in_repair
                line = (
                    f"- **Repair loop**: {len(rr_files) + rr_deferred} request(s) — "
                    f"{rr_consumed} repaired, {rr_deferred} deferred, {rr_open} open"
                )
                if rr_in_repair:
                    line += f", {rr_in_repair} in repair"
                if rr_invalid:
                    line += f", {rr_invalid} invalid"
                out.append(line)

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
        there) and a botched CONSUMEDX counted as CONSUMED."""
        return sum(1 for f in files if rr_status(f) == status)

    # ── main (runs inside the tee) ──
    def main(self) -> int:
        print("╔══════════════════════════════════════════════════════════╗")
        print("║        Specula — Full Pipeline Runner                   ║")
        print("╚══════════════════════════════════════════════════════════╝")
        print()
        print(f"Targets:      {len(self.targets)}")
        print(f"Max parallel: {self._max_parallel_summary()}")
        print(f"Max turns:    {self.max_turns}")
        print(f"Policy retries: {self.policy_retries}")
        print(f"Agent:        {self.agent}  (claude-alias={self.claude_alias})")
        memory_limit = self.tlc_memory_limit or os.environ.get(MEMORY_LIMIT_ENV) or "auto (80% available)"
        worker_limit = self.tlc_worker_limit or os.environ.get(WORKER_LIMIT_ENV) or "unbounded (report only)"
        print(f"TLC memory:   {memory_limit}")
        print(f"TLC workers:  {worker_limit}")
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
        print(f"Repair loop:  skip={_b(self.skip_repair_loop)} global_cap={cap}")
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

        # Recover before Phase 1/2/2.5 can mutate the artifacts that the
        # snapshot token commits. Skip flags control later work, never whether
        # durable crash state is reconciled.
        recovered_phase3_commits = self.prepare_repair_state()
        upstream_all_skipped = self.skip_analysis and self.skip_specgen and self.skip_harness

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

        # An uncommitted snapshot is OPEN again after reconciliation. Resume it
        # when both halves of the repair loop are enabled. The resumed loop
        # itself performs repair Phase 3 and fresh Phase 4.
        resumed_repair = False
        phase3_targets = set(recovered_phase3_commits)
        if not self.skip_confirmation and not self.skip_repair_loop and self.has_open_repair_requests():
            log("Resuming pending repair requests before the ordinary Phase 3 pass")
            phase3_targets = self.run_repair_loop(prepared_commits=recovered_phase3_commits)
            resumed_repair = True

        current_targets = set(names)
        phase3_covered = (
            bool(current_targets)
            and upstream_all_skipped
            and phase3_targets == current_targets
            and not self.has_open_repair_requests()
        )
        normal_phase3_ran = False
        if not self.skip_validation and not phase3_covered:
            self.wait_for_quota()
            self.run_phase3_validation()
            self.run_review("validation", names)
            normal_phase3_ran = True
        elif phase3_covered:
            source = "resumed repair loop" if resumed_repair else "recovered committed repairs"
            log(f"Ordinary Phase 3 covered for every target by the {source}")
        else:
            log("Skipping Phase 3 (--skip-validation)")

        phase4_covered = resumed_repair and not normal_phase3_ran
        fresh_phase4_ran = False
        if not self.skip_confirmation and not phase4_covered:
            self.wait_for_quota()
            self.run_phase4_confirmation()
            fresh_phase4_ran = True
        elif self.skip_confirmation:
            log("Skipping Phase 4a (--skip-confirmation)")
        else:
            log("Initial Phase 4 completed by the resumed repair loop")

        if fresh_phase4_ran and not self.skip_repair_loop:
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
