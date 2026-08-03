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
import fcntl
import json
import locale
import math
import os
import re
import secrets
import signal
import stat
import subprocess
import sys
import time
import traceback
from collections.abc import Callable, Iterator
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
from specula import resumelib
from specula.agent_config import AgentConfigError, AgentRouting, AgentSelection, load_agent_routing
from specula.output_index import (
    INDEX_FILENAME,
    PIPELINE_LOG_ENV,
    TargetOutput,
    is_safe_target_name,
    write_run_index,
    write_target_index,
)
from specula.phaselib import (
    DEFAULT_POLICY_RETRIES,
    DEFAULT_TRANSIENT_RESUMES,
    Workspace,
    _logical_cwd,
    _normalize_artifact_dir,
    _parse_policy_retries,
    _parse_transient_resumes,
    _wc_l,
)
from specula.resource_summary import ResourceSummaryTracker
from specula.snapshotlib import (
    SNAPSHOT_MODE_ENV,
    SOURCE_MAP,
    SnapshotError,
    capture_changes,
    clean_git_environment,
    load_sources,
    prepare_sources,
    sanitize_snapshot_git_environment,
    validate_snapshot_destinations,
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
  --skip-validate        Skip validation
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
  --transient-resumes=N  Transient provider/transport session resumes after the initial attempt (default: 20; 0 disables)
  --agent=NAME           Agent adapter to use (default: claude-code; e.g., claude-code, codex, copilot-cli, opencode, pi)
  --agent-config=PATH    JSON file selecting an agent/model profile per phase
  --claude-alias=NAME    Claude CLI profile (default: claude)
  --model=NAME           Model forwarded to every agent adapter
  --effort=LEVEL         Reasoning effort forwarded to every agent adapter
  --artifact=PATH        Path to system artifact/source code
  --keep-original        Work in a full private copy and write changes.patch
  --tlc-memory-limit=SIZE
                         Aggregate -m + -M budget for TLCs in this run (default: auto,
                         80% of effective available memory at the first TLC start)
  --tlc-worker-limit=N   Optional aggregate TLC worker bound (default: unset; report only)
  --isolate              Isolated workspace (the default): all outputs go to
                         runs/<run-id>/ — parallel-safe, keeps case-studies/
                         pristine. Sources are read from case-studies/<name>/artifact
                         or --artifact unless --keep-original copies them.
  --no-isolate           Legacy layout: outputs under $PWD/.specula-output
                         (a single target cd's into case-studies/<name>/ when
                         it exists)
  --run-id=ID            Attach to runs/ID — reuse an existing run's workspace,
                         resume unfinished agent conversations at their phase
                         (implies --isolate)
  --fresh-context        With --run-id, abandon unfinished conversations and
                         start the selected phases with fresh agent context

Output navigation (default isolated layout):
  runs/<run-id>/
    ├── index.md                    # Choose a target
    ├── pipeline-summary.md         # Final run summary, when available
    ├── pipeline.log                # Full pipeline log
    └── <name>/
        └── .specula-output/
            ├── index.md            # Human-readable results guide
            └── ...                 # Existing phase artifacts

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
        self._max_parallel_given = False
        self._max_turns_given = False
        self.policy_retries = DEFAULT_POLICY_RETRIES
        self.transient_resumes = DEFAULT_TRANSIENT_RESUMES
        self._policy_retries_given = False
        self._transient_resumes_given = False
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
        self._confirm_legacy_given = False
        self._confirm_debate_given = False
        # `or`: bash ${VAR:-default} treats an exported-but-empty var as unset
        self.max_repair_rounds = os.environ.get("MAX_REPAIR_ROUNDS") or "10"
        self._max_repair_rounds_given = False
        self.skip_reviews = True
        self._enable_reviews_given = False
        self.agent = "claude-code"
        self._agent_given = False
        self.agent_config_path: Path | None = None
        self.agent_routing: AgentRouting | None = None
        self.claude_alias = os.environ.get("CLAUDE_ALIAS") or "claude"
        self._claude_alias_given = False
        # None means no pipeline CLI override: phase launchers may consult
        # SPECULA_MODEL / SPECULA_EFFORT.  "" is an explicit empty flag and
        # must survive into the child so it can clear those environment values.
        self.model: str | None = None
        self.effort: str | None = None
        self._model_given = False
        self._effort_given = False
        self.artifact = ""
        self._artifact_given = False
        self.keep_original = False
        self._keep_original_given = False
        self._snapshot_sources: dict[str, Path] = {}
        self._snapshot_paths: list[Path] = []
        self.tlc_memory_limit: str | None = None
        self.tlc_worker_limit: str | None = None
        self.targets: list[str] = []
        self.quota_5h = os.environ.get("QUOTA_5H") or "85"
        self.quota_7d = os.environ.get("QUOTA_7D") or "95"
        self.quota_max_waits = os.environ.get("QUOTA_MAX_WAITS") or "6"
        self._targets_given = False
        # workspace isolation (step 4; default since step 7d) — run_dir stays
        # None only in legacy mode (--no-isolate)
        self.isolate = True
        self._isolate_explicit = False  # an isolation flag was given (vs the default)
        self._no_isolate_given = False
        self.run_id = ""
        self._run_id_given = False  # `--run-id=` (empty) must error, not mint a fresh id
        self.fresh_context = False
        self._attached_existing_run = False
        self._restored_routes: dict[str, AgentSelection] | None = None
        self._restored_default: AgentSelection | None = None
        self._manual_resume_phase: str | None = None
        self._manual_launch_cwd: Path | None = None
        self._run_lock_fd: int | None = None
        self.run_dir: Path | None = None
        self.pipeline_log_path: Path | None = None
        self.tlc_scope = ""
        self.argv: list[str] = []
        self.resource_summary: ResourceSummaryTracker | None = None
        self._resource_phase_key: str | None = None

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
            elif arg == "--skip-validate":
                self.skip_validation = True
            elif arg == "--skip-confirmation":
                self.skip_confirmation = True
            elif arg == "--skip-classification":
                self.skip_classification = True
            elif arg == "--skip-repair-loop":
                self.skip_repair_loop = True
            elif arg == "--legacy-confirm":
                self.confirm_legacy = True
                self._confirm_legacy_given = True
            elif arg == "--confirm-debate":
                self.confirm_debate = True
                self._confirm_debate_given = True
            elif arg.startswith("--max-repair-rounds="):
                self.max_repair_rounds = arg.split("=", 1)[1]
                self._max_repair_rounds_given = True
            elif arg == "--enable-reviews":
                self.skip_reviews = False
                self._enable_reviews_given = True
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
            elif arg == "--fresh-context":
                self.fresh_context = True
            elif arg.startswith("--max-parallel="):
                self.max_parallel = arg.split("=", 1)[1]
                self._max_parallel_given = True
            elif arg.startswith("--max-turns="):
                self.max_turns = arg.split("=", 1)[1]
                self._max_turns_given = True
            elif arg.startswith("--policy-retries="):
                self._policy_retries_given = True
                raw = arg.split("=", 1)[1]
                try:
                    self.policy_retries = _parse_policy_retries(raw)
                except ValueError:
                    print(
                        f"ERROR: --policy-retries must be a non-negative integer, got '{raw}'",
                        file=sys.stderr,
                    )
                    return 1
            elif arg.startswith("--transient-resumes="):
                self._transient_resumes_given = True
                raw = arg.split("=", 1)[1]
                try:
                    self.transient_resumes = _parse_transient_resumes(raw)
                except ValueError:
                    print(
                        f"ERROR: --transient-resumes must be a non-negative integer, got '{raw}'",
                        file=sys.stderr,
                    )
                    return 1
            elif arg.startswith("--agent="):
                self.agent = arg.split("=", 1)[1]
                self._agent_given = True
            elif arg.startswith("--agent-config="):
                raw_path = arg.split("=", 1)[1]
                if not raw_path:
                    print("ERROR: --agent-config requires a path", file=sys.stderr)
                    return 1
                try:
                    config_path = Path(raw_path).expanduser()
                    if not config_path.is_absolute():
                        config_path = _logical_cwd() / config_path
                    self.agent_config_path = config_path.resolve()
                except (OSError, RuntimeError) as exc:
                    print(f"ERROR: invalid --agent-config path '{raw_path}': {exc}", file=sys.stderr)
                    return 1
            elif arg.startswith("--claude-alias="):
                self.claude_alias = arg.split("=", 1)[1]
                self._claude_alias_given = True
            elif arg.startswith("--model="):
                self.model = arg.split("=", 1)[1]
                self._model_given = True
            elif arg.startswith("--effort="):
                self.effort = arg.split("=", 1)[1]
                self._effort_given = True
            elif arg.startswith("--artifact="):
                self.artifact = arg.split("=", 1)[1]
                self._artifact_given = True
            elif arg == "--keep-original":
                self.keep_original = True
                self._keep_original_given = True
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
        if self.agent_config_path is not None and (
            self._agent_given or self.model is not None or self.effort is not None
        ):
            print(
                "ERROR: --agent-config cannot be combined with --agent, --model, or --effort",
                file=sys.stderr,
            )
            return 1
        if self.agent_config_path is not None:
            try:
                self.agent_routing = load_agent_routing(self.agent_config_path)
            except (AgentConfigError, OSError) as exc:
                print(f"ERROR: {exc}", file=sys.stderr)
                return 1
        targets_given = bool(self.targets)
        if not self.targets:
            self.targets.append(_logical_cwd().name)  # bash `basename "$PWD"` (logical)
        self._targets_given = targets_given
        # order-independent: the two are contradictory however they arrive
        # (e.g. scheduler-injected --run-id + a --no-isolate from queue flags)
        if self._run_id_given and self._no_isolate_given:
            print("ERROR: --no-isolate conflicts with --run-id", file=sys.stderr)
            return 1
        if self.fresh_context and not self._run_id_given:
            print("ERROR: --fresh-context requires --run-id", file=sys.stderr)
            return 1
        if self.keep_original and not self.isolate:
            print("ERROR: --keep-original conflicts with --no-isolate", file=sys.stderr)
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
    def _resolve_snapshot_sources(self, fallback_artifact: str = "") -> dict[str, Path]:
        names = self.extract_names()
        if len(names) != len(self.targets) or len(set(names)) != len(names):
            raise SnapshotError("--keep-original requires one unique, non-empty target name per target")
        workspace = Workspace(
            self.targets,
            artifact=self.artifact or fallback_artifact,
            run_dir=self.run_dir,
        )
        sources: dict[str, Path] = {}
        for name in names:
            repo = workspace.find_original_repo_dir(name)
            if not repo:
                raise SnapshotError(f"cannot find source for {name!r}; pass --artifact=/path/to/source")
            source = Path(repo).resolve()
            if not source.is_dir():
                raise SnapshotError(f"source is not a directory: {source}")
            sources[name] = source
        return sources

    def _check_snapshot_overlap(self) -> None:
        assert self.run_dir is not None
        run_root = self.run_dir.resolve()
        for source in self._snapshot_sources.values():
            if run_root == source or run_root.is_relative_to(source) or source.is_relative_to(run_root):
                raise SnapshotError(f"run storage must be outside the source tree: {source}")

    @staticmethod
    def _route_specs() -> dict[str, tuple[str, str | None]]:
        return {
            "analyze": ("analyze", None),
            "specgen": ("specgen", None),
            "harness": ("harness", None),
            "validate": ("validate", None),
            "confirm": ("confirm", None),
            "repair": ("repair", "validate"),
            "classify": ("classify", None),
            "review:analysis": ("review", "analyze"),
            "review:specgen": ("review", "specgen"),
            "review:validation": ("review", "validate"),
        }

    def _resumable_selection(self, selection: AgentSelection) -> AgentSelection:
        """Freeze values known at run creation while preserving explicit resets."""
        resolved_model, resolved_effort = self._resolved_run_tuning(selection)
        return AgentSelection(
            agent=selection.agent,
            model=selection.model if selection.model is not None else resolved_model,
            effort=selection.effort if selection.effort is not None else resolved_effort,
        )

    @staticmethod
    def _selection_document(selection: AgentSelection) -> dict[str, str | None]:
        return {"agent": selection.agent, "model": selection.model, "effort": selection.effort}

    @staticmethod
    def _selection_from_document(value: object, label: str) -> AgentSelection:
        if not isinstance(value, dict):
            raise resumelib.ResumeError(f"invalid {label}: expected an object")
        agent = value.get("agent")
        model = value.get("model")
        effort = value.get("effort")
        if not isinstance(agent, str) or not agent:
            raise resumelib.ResumeError(f"invalid {label} agent")
        if model is not None and not isinstance(model, str):
            raise resumelib.ResumeError(f"invalid {label} model")
        if effort is not None and not isinstance(effort, str):
            raise resumelib.ResumeError(f"invalid {label} effort")
        return AgentSelection(agent=agent, model=model, effort=effort)

    def _resumable_routes(self) -> dict[str, AgentSelection] | None:
        if self.agent_routing is None and self._restored_routes is None:
            return None
        return {
            route: self._resumable_selection(self._agent_selection(phase, fallback=fallback))
            for route, (phase, fallback) in self._route_specs().items()
        }

    def _resume_configuration_document(self) -> dict[str, Any]:
        default = self._resumable_selection(self._agent_selection())
        routes = self._resumable_routes()
        return {
            "version": 1,
            "default": self._selection_document(default),
            "routes": (
                {name: self._selection_document(selection) for name, selection in routes.items()}
                if routes is not None
                else None
            ),
            "agent_config": str(self.agent_config_path) if self.agent_config_path is not None else None,
            "claude_alias": self.claude_alias,
            "policy_retries": self.policy_retries,
            "transient_resumes": self.transient_resumes,
            "max_parallel": self.max_parallel,
            "max_turns": self.max_turns,
            "confirm_legacy": self.confirm_legacy,
            "confirm_debate": self.confirm_debate,
            "max_repair_rounds": self.max_repair_rounds,
            "skip_reviews": self.skip_reviews,
            "targets": list(self.targets),
            "artifact": self.artifact,
        }

    def _restore_resume_configuration(self, raw: dict[str, Any], *, allow_overrides: bool = False) -> None:
        if raw.get("version") != 1:
            raise resumelib.ResumeError(
                "this run was created without manual conversation checkpoints; pass --fresh-context to continue"
            )
        stored_default = self._selection_from_document(raw.get("default"), "resume default")
        raw_routes = raw.get("routes")
        stored_routes: dict[str, AgentSelection] | None = None
        if raw_routes is not None:
            if not isinstance(raw_routes, dict) or set(raw_routes) != set(self._route_specs()):
                raise resumelib.ResumeError("invalid stored agent routes")
            stored_routes = {
                name: self._selection_from_document(value, f"stored route {name}") for name, value in raw_routes.items()
            }

        selection_overridden = (
            self.agent_config_path is not None or self._agent_given or self._model_given or self._effort_given
        )
        if allow_overrides:
            if stored_routes is not None and not selection_overridden:
                self._restored_routes = stored_routes
                self._restored_default = stored_default
                stored_path = raw.get("agent_config")
                if isinstance(stored_path, str):
                    self.agent_config_path = Path(stored_path)
            elif self.agent_config_path is None:
                if not self._agent_given:
                    self.agent = stored_default.agent
                if not self._agent_given and not self._model_given:
                    self.model = stored_default.model
                if not self._agent_given and not self._effort_given:
                    self.effort = stored_default.effort
        elif stored_routes is None:
            if self.agent_config_path is not None:
                raise resumelib.ResumeError(
                    "this run did not use --agent-config; pass --fresh-context to change agent routing"
                )
            if self._agent_given and self.agent != stored_default.agent:
                raise resumelib.ResumeError(
                    f"this run uses agent {stored_default.agent}; pass --fresh-context to use {self.agent}"
                )
            if self._model_given and self.model != stored_default.model:
                raise resumelib.ResumeError(
                    f"this run uses model {stored_default.model!r}; pass --fresh-context to change it"
                )
            if self._effort_given and self.effort != stored_default.effort:
                raise resumelib.ResumeError(
                    f"this run uses effort {stored_default.effort!r}; pass --fresh-context to change it"
                )
            self.agent = stored_default.agent
            self.model = stored_default.model
            self.effort = stored_default.effort
        else:
            if self._agent_given or self._model_given or self._effort_given:
                raise resumelib.ResumeError("this run uses phase agent routing; pass --fresh-context to override it")
            if self.agent_config_path is not None:
                current_routes = self._resumable_routes()
                if current_routes != stored_routes:
                    raise resumelib.ResumeError(
                        "--agent-config differs from this run; pass --fresh-context to change it"
                    )
            else:
                self._restored_routes = stored_routes
                self._restored_default = stored_default
                stored_path = raw.get("agent_config")
                if isinstance(stored_path, str):
                    self.agent_config_path = Path(stored_path)

        alias = raw.get("claude_alias")
        if not isinstance(alias, str):
            raise resumelib.ResumeError("invalid stored claude alias")
        if self._claude_alias_given:
            if not allow_overrides and self.claude_alias != alias:
                raise resumelib.ResumeError(
                    f"this run uses Claude profile {alias!r}; pass --fresh-context to change it"
                )
        else:
            self.claude_alias = alias

        confirmation_mode_overridden = self._confirm_legacy_given or self._confirm_debate_given
        for field, given, attr in (
            ("policy_retries", self._policy_retries_given, "policy_retries"),
            ("transient_resumes", self._transient_resumes_given, "transient_resumes"),
        ):
            value = raw.get(field)
            if not isinstance(value, int) or isinstance(value, bool) or value < 0:
                raise resumelib.ResumeError(f"invalid stored {field}")
            if given:
                if not allow_overrides and getattr(self, attr) != value:
                    raise resumelib.ResumeError(
                        f"this run uses {field.replace('_', ' ')} {value}; pass --fresh-context to change it"
                    )
            else:
                setattr(self, attr, value)

        stored_repair_rounds = raw.get("max_repair_rounds")
        if not isinstance(stored_repair_rounds, str) or re.fullmatch(r"[0-9]+", stored_repair_rounds) is None:
            raise resumelib.ResumeError("invalid stored max_repair_rounds")
        if self._max_repair_rounds_given:
            if not allow_overrides and self.max_repair_rounds != stored_repair_rounds:
                raise resumelib.ResumeError(
                    f"this run uses max repair rounds {stored_repair_rounds}; pass --fresh-context to change it"
                )
        else:
            self.max_repair_rounds = stored_repair_rounds

        stored_skip_reviews = raw.get("skip_reviews")
        if not isinstance(stored_skip_reviews, bool):
            raise resumelib.ResumeError("invalid stored skip_reviews")
        if self._enable_reviews_given:
            if not allow_overrides and self.skip_reviews != stored_skip_reviews:
                raise resumelib.ResumeError("this run uses a different review mode; pass --fresh-context to change it")
        else:
            self.skip_reviews = stored_skip_reviews

        stored_max_parallel = raw.get("max_parallel")
        if stored_max_parallel is not None and not isinstance(stored_max_parallel, str):
            raise resumelib.ResumeError("invalid stored max_parallel")
        if self._max_parallel_given:
            if not allow_overrides and self.max_parallel != stored_max_parallel:
                raise resumelib.ResumeError(
                    f"this run uses max parallel {stored_max_parallel!r}; pass --fresh-context to change it"
                )
        else:
            self.max_parallel = stored_max_parallel

        stored_max_turns = raw.get("max_turns")
        if not isinstance(stored_max_turns, str):
            raise resumelib.ResumeError("invalid stored max_turns")
        if self._max_turns_given:
            if not allow_overrides and self.max_turns != stored_max_turns:
                raise resumelib.ResumeError(
                    f"this run uses max turns {stored_max_turns!r}; pass --fresh-context to change it"
                )
        else:
            self.max_turns = stored_max_turns

        for field, given, attr in (
            ("confirm_legacy", self._confirm_legacy_given, "confirm_legacy"),
            ("confirm_debate", self._confirm_debate_given, "confirm_debate"),
        ):
            value = raw.get(field)
            if not isinstance(value, bool):
                raise resumelib.ResumeError(f"invalid stored {field}")
            if given:
                if not allow_overrides and getattr(self, attr) != value:
                    raise resumelib.ResumeError(
                        f"this run uses {field.replace('_', ' ')}={value}; pass --fresh-context to change it"
                    )
            elif not (allow_overrides and confirmation_mode_overridden):
                setattr(self, attr, value)
        if self.confirm_legacy and self.confirm_debate:
            raise resumelib.ResumeError("invalid stored confirmation mode")

        stored_targets = raw.get("targets")
        if (
            not isinstance(stored_targets, list)
            or not stored_targets
            or not all(isinstance(target, str) for target in stored_targets)
        ):
            raise resumelib.ResumeError("invalid stored targets")
        if self._targets_given:
            if not allow_overrides and self.targets != stored_targets:
                raise resumelib.ResumeError("targets differ from this run; pass --fresh-context to change them")
        else:
            self.targets = list(stored_targets)

        stored_artifact = raw.get("artifact")
        if not isinstance(stored_artifact, str):
            raise resumelib.ResumeError("invalid stored artifact")
        if self._artifact_given:
            if not allow_overrides and (
                not stored_artifact or Path(self.artifact).resolve() != Path(stored_artifact).resolve()
            ):
                raise resumelib.ResumeError(
                    "--artifact differs from this run; pass --fresh-context to use another source"
                )
        elif stored_artifact and not self.keep_original:
            artifact = _normalize_artifact_dir(stored_artifact)
            if artifact is None:
                raise resumelib.ResumeError(f"this run's artifact is unavailable: {stored_artifact}")
            self.artifact = artifact
            self._artifact_given = True

    def _position_at_manual_resume_phase(self, active: list[dict[str, Any]] | None = None) -> None:
        phase = self._manual_resume_phase
        if phase is None:
            return
        controlling_skip: tuple[str, str] | None = {
            "code_analysis": ("skip_analysis", "--skip-analysis"),
            "spec_generation": ("skip_specgen", "--skip-specgen"),
            "harness_generation": ("skip_harness", "--skip-harness"),
            "bug_confirmation": ("skip_confirmation", "--skip-confirmation"),
            "bug_classification": ("skip_classification", "--skip-classification"),
        }.get(phase)
        if phase == "spec_validation":
            prompt_names = {
                Path(str(entry.get("prompt_file"))).name
                for entry in active or []
                if isinstance(entry.get("prompt_file"), str)
            }
            if len(prompt_names) > 1:
                raise resumelib.ResumeError(
                    "unfinished validation conversations mix ordinary and repair inputs; "
                    "pass --fresh-context to start over"
                )
            repair = prompt_names == {".spec-repair-prompt.md"}
            conflicts = (
                (("skip_confirmation", "--skip-confirmation"), ("skip_repair_loop", "--skip-repair-loop"))
                if repair
                else (("skip_validation", "--skip-validate"),)
            )
            controlling_skip = next((item for item in conflicts if getattr(self, item[0])), None)
        if controlling_skip is not None and getattr(self, controlling_skip[0]):
            raise resumelib.ResumeError(f"cannot use {controlling_skip[1]} while resuming unfinished phase {phase!r}")
        preceding = {
            "code_analysis": (),
            "review:analysis": ("skip_analysis",),
            "spec_generation": ("skip_analysis",),
            "review:specgen": ("skip_analysis", "skip_specgen"),
            "harness_generation": ("skip_analysis", "skip_specgen"),
            "spec_validation": ("skip_analysis", "skip_specgen", "skip_harness"),
            "review:validation": ("skip_analysis", "skip_specgen", "skip_harness", "skip_validation"),
            "bug_confirmation": ("skip_analysis", "skip_specgen", "skip_harness", "skip_validation"),
            "bug_classification": (
                "skip_analysis",
                "skip_specgen",
                "skip_harness",
                "skip_validation",
                "skip_confirmation",
            ),
        }.get(phase)
        if preceding is None:
            raise resumelib.ResumeError(
                f"cannot position the pipeline at interrupted phase {phase!r}; pass --fresh-context to start over"
            )
        for field in preceding:
            setattr(self, field, True)

    def _acquire_run_lock(self) -> None:
        if self.run_dir is None or self._run_lock_fd is not None:
            return
        resumelib.ensure_storage(self.run_dir)
        lock_path = resumelib.resume_dir(self.run_dir) / "run.lock"
        flags = os.O_CREAT | os.O_RDWR | getattr(os, "O_NOFOLLOW", 0)
        try:
            fd = os.open(lock_path, flags, 0o600)
        except OSError as exc:
            raise resumelib.ResumeError(f"cannot open safe run lock {lock_path}: {exc}") from exc
        if not stat.S_ISREG(os.fstat(fd).st_mode):
            os.close(fd)
            raise resumelib.ResumeError(f"run lock is not a regular file: {lock_path}")
        os.set_inheritable(fd, False)
        try:
            fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as exc:
            os.close(fd)
            raise resumelib.ResumeError(
                f"run {self.run_id} still has a live phase or agent; "
                "wait for it to finish or terminate it manually before attaching"
            ) from exc
        self._run_lock_fd = fd
        os.environ[resumelib.RUN_LOCK_FD_ENV] = str(fd)

    def _release_run_lock(self) -> None:
        if self._run_lock_fd is None:
            return
        fd = self._run_lock_fd
        if os.environ.get(resumelib.RUN_LOCK_FD_ENV) == str(fd):
            os.environ.pop(resumelib.RUN_LOCK_FD_ENV, None)
        with contextlib.suppress(OSError):
            # Do not explicitly unlock: phase/agent children inherit this open
            # file description, so the kernel releases the lease only after the
            # last live owner exits.
            os.close(fd)
        self._run_lock_fd = None

    def resolve_run_dir(self, *, acquire_lock: bool = False) -> int | None:
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
            os.environ.pop(SNAPSHOT_MODE_ENV, None)
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

        run_preexisting = self.run_dir.exists()
        locked_here = False

        def fail(code: int = 1) -> int:
            if locked_here:
                self._release_run_lock()
            return code

        if run_preexisting:
            try:
                run_info = self.run_dir.lstat()
                if not stat.S_ISDIR(run_info.st_mode):
                    raise resumelib.ResumeError(f"run directory is not a real directory: {self.run_dir}")
            except (OSError, resumelib.ResumeError) as exc:
                print(f"ERROR: {exc}", file=sys.stderr)
                return 1
        if acquire_lock:
            try:
                self.run_dir.mkdir(parents=True, exist_ok=True)
                run_info = self.run_dir.lstat()
                if not stat.S_ISDIR(run_info.st_mode):
                    raise resumelib.ResumeError(f"run directory is not a real directory: {self.run_dir}")
                self._acquire_run_lock()
                locked_here = True
            except (OSError, resumelib.ResumeError) as exc:
                print(f"ERROR: {exc}", file=sys.stderr)
                return 1
        os.environ[resumelib.INVOCATION_ENV] = secrets.token_hex(16)
        os.environ.pop(resumelib.MANUAL_ENV, None)
        os.environ.pop(resumelib.FRESH_ENV, None)
        fallback_artifact = ""
        meta_file = self.run_dir / "run.json"
        metadata: dict[str, Any] | None = None
        if meta_file.is_file():
            with contextlib.suppress(OSError, UnicodeError, json.JSONDecodeError):
                meta = json.loads(meta_file.read_text())
                if isinstance(meta, dict):
                    metadata = meta
                    mode = meta.get("source_mode", "in-place")
                    if mode == "snapshot":
                        self.keep_original = True
                    elif mode == "in-place" and self._keep_original_given:
                        print(
                            "ERROR: --keep-original cannot be enabled when resuming an in-place run",
                            file=sys.stderr,
                        )
                        return fail()
                    stored_artifact = meta.get("artifact")
                    if isinstance(stored_artifact, str):
                        fallback_artifact = stored_artifact

        if self._run_id_given and run_preexisting:
            self._attached_existing_run = True
            try:
                if self.fresh_context:
                    resumelib.initialize_run(self.run_dir, reset=True)
                    try:
                        stored_configuration = resumelib.load_configuration(self.run_dir)
                    except resumelib.ResumeError:
                        # Runs created before checkpoints have no configuration to
                        # restore. The fresh invocation becomes their baseline.
                        pass
                    else:
                        self._restore_resume_configuration(stored_configuration, allow_overrides=True)
                    os.environ[resumelib.FRESH_ENV] = "1"
                else:
                    resumelib.require_supported_run(self.run_dir)
                    if metadata is None:
                        raise resumelib.ResumeError(f"cannot read run metadata from {meta_file}")
                    self._restore_resume_configuration(resumelib.load_configuration(self.run_dir))
                    active = resumelib.active_entries(self.run_dir)
                    if not active:
                        raise resumelib.ResumeError(
                            "this run has no unfinished agent conversation; pass --fresh-context to start over"
                        )
                    phases = {str(entry.get("phase")) for entry in active}
                    if len(phases) != 1:
                        raise resumelib.ResumeError(
                            "unfinished conversations span multiple phases; pass --fresh-context to start over"
                        )
                    self._manual_resume_phase = phases.pop()
                    self._position_at_manual_resume_phase(active)
                    if not self.keep_original:
                        launch_cwds = {entry.get("cwd") for entry in active if entry.get("kind") in {"phase", "review"}}
                        if launch_cwds:
                            raw_launch_cwd = next(iter(launch_cwds))
                            if len(launch_cwds) != 1 or not isinstance(raw_launch_cwd, str):
                                raise resumelib.ResumeError(
                                    "unfinished conversations do not share one safe launch directory; "
                                    "pass --fresh-context to start over"
                                )
                            launch_cwd = Path(raw_launch_cwd)
                            try:
                                launch_info = launch_cwd.lstat()
                            except OSError as exc:
                                raise resumelib.ResumeError(
                                    f"recorded agent launch directory is unavailable: {launch_cwd}"
                                ) from exc
                            if not stat.S_ISDIR(launch_info.st_mode):
                                raise resumelib.ResumeError(
                                    f"recorded agent launch directory is not safe: {launch_cwd}"
                                )
                            self._manual_launch_cwd = launch_cwd
                    os.environ[resumelib.MANUAL_ENV] = "1"
            except resumelib.ResumeError as exc:
                print(f"ERROR: {exc}", file=sys.stderr)
                return fail()

        source_map = self.run_dir / SOURCE_MAP
        if source_map.exists() or source_map.is_symlink():
            try:
                snapshots = load_sources(self.run_dir)
            except SnapshotError as exc:
                print(f"ERROR: cannot restore private source: {exc}", file=sys.stderr)
                return fail()
            self.keep_original = True
            self._snapshot_sources = {name: item.original for name, item in snapshots.items()}
            self._snapshot_paths = [item.source for item in snapshots.values()]
            if self._artifact_given and any(
                source != Path(self.artifact).resolve() for source in self._snapshot_sources.values()
            ):
                print("ERROR: --artifact differs from this run's private source", file=sys.stderr)
                return fail()
        elif self.keep_original:
            try:
                self._snapshot_sources = self._resolve_snapshot_sources(fallback_artifact)
            except SnapshotError as exc:
                print(f"ERROR: cannot prepare private source: {exc}", file=sys.stderr)
                return fail()
        if self.keep_original:
            try:
                self._check_snapshot_overlap()
            except SnapshotError as exc:
                print(f"ERROR: {exc}", file=sys.stderr)
                return fail()

        self.run_dir.mkdir(parents=True, exist_ok=True)
        if not stat.S_ISDIR(self.run_dir.lstat().st_mode):
            print(f"ERROR: run directory is not a real directory: {self.run_dir}", file=sys.stderr)
            return fail()
        if not self._attached_existing_run:
            try:
                resumelib.initialize_run(self.run_dir)
            except resumelib.ResumeError as exc:
                print(f"ERROR: {exc}", file=sys.stderr)
                return fail()
        os.environ["SPECULA_RUN_DIR"] = str(self.run_dir)  # phase subprocesses inherit
        if self.keep_original:
            os.environ[SNAPSHOT_MODE_ENV] = "1"
        else:
            os.environ.pop(SNAPSHOT_MODE_ENV, None)
        self.tlc_scope = str(self.run_dir.resolve())
        os.environ[SCOPE_ENV] = self.tlc_scope
        resource_rc = self._restore_run_resource_config()
        if resource_rc is not None:
            return fail(resource_rc)
        self._write_run_meta()
        if not self._attached_existing_run or self.fresh_context:
            try:
                resumelib.save_configuration(self.run_dir, self._resume_configuration_document())
            except resumelib.ResumeError as exc:
                print(f"ERROR: {exc}", file=sys.stderr)
                return fail()
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
            artifact = Path(self.artifact).resolve()
            with contextlib.suppress(Exception):
                r = subprocess.run(
                    ["git", "-C", str(artifact), "rev-parse", "--show-toplevel", "HEAD"],
                    env=clean_git_environment(),
                    capture_output=True,
                )
                lines = r.stdout.decode(errors="replace").splitlines()
                if r.returncode == 0 and len(lines) == 2 and Path(lines[0]).resolve() == artifact:
                    artifact_sha = lines[1]
        default_selection = self._agent_selection()
        model, effort = self._resolved_run_tuning(default_selection)
        resume_configuration = self._resume_configuration_document()
        meta: dict[str, object] = {
            "run_id": self.run_id,
            "created": _date_iseconds(),
            "argv": self.argv,
            "targets": self.targets,
            "agent": default_selection.agent,
            "model": model,
            "effort": effort,
            "policy_retries": self.policy_retries,
            "transient_resumes": self.transient_resumes,
            "claude_alias": self.claude_alias,
            "artifact": self.artifact,
            "artifact_git_sha": artifact_sha,
            "tlc_memory_limit": self.tlc_memory_limit or os.environ.get(MEMORY_LIMIT_ENV) or "auto",
            "tlc_worker_limit": self.tlc_worker_limit or os.environ.get(WORKER_LIMIT_ENV) or None,
            "resume_configuration": resume_configuration,
        }
        if self.agent_routing is not None:
            assert self.agent_config_path is not None
            routes: dict[str, dict[str, str | None]] = {}
            for route_name, (phase, fallback) in self._route_specs().items():
                selection = self._agent_selection(phase, fallback=fallback)
                route_model, route_effort = self._resolved_run_tuning(selection)
                routes[route_name] = {
                    "agent": selection.agent,
                    "model": route_model,
                    "effort": route_effort,
                }
            meta["agent_config"] = str(self.agent_config_path)
            meta["agent_config_sha256"] = self.agent_routing.source_sha256
            meta["agent_routes"] = routes
        if self.keep_original:
            meta["source_mode"] = "snapshot"
        with contextlib.suppress(OSError):
            meta_file.write_text(json.dumps(meta, indent=2) + "\n")

    def _agent_selection(self, phase: str | None = None, *, fallback: str | None = None) -> AgentSelection:
        if self._restored_routes is not None:
            if phase is None:
                assert self._restored_default is not None
                return self._restored_default
            route = f"review:{fallback}" if phase == "review" and fallback is not None else phase
            return self._restored_routes[route]
        if self.agent_routing is None:
            return AgentSelection(agent=self.agent, model=self.model, effort=self.effort)
        if phase is None:
            return self.agent_routing.default
        return self.agent_routing.resolve(phase, fallback=fallback)

    def _resolved_run_tuning(self, selection: AgentSelection | None = None) -> tuple[str | None, str | None]:
        """Return model/effort values that are knowable at run creation.

        Pipeline flags win even when explicitly empty. An empty flag resets the
        adapter to its own configuration, whose resulting value is unknown here
        and therefore recorded as null. Otherwise mirror the phase and adapter
        environment fallbacks; never guess values selected by CLI config files.
        """
        selected = selection or self._agent_selection()
        if selected.model is not None:
            model = selected.model or None
        else:
            model = os.environ.get("SPECULA_MODEL") or None
            if model is None:
                adapter_model_env = {
                    "claude-code": "CLAUDE_MODEL",
                    "codex": "CODEX_MODEL",
                    "copilot-cli": "COPILOT_MODEL",
                    "opencode": "OPENCODE_MODEL",
                    "pi": "PI_MODEL",
                }.get(selected.agent)
                if adapter_model_env is not None:
                    model = os.environ.get(adapter_model_env) or None

        if selected.effort is not None:
            effort = selected.effort or None
        else:
            effort = os.environ.get("SPECULA_EFFORT") or None
            if effort is None:
                if selected.agent == "claude-code":
                    # Phase launchers explicitly pass max, overriding any
                    # ambient CLAUDE_EFFORT value.
                    effort = "max"
                else:
                    effort_env = {
                        "codex": "CODEX_EFFORT",
                        "opencode": "OPENCODE_EFFORT",
                        "pi": "PI_EFFORT",
                    }.get(selected.agent)
                    if effort_env is not None:
                        effort = os.environ.get(effort_env) or None

        # The Claude adapter omits --effort for this explicit reset sentinel.
        if selected.agent == "claude-code" and effort == "default":
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
        agents = {self.agent}
        if self._restored_routes is not None:
            agents = {selection.agent for selection in self._restored_routes.values()}
        elif self.agent_routing is not None:
            agents = {selection.agent for selection in self.agent_routing.profiles.values()}
        for agent in sorted(agents):
            adapter = LAUNCH_DIR / "adapters" / f"{agent}.sh"
            if not adapter.is_file():
                print(
                    f"ERROR: Unknown agent '{agent}' — adapter not found at {adapter}",
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

    @staticmethod
    def _descriptor_name(target: str) -> str:
        first_line = target.split("\n", 1)[0]
        return first_line.split("|", 1)[0].strip()

    def _index_names(self) -> list[str]:
        """Original run targets first, so a partial resume cannot erase rows."""
        descriptors: list[str] = []
        if self.run_dir is not None:
            metadata = self.run_dir / "run.json"
            with contextlib.suppress(OSError, UnicodeError, json.JSONDecodeError):
                document = json.loads(metadata.read_text())
                stored = document.get("targets") if isinstance(document, dict) else None
                if isinstance(stored, list):
                    descriptors.extend(target for target in stored if isinstance(target, str))
        descriptors.extend(self.targets)
        names = [self._descriptor_name(target) for target in descriptors]
        return list(dict.fromkeys(name for name in names if name))

    def _index_targets(self) -> list[TargetOutput]:
        targets: list[TargetOutput] = []
        output_root = self.run_dir if self.run_dir is not None else _logical_cwd()
        for name in self._index_names():
            if not is_safe_target_name(name):
                log(f"WARNING: cannot update output index for unsafe target name {name!r}")
                continue
            targets.append(TargetOutput(name, Path(self.get_work_dir(name)), output_root))
        return targets

    def _refresh_target_indexes(self) -> tuple[list[TargetOutput], set[Path]]:
        """Refresh target navigation and report indexes published by this call."""
        if self.dry_run:
            return [], set()
        try:
            targets = self._index_targets()
        except Exception as exc:
            log(f"WARNING: cannot resolve output indexes: {exc}")
            return [], set()
        published: set[Path] = set()
        for target in targets:
            try:
                write_target_index(
                    target.name,
                    target.work_dir,
                    output_root=target.output_root,
                    pipeline_log=self.pipeline_log_path,
                )
                published.add(target.work_dir / INDEX_FILENAME)
            except Exception as exc:
                log(f"WARNING: cannot update output index for {target.name}: {exc}")
        return targets, published

    def refresh_target_indexes(self) -> list[TargetOutput]:
        """Best-effort target navigation refresh; never changes pipeline status."""
        targets, _ = self._refresh_target_indexes()
        return targets

    def refresh_output_indexes(self) -> Path | None:
        """Refresh output navigation and return the primary index published now."""
        targets, published = self._refresh_target_indexes()
        if not targets or self.pipeline_log_path is None:
            return None
        if self.run_dir is not None:
            run_root = self.run_dir
        elif len(targets) > 1:
            # Legacy multi-target has a distinct launch-level output directory.
            # Legacy single-target collapses run and target index to one path, so
            # only the detailed target index is generated.
            run_root = self.pipeline_log_path.parent
        else:
            index = targets[0].work_dir / INDEX_FILENAME
            return index if index in published else None
        try:
            write_run_index(
                run_root,
                targets,
                summary=run_root / "pipeline-summary.md",
                pipeline_log=self.pipeline_log_path,
            )
        except Exception as exc:
            log(f"WARNING: cannot update run index: {exc}")
            return None
        return run_root / INDEX_FILENAME

    def initialize_resource_summaries(self, names: list[str]) -> None:
        """Create the per-target resource summaries without affecting the run."""
        if self.dry_run:
            return
        targets = {name: Path(self.get_work_dir(name)) for name in dict.fromkeys(names) if is_safe_target_name(name)}
        if not targets:
            return
        memory_limit = self.tlc_memory_limit or os.environ.get(MEMORY_LIMIT_ENV) or "auto (80% available)"
        worker_limit = self.tlc_worker_limit or os.environ.get(WORKER_LIMIT_ENV) or "unbounded (report only)"
        tracker = ResourceSummaryTracker(
            targets,
            output_root=self.run_dir if self.run_dir is not None else Path(_logical_cwd()),
            maximum_parallelism=self._max_parallel_summary(),
            tlc_memory_limit=memory_limit,
            tlc_worker_limit=worker_limit,
        )
        try:
            tracker.initialize(resume=self.run_dir is not None)
        except Exception as exc:
            log(f"WARNING: cannot initialize resource summaries: {exc}")
            return
        self.resource_summary = tracker

    def _capture_resource_usage(
        self,
        names: list[str] | None = None,
        *,
        require_change: bool = False,
    ) -> None:
        tracker = self.resource_summary
        phase = self._resource_phase_key
        if tracker is None or phase is None:
            return
        try:
            tracker.capture_usage(
                phase,
                self._index_names() if names is None else names,
                require_change=require_change,
            )
        except Exception as exc:
            log(f"WARNING: cannot update {phase} resource usage: {exc}")

    def _skip_resource_phase(self, phase: str, names: list[str]) -> None:
        if self.resource_summary is None:
            return
        try:
            self.resource_summary.skip_phase(phase, names)
        except Exception as exc:
            log(f"WARNING: cannot mark {phase} resource usage as skipped: {exc}")

    def _complete_resource_summaries(self) -> None:
        if self.resource_summary is None:
            return
        try:
            self.resource_summary.complete_run()
        except Exception as exc:
            log(f"WARNING: cannot finalize resource summaries: {exc}")

    def refresh_resource_summaries(self) -> None:
        """Best-effort refresh used by the outer failure-cleanup path."""
        if self.resource_summary is None:
            return
        try:
            self.resource_summary.refresh()
        except Exception as exc:
            log(f"WARNING: cannot refresh resource summaries: {exc}")

    @contextlib.contextmanager
    def resource_phase(self, phase: str, names: list[str]) -> Iterator[None]:
        """Measure one grouped phase segment and preserve the phase result."""
        tracker = self.resource_summary
        selected = list(dict.fromkeys(names))
        if tracker is None:
            yield
            return

        try:
            tracker.start_phase(phase, selected)
        except Exception as exc:
            log(f"WARNING: cannot start {phase} resource accounting: {exc}")
        previous_phase = self._resource_phase_key
        self._resource_phase_key = phase
        started_at = time.monotonic()
        succeeded = False
        try:
            yield
            succeeded = True
        finally:
            elapsed = time.monotonic() - started_at
            self._capture_resource_usage(selected)
            self._resource_phase_key = previous_phase
            try:
                tracker.finish_phase(phase, selected, elapsed, succeeded)
            except Exception as exc:
                log(f"WARNING: cannot finish {phase} resource accounting: {exc}")

    def prepare_source_snapshots(self, names: list[str]) -> None:
        if not self.keep_original:
            return
        if self.run_dir is None:
            raise SnapshotError("--keep-original requires an isolated run")
        if set(self._snapshot_sources) != set(names):
            raise SnapshotError("private source targets do not match this invocation")
        validate_snapshot_destinations(self.run_dir, tuple(self._snapshot_sources))
        if self.dry_run:
            log("[DRY RUN] would create a full private source copy")
            return
        snapshots = prepare_sources(self.run_dir, self._snapshot_sources)
        self._snapshot_paths = [snapshots[name].source for name in names]
        existing = [path for path in os.environ.get("SPECULA_SANDBOX_EXTRA_WRITE", "").split(os.pathsep) if path]
        os.environ["SPECULA_SANDBOX_EXTRA_WRITE"] = os.pathsep.join(
            dict.fromkeys([*existing, *(str(path) for path in self._snapshot_paths)])
        )
        for name in names:
            log(f"Private source for {name}: {snapshots[name].source}")

    def finalize_source_snapshots(self) -> None:
        if not self.keep_original or self.dry_run or not self._snapshot_paths:
            return
        assert self.run_dir is not None
        for name, changed in capture_changes(self.run_dir).items():
            patch = self.run_dir / name / "changes.patch"
            label = "changes captured" if changed else "no changes"
            log(f"Source diff for {name}: {patch} ({label})")

    def wait_for_quota(self, *, reactive: bool = False) -> None:
        wait_for_quota(
            usage_script=USAGE_SCRIPT,
            q5=self.quota_5h,
            q7=self.quota_7d,
            max_waits=self.quota_max_waits,
            claude_alias=self.claude_alias,
            reactive=reactive,
        )

    def wait_for_phase_quota(self, phase: str, *, fallback: str | None = None) -> None:
        """The proactive usage endpoint is Claude-specific."""
        if self._agent_selection(phase, fallback=fallback).agent == "claude-code":
            self.wait_for_quota()

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

    def repair_phase3_commit_path(self, name: str) -> Path:
        return Path(self.get_work_dir(name)) / "spec" / ".repair-phase3-commit.json"

    def persist_open_repair_snapshot(self, name: str, snapshot: dict[Path, str], round_: int) -> None:
        """Durably publish the OPEN inputs before a repair subprocess starts.

        The unique commit token is copied into a separate commit-proof marker
        only after the repair launcher returns success. Recovery can therefore
        distinguish a completed Phase 3 whose snapshot cleanup was interrupted
        from an attempt killed after merely writing CONSUMED into its requests,
        without depending on Phase-4 cache invalidation.
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

    def clear_repair_phase3_snapshot(self, name: str) -> None:
        if not self.dry_run:
            self.repair_phase3_snapshot_path(name).unlink(missing_ok=True)

    def clear_repair_phase3_commit(self, name: str) -> None:
        if not self.dry_run:
            self.repair_phase3_commit_path(name).unlink(missing_ok=True)

    def clear_open_repair_snapshot(self, name: str) -> None:
        """Discard an uncommitted repair attempt and all of its durable state."""
        self.clear_repair_phase3_snapshot(name)
        self.clear_repair_phase3_commit(name)

    def publish_repair_phase3_commit(self, repair_round: int, names: list[str] | None = None) -> None:
        """Durably prove that the exact repair attempt returned successfully.

        This proof is deliberately separate from confirmation-generation.json:
        recovery must remain correct even when Phase 4 stops invalidating all
        cached findings after every scoped repair. The exact Phase-3 findings
        document stays with the proof until its scoped confirmation/reconciliation
        succeeds, so a crash cannot silently switch the current violation set.
        """
        if self.dry_run:
            return
        for name in names if names is not None else self.extract_names():
            loaded = self.load_open_repair_snapshot(name)
            if loaded is None:
                raise RuntimeError(f"cannot commit repair Phase 3 for {name} without a durable snapshot")
            _snapshot, snapshot_round, commit_token = loaded
            if snapshot_round != repair_round or commit_token is None:
                raise RuntimeError(f"cannot commit mismatched repair Phase 3 snapshot for {name}")
            spec_dir = Path(self.get_work_dir(name)) / "spec"
            findings_path = spec_dir / "findings.json"
            if findings_path.is_symlink() or not findings_path.is_file():
                raise RuntimeError(f"repair Phase 3 for {name} did not produce a safe spec/findings.json")
            try:
                findings_json = findings_path.read_text()
                findings_doc = json.loads(findings_json)
            except (OSError, UnicodeError, json.JSONDecodeError) as exc:
                raise RuntimeError(f"repair Phase 3 for {name} produced invalid spec/findings.json: {exc}") from exc
            findings = findings_doc.get("findings") if isinstance(findings_doc, dict) else None
            if not isinstance(findings, list):
                raise RuntimeError(f"repair Phase 3 for {name} produced findings.json without a findings list")
            seen: set[str] = set()
            violation_ids: list[str] = []
            for index, finding in enumerate(findings):
                finding_id = finding.get("id") if isinstance(finding, dict) else None
                if (
                    not isinstance(finding_id, str)
                    or not finding_id.startswith("MC-")
                    or set(finding_id) - set("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789._-")
                    or finding_id in {".", ".."}
                    or finding_id in seen
                    or finding.get("source") != "model-checking"
                ):
                    raise RuntimeError(
                        f"repair Phase 3 for {name} produced invalid model-checking finding at index {index}"
                    )
                seen.add(finding_id)
                violation_ids.append(finding_id)
            # Reuse the confirmation dispatcher's full MC-input validation so
            # an unusable counterexample/config cannot cross the durable commit
            # point and strand a CONSUMED request.
            from specula.confirmlib import _expected_mc_ids

            validated, validation_errors = _expected_mc_ids(spec_dir)
            if validated is None or validation_errors or list(validated) != violation_ids:
                detail = validation_errors[0] if validation_errors else "finding order/identity mismatch"
                raise RuntimeError(f"repair Phase 3 for {name} produced invalid spec/findings.json: {detail}")
            request_ids = sorted(path.stem for path in _snapshot)
            marker = self.repair_phase3_commit_path(name)
            payload = (
                json.dumps(
                    {
                        "version": 2,
                        "repair_round": repair_round,
                        "commit_token": commit_token,
                        "request_ids": request_ids,
                        "violation_ids": violation_ids,
                        "findings_json": findings_json,
                    },
                    ensure_ascii=False,
                    sort_keys=True,
                )
                + "\n"
            )
            if marker.is_file():
                try:
                    existing = json.loads(marker.read_text())
                except (OSError, json.JSONDecodeError):
                    existing = None
                if (
                    isinstance(existing, dict)
                    and existing.get("version") == 1
                    and existing.get("repair_round") == repair_round
                    and existing.get("commit_token") == commit_token
                ):
                    self._atomic_replace_text(marker, payload)
                    continue
            try:
                self._publish_deferred_no_replace(marker, payload)
            except FileExistsError:
                log(f"ERROR: durable Phase 3 commit proof already exists for {name}: {marker}")
                raise SystemExit(1) from None

    def load_repair_phase3_commit(self, name: str) -> dict[str, Any] | None:
        """Load one pending scoped-confirmation checkpoint, failing closed."""
        marker = self.repair_phase3_commit_path(name)
        if not marker.is_file():
            return None
        try:
            doc = json.loads(marker.read_text())
            if not isinstance(doc, dict):
                raise ValueError("top level is not an object")
            version = doc.get("version")
            repair_round = doc.get("repair_round")
            commit_token = doc.get("commit_token")
            if (
                version not in {1, 2}
                or not isinstance(repair_round, int)
                or isinstance(repair_round, bool)
                or repair_round < 1
                or not isinstance(commit_token, str)
                or re.fullmatch(r"[0-9a-f]{32}", commit_token) is None
            ):
                raise ValueError("invalid version, round, or commit token")
            if version == 1:
                # Version 1 proved Phase-3 completion but predates the durable
                # scoped-input checkpoint. Bind it to the still-current file
                # once, preserving recovery for interrupted upgraded runs.
                findings_path = Path(self.get_work_dir(name)) / "spec" / "findings.json"
                if findings_path.is_symlink() or not findings_path.is_file():
                    raise ValueError("legacy proof has no safe findings.json")
                findings_json = findings_path.read_text()
                findings_doc = json.loads(findings_json)
                findings = findings_doc.get("findings") if isinstance(findings_doc, dict) else None
                if not isinstance(findings, list):
                    raise ValueError("legacy findings.json has no findings list")
                doc["request_ids"] = []
                doc["violation_ids"] = [finding.get("id") for finding in findings if isinstance(finding, dict)]
                doc["findings_json"] = findings_json
            request_ids = doc.get("request_ids")
            violation_ids = doc.get("violation_ids")
            findings_json_value = doc.get("findings_json")
            if (
                not isinstance(request_ids, list)
                or not all(isinstance(value, str) and re.fullmatch(r"RR-\d+", value) for value in request_ids)
                or len(set(request_ids)) != len(request_ids)
                or not isinstance(violation_ids, list)
                or not all(isinstance(value, str) and value for value in violation_ids)
                or len(set(violation_ids)) != len(violation_ids)
                or not isinstance(findings_json_value, str)
            ):
                raise ValueError("invalid request or violation checkpoint")
            findings_doc = json.loads(findings_json_value)
            findings = findings_doc.get("findings") if isinstance(findings_doc, dict) else None
            actual_ids = (
                [finding.get("id") for finding in findings if isinstance(finding, dict)]
                if isinstance(findings, list)
                else None
            )
            if actual_ids != violation_ids:
                raise ValueError("violation ids do not match findings snapshot")
            live = Path(self.get_work_dir(name)) / "spec" / "findings.json"
            if live.is_symlink() or not live.is_file() or live.read_text() != findings_json_value:
                raise ValueError("live findings.json diverges from the committed Phase-3 snapshot")
        except (OSError, UnicodeError, ValueError, json.JSONDecodeError) as exc:
            log(f"ERROR: invalid pending repair Phase 3 commit for {name}: {marker} ({exc})")
            raise SystemExit(1) from exc
        return doc

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
                # A surviving commit proof is intentionally pending until its
                # exact scoped confirmation/reconciliation succeeds.
                if self.load_repair_phase3_commit(name) is not None:
                    recovered_commits.add(name)
                continue
            snapshot, round_, commit_token = loaded
            if self._repair_phase3_snapshot_committed(name, snapshot, round_, commit_token):
                marker = self.repair_phase3_commit_path(name)
                try:
                    marker_doc = json.loads(marker.read_text())
                except (OSError, json.JSONDecodeError):
                    marker_doc = None
                if not isinstance(marker_doc, dict) or marker_doc.get("version") != 2:
                    # Upgrade an interrupted pre-scoped run while the exact
                    # OPEN-input snapshot still identifies its request set.
                    self.publish_repair_phase3_commit(round_, [name])
                self.clear_repair_phase3_snapshot(name)
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

        CONSUMED alone is not proof: an agent can write it before failing. The
        orchestrator publishes a separate commit marker only after a zero exit;
        it contains the snapshot's unique attempt token.
        Complete, executable CONSUMED requests are required as a second guard.
        """
        if commit_token is None:
            return False
        marker = self.repair_phase3_commit_path(name)
        try:
            doc = json.loads(marker.read_text())
        except (OSError, json.JSONDecodeError):
            doc = None
        committed = bool(
            isinstance(doc, dict)
            and doc.get("version") in {1, 2}
            and doc.get("repair_round") == round_
            and doc.get("commit_token") == commit_token
        )
        if committed and doc.get("version") == 2:
            committed = doc.get("request_ids") == sorted(path.stem for path in snapshot)
        if not committed:
            # Compatibility for an interrupted pre-decoupling run. New
            # generation markers never contain repair_phase3_commit.
            legacy = Path(self.get_work_dir(name)) / "spec" / "confirmation-generation.json"
            try:
                legacy_doc = json.loads(legacy.read_text())
            except (OSError, json.JSONDecodeError):
                return False
            if (
                not isinstance(legacy_doc, dict)
                or legacy_doc.get("repair_round") != round_
                or legacy_doc.get("repair_phase3_commit") != commit_token
            ):
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
            if len(cells) >= 5 and cells[1].strip() in {"Bug", "Entry"} and cells[3].strip() == "Status":
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

            report = Path(self.get_work_dir(n)) / "confirmed-bugs.md"
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
        Repair crash recovery uses a separate durable commit proof.
        """
        if self.dry_run:
            return
        for n in names if names is not None else self.extract_names():
            marker = Path(self.get_work_dir(n)) / "spec" / "confirmation-generation.json"
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
            self._atomic_replace_text(marker, json.dumps(payload, indent=2, sort_keys=True) + "\n")

    # ── phase runners ──
    @staticmethod
    def _model_effort_args(selection: AgentSelection) -> list[str]:
        """Explicit pipeline tuning flags, preserving an explicit empty value.

        An absent flag stays absent so phase launchers can apply their run-wide
        SPECULA_* fallback and adapter-specific defaults.  An explicit empty
        flag must be forwarded to override (and clear) those fallbacks.
        """
        args: list[str] = []
        if selection.model is not None:
            args.append(f"--model={selection.model}")
        if selection.effort is not None:
            args.append(f"--effort={selection.effort}")
        return args

    def _max_parallel_summary(self) -> str:
        if self.max_parallel is not None:
            return self.max_parallel
        confirmation_default = (
            "legacy confirmation 1 at a time" if self.confirm_legacy else "per-finding confirmation 4 at a time"
        )
        return f"phase defaults (ordinary phases 1 at a time; {confirmation_default})"

    def _phase_args(
        self,
        positional: list[str],
        pre: list[str] | None = None,
        with_artifact: bool = True,
        *,
        phase: str | None = None,
        fallback: str | None = None,
    ) -> list[str]:
        selection = self._agent_selection(phase, fallback=fallback)
        args = list(pre or [])
        if self.max_parallel is not None:
            args.append(f"--max-parallel={self.max_parallel}")
        args += [
            f"--max-turns={self.max_turns}",
            f"--policy-retries={self.policy_retries}",
            f"--transient-resumes={self.transient_resumes}",
            f"--agent={selection.agent}",
            f"--claude-alias={self.claude_alias}",
            *self._model_effort_args(selection),
        ]
        if with_artifact and self._artifact_given and not self.keep_original:
            args.append(f"--artifact={self.artifact}")
        args += positional
        return args

    def _run_launcher(self, script: str, args: list[str]) -> None:
        env = os.environ.copy()
        if self.keep_original:
            # Phase launchers calculate their exact private-source ceiling after
            # parsing targets.  Remove ambient repository selectors before even
            # their prerequisite checks run.
            sanitize_snapshot_git_environment(env)
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
        if self.pipeline_log_path is not None:
            env[PIPELINE_LOG_ENV] = str(self.pipeline_log_path)
        if self._manual_launch_cwd is not None:
            env["PWD"] = str(self._manual_launch_cwd)
        pass_fds: tuple[int, ...] = ()
        if self._run_lock_fd is not None:
            env[resumelib.RUN_LOCK_FD_ENV] = str(self._run_lock_fd)
            pass_fds = (self._run_lock_fd,)
        else:
            env.pop(resumelib.RUN_LOCK_FD_ENV, None)

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
                cwd=self._manual_launch_cwd,
                start_new_session=True,
                pass_fds=pass_fds,
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

    def _resource_names_from_args(self, args: list[str]) -> list[str]:
        known_names = self._index_names()
        known = set(known_names)
        selected = [
            self._descriptor_name(arg)
            for arg in args
            if not arg.startswith("--") and self._descriptor_name(arg) in known
        ]
        return list(dict.fromkeys(selected)) or known_names

    def _phase(self, banner: str, script: str, args: list[str]) -> None:
        divider()
        log(banner)
        divider()
        if self.dry_run:
            log(f"[DRY RUN] bash scripts/launch/{script} {' '.join(args)}")
            return
        resource_names = self._resource_names_from_args(args)
        self._capture_resource_usage(resource_names)
        try:
            self._run_launcher(script, args)
        finally:
            self._capture_resource_usage(resource_names, require_change=True)
            self.refresh_target_indexes()

    def run_phase1_analysis(self) -> None:
        self._phase(
            "PHASE 1: CODE ANALYSIS",
            "launch_code_analysis.sh",
            self._phase_args(self.targets, phase="analyze"),
        )

    def run_review(self, phase: str, names: list[str], *, force: bool = False) -> None:
        if self.skip_reviews and not force:
            log(f"Skipping {phase} review (--skip-reviews)")
            return
        # launch_review.sh's contract is `<phase> <name...>`: it reads the phase
        # from the first positional (ReviewPhase.run: phase = argv[0]) and treats
        # every other non-flag arg as a target. The pre-migration bash emitted the
        # flags BEFORE the phase, so a real run parsed phase as "--agent=..." and
        # died with "Unknown phase" — invisible under --dry-run, which only logs
        # the command without executing it. Phase goes first: a deliberate
        # divergence from the buggy bash order (git history has the original).
        fallback = {
            "analysis": "analyze",
            "specgen": "specgen",
            "validation": "validate",
        }[phase]
        selection = self._agent_selection("review", fallback=fallback)
        if self.agent_routing is not None or self._restored_routes is not None:
            self.wait_for_phase_quota("review", fallback=fallback)
        args = [
            phase,
            f"--agent={selection.agent}",
            f"--claude-alias={self.claude_alias}",
            f"--policy-retries={self.policy_retries}",
            f"--transient-resumes={self.transient_resumes}",
            *self._model_effort_args(selection),
            *names,
        ]
        self._phase(f"REVIEW: {phase}", "launch_review.sh", args)

    def run_phase2_specgen(self) -> None:
        self._phase(
            "PHASE 2: SPEC GENERATION",
            "launch_spec_generation.sh",
            self._phase_args(self.extract_names(), phase="specgen"),
        )

    def run_phase2_5_harness(self) -> None:
        self._phase(
            "PHASE 2.5: HARNESS GENERATION (instrumentation + trace collection)",
            "launch_harness_generation.sh",
            self._phase_args(self.extract_names(), phase="harness"),
        )

    def run_phase3_validation(self) -> None:
        self._phase(
            "PHASE 3: SPEC VALIDATION (trace validation + invariant checking + bug hunting)",
            "launch_spec_validation.sh",
            self._phase_args(self.extract_names(), phase="validate"),
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
            self._phase_args(self.extract_names(), pre=pre or None, phase="confirm"),
        )

    def _run_repair_result_dispatcher(
        self,
        name: str,
        repair_round: int,
        repair_token: str,
        violation_ids: list[str],
    ) -> None:
        """Reconcile one committed repair result and confirm only its violations.

        The zero-violation path is dispatcher-only report/evidence maintenance:
        it starts no Phase-4 finding agent. A non-empty pass uses the ordinary
        per-finding confirmation methodology, but its input is exactly the
        committed Phase-3 findings snapshot (never code-review candidates).
        """
        pre = [
            f"--repair-round={repair_round}",
            f"--repair-token={repair_token}",
        ]
        if self.confirm_debate:
            pre.append("--debate")
        if violation_ids:
            banner = (
                f"REPAIR ROUND {repair_round}: PHASE 4 "
                f"({len(violation_ids)} current violation(s): {', '.join(violation_ids)})"
            )
        else:
            banner = f"REPAIR ROUND {repair_round}: RESULT RECONCILIATION (0 violations; no Phase 4 finding agents)"
        self._phase(
            banner,
            "launch_bug_confirmation.sh",
            self._phase_args([name], pre=pre, phase="confirm"),
        )

    def reconcile_repair_without_violations(
        self,
        name: str,
        repair_round: int,
        repair_token: str,
    ) -> None:
        """Update the existing evidence/report after a clean Phase-3 pass."""
        self._run_repair_result_dispatcher(name, repair_round, repair_token, [])

    def run_repair_confirmation(
        self,
        name: str,
        repair_round: int,
        repair_token: str,
        violation_ids: list[str],
    ) -> None:
        if not violation_ids:
            raise ValueError("repair Phase 4 requires at least one current violation")
        self._run_repair_result_dispatcher(name, repair_round, repair_token, violation_ids)

    def process_pending_repair_results(self, names: set[str] | None = None) -> set[str]:
        """Finish every committed Phase-3 result exactly once.

        A marker is removed only after the scoped dispatcher succeeds. Partial
        confirmation failure therefore leaves the exact token/input recoverable,
        while per-finding verdict caches retain completed current violations.
        """
        if self.dry_run:
            return set()
        selected = set(self.extract_names()) if names is None else set(names)
        processed: set[str] = set()
        for name in self.extract_names():
            if name not in selected:
                continue
            commit = self.load_repair_phase3_commit(name)
            if commit is None:
                continue
            violation_ids = list(commit["violation_ids"])
            if violation_ids:
                self.wait_for_phase_quota("confirm")
                self.run_repair_confirmation(
                    name,
                    int(commit["repair_round"]),
                    str(commit["commit_token"]),
                    violation_ids,
                )
            else:
                self.reconcile_repair_without_violations(
                    name,
                    int(commit["repair_round"]),
                    str(commit["commit_token"]),
                )
            self.clear_repair_phase3_commit(name)
            processed.add(name)
        return processed

    def run_phase3_repair(self, round_: int, names: list[str] | None = None) -> None:
        """Phase 3 in repair mode: consume OPEN repair requests, repair the spec,
        perform full trace validation and model checking, write the current
        findings set, and mark each repaired request CONSUMED."""
        selected = names if names is not None else self.extract_names()
        self._phase(
            f"REPAIR ROUND {round_}: PHASE 3 (scoped spec/fault/invariant repair)",
            "launch_spec_validation.sh",
            self._phase_args(selected, pre=["--repair"], phase="repair", fallback="validate"),
        )
        self.publish_repair_phase3_commit(round_, selected)

    def run_phase4b_classification(self) -> None:
        self._phase(
            "PHASE 4b: BUG CLASSIFICATION (severity tier assignment)",
            "launch_bug_classification.sh",
            self._phase_args(self.extract_names(), with_artifact=False, phase="classify"),
        )

    def run_repair_loop(self, prepared_commits: set[str] | None = None) -> set[str]:
        """Confirmation back-edge over current conformance violations only.

        Phase 3 performs the existing full trace-validation/model-checking repair
        pass. Zero current violations are reconciled without a Phase-4 finding
        agent; otherwise Phase 4 receives exactly the current ``findings.json``
        entries. Completed/code-review findings are preserved and never re-run.
        Only a new PENDING REPAIR result creates the next back-edge. The global
        round cap still files any remaining OPEN request under deferred/.

        A caller that already ran startup reconciliation passes its exact
        committed-target set. A direct caller leaves it unset. The returned set
        is exactly the targets covered by a recovered or newly successful repair
        Phase 3 during this invocation.
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
        self.refresh_target_indexes()
        phase3_targets = set(recovered_commits)
        if recovered_commits:
            try:
                self.process_pending_repair_results(recovered_commits)
            except BaseException as exc:
                self.regenerate_ledger()
                detail = f"exit {exc.code}" if isinstance(exc, SystemExit) else type(exc).__name__
                names = ", ".join(sorted(recovered_commits))
                log(
                    f"ERROR: recovered repair result processing failed for {names} ({detail}); "
                    "the exact committed violations were retained for retry."
                )
                raise
            self.regenerate_ledger()
            names = ", ".join(sorted(recovered_commits))
            log(f"Recovered committed repair Phase 3 for {names}; completed its pending scoped result pass.")
            if self.has_open_repair_requests():
                log("Scoped result pass opened repair requests; continuing the repair loop.")

        if not self.has_open_repair_requests():
            if not recovered_commits:
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
                    self.wait_for_phase_quota(
                        "repair", fallback="validate"
                    )  # budget pressure -> WAIT, never auto-defer
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
                    self.clear_repair_phase3_snapshot(name)
                except OSError as cleanup_exc:
                    # Phase 3 already crossed its tokenized durable commit
                    # point. Never turn cleanup failure into repair failure:
                    # retain CONSUMED + snapshot so startup can finalize the
                    # exact commit and continue with the scoped result pass.
                    self.regenerate_ledger()
                    log(
                        f"ERROR: committed repair Phase 3 for {name}, but could not clear its durable snapshot "
                        f"({cleanup_exc}); CONSUMED state was retained for startup recovery."
                    )
                    raise
                repaired_names.append(name)
                phase3_targets.add(name)

            try:
                self.process_pending_repair_results(set(repaired_names))
            except BaseException as exc:
                self.regenerate_ledger()
                detail = f"exit {exc.code}" if isinstance(exc, SystemExit) else type(exc).__name__
                names = ", ".join(repaired_names) or "none"
                log(
                    f"ERROR: repair loop failed in round {round_} while processing current violations ({detail}); "
                    f"successful Phase 3 commits were retained for: {names}. "
                    "Rerun the pipeline; startup recovery will retry only unfinished current violations."
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
            cb = Path(self.get_work_dir(n)) / "confirmed-bugs.md"
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

            confirmed = work_dir / "confirmed-bugs.md"
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

            severity = work_dir / "bug-severity.md"
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
        print(f"Transient resumes: {self.transient_resumes}")
        if self.agent_routing is None:
            print(f"Agent:        {self.agent}  (claude-alias={self.claude_alias})")
        else:
            print(
                f"Agent config: {self.agent_config_path}"
                f"  (default={self._agent_selection().agent}, claude-alias={self.claude_alias})"
            )
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

        self.initialize_resource_summaries(self._index_names())
        self.prepare_source_snapshots(names)

        start_time = int(time.time())

        if self._manual_resume_phase is not None and self._manual_resume_phase.startswith("review:"):
            review_phase = self._manual_resume_phase.split(":", 1)[1]
            if review_phase not in {"analysis", "specgen", "validation"}:
                log(f"ERROR: invalid interrupted review phase {review_phase!r}")
                raise SystemExit(1)
            log(f"Restoring interrupted {review_phase} review before continuing the pipeline")
            self.run_review(review_phase, names, force=True)
            self._manual_resume_phase = None

        # Recover before Phase 1/2/2.5 can mutate the artifacts that the
        # snapshot token commits. Skip flags control later work, never whether
        # durable crash state is reconciled.
        recovered_phase3_commits = self.prepare_repair_state()
        self.refresh_output_indexes()
        upstream_all_skipped = self.skip_analysis and self.skip_specgen and self.skip_harness

        # A committed repair result is bound to the exact Phase-3 findings
        # checkpoint. Finish that scoped result pass before any upstream phase
        # can mutate its source/spec artifacts.
        resumed_repair = False
        phase3_targets = set(recovered_phase3_commits)
        if recovered_phase3_commits and (self.skip_confirmation or self.skip_repair_loop):
            disabled = "--skip-confirmation" if self.skip_confirmation else "--skip-repair-loop"
            log(
                f"ERROR: cannot use {disabled} while a committed repair result is pending; "
                "resume once without that flag so its exact findings can be reconciled."
            )
            raise SystemExit(1)
        if recovered_phase3_commits:
            log("Resuming committed repair result before upstream phases")
            with self.resource_phase("phase4a", names):
                phase3_targets = self.run_repair_loop(prepared_commits=recovered_phase3_commits)
            resumed_repair = True

        if not self.skip_analysis:
            with self.resource_phase("phase1", names):
                self.wait_for_phase_quota("analyze")
                self.run_phase1_analysis()
                self.run_review("analysis", names)
        else:
            log("Skipping Phase 1 (--skip-analysis)")
            self._skip_resource_phase("phase1", names)

        if not self.skip_specgen:
            with self.resource_phase("phase2", names):
                self.wait_for_phase_quota("specgen")
                self.run_phase2_specgen()
                self.run_review("specgen", names)
        else:
            log("Skipping Phase 2 (--skip-specgen)")
            self._skip_resource_phase("phase2", names)

        if not self.skip_harness:
            with self.resource_phase("phase2_5", names):
                self.wait_for_phase_quota("harness")
                self.run_phase2_5_harness()
        else:
            log("Skipping Phase 2.5 (--skip-harness)")
            self._skip_resource_phase("phase2_5", names)

        # Resume OPEN repairs before ordinary Phase 3. An unfinished Phase 4
        # conversation must settle first because it owns the active session.
        if (
            not resumed_repair
            and not self.skip_confirmation
            and not self.skip_repair_loop
            and self._manual_resume_phase != "bug_confirmation"
            and self.has_open_repair_requests()
        ):
            log("Resuming pending repair requests before the ordinary Phase 3 pass")
            with self.resource_phase("phase4a", names):
                phase3_targets = self.run_repair_loop(prepared_commits=set())
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
            with self.resource_phase("phase3", names):
                self.wait_for_phase_quota("validate")
                self.run_phase3_validation()
                self.run_review("validation", names)
            normal_phase3_ran = True
        elif phase3_covered:
            source = "resumed repair loop" if resumed_repair else "recovered committed repairs"
            log(f"Ordinary Phase 3 covered for every target by the {source}")
            self._skip_resource_phase("phase3", names)
        else:
            log("Skipping Phase 3 (--skip-validate)")
            self._skip_resource_phase("phase3", names)

        phase4_covered = resumed_repair and not normal_phase3_ran
        fresh_phase4_ran = False
        if not self.skip_confirmation and not phase4_covered:
            with self.resource_phase("phase4a", names):
                self.wait_for_phase_quota("confirm")
                self.run_phase4_confirmation()
                fresh_phase4_ran = True
                if not self.skip_repair_loop:
                    self.run_repair_loop()
                else:
                    log("Skipping repair loop (--skip-repair-loop)")
        elif self.skip_confirmation:
            log("Skipping Phase 4a (--skip-confirmation)")
            self._skip_resource_phase("phase4a", names)
        else:
            log("Initial Phase 4 completed by the resumed repair loop")

        if not fresh_phase4_ran and self.skip_repair_loop:
            log("Skipping repair loop (--skip-repair-loop)")

        if not self.skip_classification:
            with self.resource_phase("phase4b", names):
                self.wait_for_phase_quota("classify")
                self.run_phase4b_classification()
        else:
            log("Skipping Phase 4b (--skip-classification)")
            self._skip_resource_phase("phase4b", names)

        if not self.dry_run and self.run_dir is not None:
            try:
                active = resumelib.active_entries(self.run_dir)
            except resumelib.ResumeError as exc:
                log(f"ERROR: cannot verify completed conversation state: {exc}")
                return 1
            if active:
                phases = ", ".join(sorted({str(entry.get("phase")) for entry in active}))
                log(f"ERROR: pipeline cannot complete with unfinished conversation(s) in {phases}")
                return 1

        self.generate_summary()
        self._complete_resource_summaries()
        self.refresh_output_indexes()

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
    rc = p.resolve_run_dir(acquire_lock=True)
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
    p.pipeline_log_path = log_path
    tee = subprocess.Popen(["tee", str(log_path)], stdin=subprocess.PIPE)
    assert tee.stdin is not None  # stdin=PIPE
    tee_in = tee.stdin
    terminal_stdout = os.fdopen(os.dup(1), "w", encoding="utf-8", errors="surrogateescape")
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
        try:
            p.finalize_source_snapshots()
        except BaseException as e:
            traceback.print_exc()
            if code == 0:
                code = 130 if isinstance(e, KeyboardInterrupt) else 1
        try:
            p.refresh_resource_summaries()
        except BaseException:
            # Resource summaries are derived output and must not mask the run.
            traceback.print_exc()
        try:
            p.refresh_output_indexes()
        except BaseException:
            # Navigation is a disposable view and must never mask the pipeline's
            # original exit status, including on an interrupted cleanup path.
            traceback.print_exc()
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
        result_index: Path | None = None
        with contextlib.suppress(BaseException):
            # tee creates the log asynchronously. Refresh once more after EOF so
            # even an immediate pipeline failure gets a Troubleshooting link.
            result_index = p.refresh_output_indexes()
        if tee_rc != 0:
            code = tee_rc
        try:
            if code == 0 and result_index is not None:
                with contextlib.suppress(OSError, UnicodeError):
                    print(
                        f"\nView all results: {result_index} (final reports are listed at the top).",
                        file=terminal_stdout,
                        flush=True,
                    )
        finally:
            with contextlib.suppress(OSError, UnicodeError):
                terminal_stdout.close()
            p._release_run_lock()
    return code


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
