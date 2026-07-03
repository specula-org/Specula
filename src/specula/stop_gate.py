#!/usr/bin/env python3
"""Stop gate — completion gate for Specula phase agents.

Batch agents must not end their turn while backgrounded work (TLC, builds,
tests) is still running unobserved, and must not finish a phase without its
deliverable. The skill guides already say so (tla-checking-workflow guide,
"Batch Mode Constraints"), but a written rule cannot stop a model that ends
its turn anyway — this gate can. It enforces one contract in two places:

  execution layer  — agent-side Stop hooks (`claude` / `codex` subcommands):
                     when the agent tries to end its turn, the hook checks the
                     contract and blocks the stop with corrective instructions;
  acceptance layer — launcher-side audit (`accept` subcommand, called by
                     phaselib after the agents exit): the same contract,
                     re-checked from outside, so a run that slipped through
                     is loudly FAILED in the summary instead of silently OK.

The contract forces an ACCOUNT, never an outcome. A report documenting zero
findings is a valid deliverable; a fabricated success is not. An agent that
genuinely cannot finish writes BLOCKED.md next to the deliverable (what it
tried, why it cannot proceed) and is then allowed to stop — "no silent quit"
is the only thing being enforced.

Generic interface (adapter-independent — adapters that cannot host a stop
hook simply never read these, and the gate fails open by construction):

  SPECULA_PHASE          phase key (phaselib Phase.key, e.g. "spec_validation")
  SPECULA_WORK_DIR       the target's .specula-output directory
  SPECULA_STOP_GATE      set to "off" to disable the gate entirely
  SPECULA_STOP_GATE_CAP  blocks allowed per agent run before the fuse opens
                         (default 5; the fuse writes FAILED-HOOK-CAP and lets
                         the stop through so a confused agent can never loop
                         forever)

Per-run state lives under $SPECULA_WORK_DIR/.stop-gate/ (block counter,
FAILED-HOOK-CAP marker, gate.log audit trail); adapters reset the counter and
marker when they launch a fresh agent.

Fail-open principle: any error in the gate itself — unreadable state, garbage
input, missing directories — allows the stop. A broken gate must never wedge
a healthy run.

Invoked by file path, never `-m` (see adapters/claude-code.sh for why).
Stdlib-only; runs under any python3 >= 3.10.
"""

import contextlib
import json
import os
import shlex
import sys
import time
from pathlib import Path
from typing import Any

SPECULA_ROOT = Path(__file__).resolve().parents[2]
STATE_DIRNAME = ".stop-gate"

# Acceptance-layer contract: the phase's primary deliverable, relative to the
# work dir. Only phases whose deliverable is both a hard prerequisite of later
# phases AND routinely produced after long background jobs get an entry; the
# background-job check above applies to every phase regardless.
CONTRACTS: dict[str, str] = {
    "spec_validation": "spec/bug-report.md",
    "bug_confirmation": "spec/confirmed-bugs.md",
}

# Where an agent may declare it cannot finish (checked in order).
BLOCKED_LOCATIONS = ("spec/BLOCKED.md", "BLOCKED.md")

DEFAULT_CAP = 5

# A live process whose start time postdates its pid file by more than this is
# assumed to be a reused pid, not the recorded job.
PID_REUSE_TOLERANCE_S = 300

# Pid-file scan bounds. A TLC hunt's metadir (states/, checkpoints) can hold
# millions of files; an unbounded walk would blow the hook's timeout and
# silently disarm the gate, so prune known-huge dirs and cap depth/volume.
SCAN_EXCLUDE_DIRS = frozenset({".git", "states", ".tlacache", "node_modules", "__pycache__", STATE_DIRNAME})
SCAN_MAX_DEPTH = 5
SCAN_DIR_BUDGET = 2000


# ──────────────────────────────────────────────────────────
# State (per-run, under <work_dir>/.stop-gate/)
# ──────────────────────────────────────────────────────────
def _state_dir(work_dir: Path) -> Path:
    return work_dir / STATE_DIRNAME


def _read_blocks(work_dir: Path) -> int:
    try:
        return int((_state_dir(work_dir) / "blocks").read_text().strip())
    except (OSError, ValueError):
        return 0


def _write_blocks(work_dir: Path, n: int) -> bool:
    """Persist the block counter; False if it couldn't be written (fuse can't
    advance, so the caller must fail open)."""
    try:
        _state_dir(work_dir).mkdir(parents=True, exist_ok=True)
        (_state_dir(work_dir) / "blocks").write_text(f"{n}\n")
        return True
    except OSError:
        return False


def _log(work_dir: Path, msg: str) -> None:
    try:
        _state_dir(work_dir).mkdir(parents=True, exist_ok=True)
        with open(_state_dir(work_dir) / "gate.log", "a") as fh:
            fh.write(f"[{time.strftime('%Y-%m-%d %H:%M:%S')}] {msg}\n")
    except OSError:
        pass


def reset_state(work_dir: Path) -> None:
    """Fresh fuse for a fresh agent run (adapters call this before launching).
    The gate.log audit trail is kept across runs."""
    for name in ("blocks", "FAILED-HOOK-CAP"):
        with contextlib.suppress(OSError):
            (_state_dir(work_dir) / name).unlink()


def _has_content(p: Path) -> bool:
    """True if p is a file with non-whitespace content. A report of only spaces
    is a silent quit, not a deliverable — st_size > 0 would wave it through.
    Raises OSError to the caller (each site handles read failure differently)."""
    return p.is_file() and bool(p.read_text(errors="replace").strip())


def _blocked_file(work_dir: Path) -> Path | None:
    for rel in BLOCKED_LOCATIONS:
        p = work_dir / rel
        try:
            if _has_content(p):
                return p
        except OSError:
            continue
    return None


# ──────────────────────────────────────────────────────────
# Live background jobs (pid files under the work dir)
# ──────────────────────────────────────────────────────────
def _ancestor_pids() -> set[int]:
    """This process's ancestor chain (the phase agent's own adapter/CLI pids
    land in work-dir pid files too — those are not orphaned background jobs).
    Best-effort via /proc; on failure just self + parent."""
    pids = {os.getpid(), os.getppid()}
    try:
        pid = os.getpid()
        for _ in range(32):
            with open(f"/proc/{pid}/stat") as fh:
                stat = fh.read()
            # field 4 (ppid) sits after the parenthesized comm, which may
            # itself contain spaces/parens — split after the LAST ')'.
            ppid = int(stat.rsplit(")", 1)[1].split()[1])
            if ppid <= 1:
                break
            pids.add(ppid)
            pid = ppid
    except (OSError, ValueError, IndexError):
        pass
    return pids


def _alive(pid: int) -> bool:
    try:
        os.kill(pid, 0)
        return True
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    except OSError:
        return False


def _started_long_after(pid: int, pid_file: Path) -> bool:
    """True iff the process started well after its pid file was written —
    i.e. the pid was reused by an unrelated process. On any failure, assume
    it IS the recorded job (block; the fuse bounds the damage)."""
    try:
        with open(f"/proc/{pid}/stat") as fh:
            starttime_ticks = int(fh.read().rsplit(")", 1)[1].split()[19])
        with open("/proc/stat") as fh:
            btime = next(int(ln.split()[1]) for ln in fh if ln.startswith("btime "))
        started = btime + starttime_ticks / os.sysconf("SC_CLK_TCK")
        return started > pid_file.stat().st_mtime + PID_REUSE_TOLERANCE_S
    except (OSError, ValueError, IndexError, StopIteration):
        return False


def _find_pid_files(work_dir: Path) -> list[Path]:
    """Bounded *.pid search: prunes SCAN_EXCLUDE_DIRS, descends at most
    SCAN_MAX_DEPTH levels, and visits at most SCAN_DIR_BUDGET directories."""
    found: list[Path] = []
    root_depth = len(work_dir.parts)
    budget = SCAN_DIR_BUDGET
    try:
        for dirpath, dirnames, filenames in os.walk(work_dir):
            depth = len(Path(dirpath).parts) - root_depth
            if depth >= SCAN_MAX_DEPTH:
                dirnames[:] = []
            else:
                dirnames[:] = sorted(d for d in dirnames if d not in SCAN_EXCLUDE_DIRS)
            found.extend(Path(dirpath) / f for f in filenames if f.endswith(".pid"))
            budget -= 1
            if budget <= 0:
                break
    except OSError:
        pass
    return sorted(found)


def _live_pid_files(work_dir: Path) -> list[tuple[Path, int]]:
    """Pid files under the work dir whose process is still alive.

    Skipped: the gate's own state dir; pid files at the work-dir root (the
    launcher writes the phase agent's OWN pid there — spec-validation.pid
    etc. — and that agent is alive by definition while its hook runs); and
    anything in this process's ancestor chain (same reason, belt-and-braces
    for layouts the root rule misses)."""
    ancestors = _ancestor_pids()
    live: list[tuple[Path, int]] = []
    for pf in _find_pid_files(work_dir):
        if pf.parent == work_dir:
            continue
        try:
            text = pf.read_text().strip().splitlines()[0].strip()
        except (OSError, IndexError):
            continue
        if not text.isdigit():
            continue
        pid = int(text)
        if pid in ancestors or not _alive(pid) or _started_long_after(pid, pf):
            continue
        live.append((pf, pid))
    return live


# ──────────────────────────────────────────────────────────
# The decision
# ──────────────────────────────────────────────────────────
def decide(phase: str, work_dir: Path) -> tuple[bool, str]:
    """(allow, reason). Called at the moment the agent tries to end its turn."""
    if os.environ.get("SPECULA_STOP_GATE", "").lower() == "off":
        return True, "gate disabled (SPECULA_STOP_GATE=off)"
    if not phase or not work_dir.is_dir():
        return True, "no phase context (fail-open)"

    blocked = _blocked_file(work_dir)
    if blocked is not None:
        # Surrender is terminal — but never silent about what it leaves behind.
        reason = f"agent declared failure in {blocked}"
        leftovers = _live_pid_files(work_dir)
        if leftovers:
            jobs = ", ".join(f"{pf} (pid {pid})" for pf, pid in leftovers)
            reason += f"; WARNING: live background job(s) left behind: {jobs}"
        return True, reason

    try:
        cap = int(os.environ.get("SPECULA_STOP_GATE_CAP", "") or DEFAULT_CAP)
    except ValueError:
        cap = DEFAULT_CAP
    blocks = _read_blocks(work_dir)
    if blocks >= cap:
        try:
            _state_dir(work_dir).mkdir(parents=True, exist_ok=True)
            (_state_dir(work_dir) / "FAILED-HOOK-CAP").write_text(
                f"gate blocked {blocks} times without the contract being met; fuse opened\n"
            )
        except OSError:
            pass
        return True, f"fuse open after {blocks} blocks (cap {cap})"

    live = _live_pid_files(work_dir)
    if live:
        jobs = ", ".join(f"{pf} (pid {pid})" for pf, pid in live)
        waiter = SPECULA_ROOT / "scripts" / "infra" / "wait_for_pid.sh"
        return False, (
            f"Background job(s) you started are still running: {jobs}. "
            f"Do NOT stop while they run unobserved — nothing re-invokes you when they finish. "
            f"Wait on each in the foreground now, e.g. "
            f"`bash {waiter} --pid-file {shlex.quote(str(live[0][0]))} --timeout 45m`, "
            f"then harvest the results and finish the phase deliverables. "
            f"If you are genuinely unable to proceed, kill the jobs and write "
            f"{work_dir / BLOCKED_LOCATIONS[0]} describing what you tried and why — "
            f"then you may stop."
        )

    contract = CONTRACTS.get(phase)
    if contract is not None:
        deliverable = work_dir / contract
        try:
            missing = not _has_content(deliverable)
        except OSError:
            missing = True
        if missing:
            return False, (
                f"Phase '{phase}' deliverable is missing or empty: {deliverable}. "
                f"Write it before stopping — an honest report of what ran, what passed, "
                f"and what found nothing is a valid deliverable; do NOT invent results. "
                f"If producing it is genuinely impossible, write "
                f"{work_dir / BLOCKED_LOCATIONS[0]} describing what you tried and why — "
                f"then you may stop."
            )

    return True, "contract satisfied"


# ──────────────────────────────────────────────────────────
# Entry points
# ──────────────────────────────────────────────────────────
def _hook_main(flavor: str) -> int:
    """Shared Stop-hook driver. `claude` and `codex` use the same wire contract
    ({"decision": "block", "reason": ...} on stdout, exit 0); they stay separate
    subcommands so a future protocol divergence has a seam to land in."""
    try:
        payload: Any = json.load(sys.stdin)
    except Exception:
        payload = {}
    phase = os.environ.get("SPECULA_PHASE", "")
    work_dir = Path(os.environ.get("SPECULA_WORK_DIR") or "/nonexistent")

    try:
        allow, reason = decide(phase, work_dir)
    except Exception as e:  # fail-open: a broken gate must never wedge a run
        allow, reason = True, f"gate error ({e.__class__.__name__}: {e})"

    if work_dir.is_dir():
        active = bool(payload.get("stop_hook_active")) if isinstance(payload, dict) else False
        verdict = "allow" if allow else "block"
        _log(work_dir, f"{flavor} phase={phase} {verdict} (stop_hook_active={active}) {reason}")
        if not allow:
            if not _write_blocks(work_dir, _read_blocks(work_dir) + 1):
                allow, reason = True, "gate state unwritable; failing open"

    if not allow:
        json.dump({"decision": "block", "reason": reason}, sys.stdout)
        print()
    return 0


def _orphan_note(work_dir: Path) -> str:
    leftovers = _live_pid_files(work_dir)
    if not leftovers:
        return ""
    return "; live background job(s) left behind: " + ", ".join(f"{pf} (pid {pid})" for pf, pid in leftovers)


def _accept_main(phase: str, work_dir_arg: str) -> int:
    """Acceptance layer: audit the contract after the agent exits.
    Exit 0 = contract satisfied (or no contract for this phase; silent),
    exit 1 = deliverable missing, exit 3 = agent declared failure (BLOCKED.md).
    Fail-open is deliberately narrow here — only the file checks are guarded
    (except OSError); a programming error must crash loudly in tests/CI, not
    turn the audit into a permanent silent OK."""
    work_dir = Path(work_dir_arg)
    blocked = _blocked_file(work_dir)  # swallows I/O errors internally
    contract = CONTRACTS.get(phase)
    if contract is not None:
        deliverable = work_dir / contract
        try:
            delivered = _has_content(deliverable)
        except OSError:
            delivered = True  # unreadable ≠ missing: don't false-alarm
        if delivered:
            return 0
        if blocked is not None:
            print(f"agent declared failure — no {contract}; see {blocked}{_orphan_note(work_dir)}")
            return 3
        try:
            capped = (_state_dir(work_dir) / "FAILED-HOOK-CAP").is_file()
        except OSError:
            capped = False
        suffix = " (stop-gate fuse opened; see .stop-gate/gate.log)" if capped else ""
        print(f"deliverable missing or empty: {contract}{suffix}")
        return 1
    if blocked is not None:
        print(f"agent declared failure; see {blocked}{_orphan_note(work_dir)}")
        return 3
    return 0


def main(argv: list[str]) -> int:
    if len(argv) >= 1 and argv[0] in ("claude", "codex"):
        return _hook_main(argv[0])
    if len(argv) == 3 and argv[0] == "accept":
        return _accept_main(argv[1], argv[2])
    if len(argv) == 2 and argv[0] == "reset":
        # for adapters that are shell scripts (codex.sh) and cannot import this
        reset_state(Path(argv[1]))
        return 0
    print(
        "usage: stop_gate.py claude|codex   (Stop-hook entry; reads hook JSON on stdin)\n"
        "       stop_gate.py accept <phase> <work_dir>\n"
        "       stop_gate.py reset  <work_dir>",
        file=sys.stderr,
    )
    return 2


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
