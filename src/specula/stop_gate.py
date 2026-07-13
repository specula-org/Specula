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
  SPECULA_STOP_GATE_WORK_DIR
                         optional worker-local gate state/PID-scan directory;
                         defaults to SPECULA_WORK_DIR
  SPECULA_STOP_GATE      set to "off" to disable the gate entirely
  SPECULA_STOP_GATE_CAP  blocks allowed per agent run before the fuse opens
                         (default 5; the fuse writes FAILED-HOOK-CAP and lets
                         the stop through so a confused agent can never loop
                         forever)

Per-run state lives under $SPECULA_STOP_GATE_WORK_DIR/.stop-gate/ (block
counter, FAILED-HOOK-CAP marker, gate.log audit trail); adapters reset the
counter and marker when they launch a fresh agent.

Fail-open principle: an internal exception, malformed hook input, or missing
workspace allows the stop. A completed decision that cannot finish PID
discovery is different: it blocks subject to the normal fuse, because silently
assuming an unobserved job ended is the exact failure this gate prevents.

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

# PID-file discovery has two sources. ``start_background.sh`` registers every
# managed job in the worker-local gate state, so a log/PID file may live outside
# the worker directory (or below a pruned TLC metadir) without becoming
# invisible.  We also scan ordinary workspace directories for ad-hoc PID files.
# Known huge/generated trees are pruned, but there is deliberately no fixed
# depth or directory-count limit: repository topology alone must never block a
# healthy stop. A real timeout/read error remains fail-closed, subject to the
# normal fuse.
SCAN_EXCLUDE_DIRS = frozenset({".git", "states", ".tlacache", "node_modules", "__pycache__", STATE_DIRNAME})
BACKGROUND_PID_DIRNAME = "background-pids"
SCAN_TIMEOUT_S = 5.0


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


def _registered_pid_files(state_dir: Path) -> tuple[list[Path], bool]:
    """Return the flat, launcher-managed background PID registry."""
    registry = state_dir / BACKGROUND_PID_DIRNAME
    try:
        if not registry.exists():
            return [], False
        if registry.is_symlink() or not registry.is_dir():
            return [], True
        return sorted(path for path in registry.iterdir() if path.is_file() and path.name.endswith(".pid")), False
    except OSError:
        return [], True


def _is_registered_pid_file(pid_file: Path) -> bool:
    return pid_file.parent.name == BACKGROUND_PID_DIRNAME and pid_file.parent.parent.name == STATE_DIRNAME


def _find_pid_files(work_dir: Path) -> tuple[list[Path], bool]:
    """Find registered and ordinary PID files without topology false blocks.

    Managed background jobs are found through each worker's ``.stop-gate``
    registry even though that state directory is pruned from the ordinary walk.
    The boolean reports only an actual timeout/read failure, never merely a
    deep or broad repository.
    """
    found: list[Path] = []
    incomplete = False
    deadline = time.monotonic() + SCAN_TIMEOUT_S

    def scan_error(_error: OSError) -> None:
        nonlocal incomplete
        incomplete = True

    try:
        for dirpath, dirnames, filenames in os.walk(work_dir, onerror=scan_error):
            if time.monotonic() > deadline:
                incomplete = True
                break
            current = Path(dirpath)
            if STATE_DIRNAME in dirnames:
                registered, registry_incomplete = _registered_pid_files(current / STATE_DIRNAME)
                found.extend(registered)
                incomplete = incomplete or registry_incomplete
            dirnames[:] = sorted(d for d in dirnames if d not in SCAN_EXCLUDE_DIRS)
            found.extend(current / f for f in filenames if f.endswith(".pid"))
    except OSError:
        incomplete = True
    return sorted(set(found)), incomplete


def _live_pid_files(work_dir: Path) -> tuple[list[tuple[Path, int]], bool]:
    """Pid files under the work dir whose process is still alive.

    The gate's own state dir is pruned. Adapter/agent pid files are ignored by
    checking the actual ancestor chain, regardless of where the marker lives;
    unrelated live jobs at the finding root therefore remain visible.
    """
    ancestors = _ancestor_pids()
    live: list[tuple[Path, int]] = []
    pid_files, incomplete = _find_pid_files(work_dir)
    for pf in pid_files:
        registered = _is_registered_pid_file(pf)
        try:
            text = pf.read_text().strip().splitlines()[0].strip()
        except (OSError, IndexError):
            incomplete = incomplete or registered
            continue
        if not text.isdigit():
            incomplete = incomplete or registered
            continue
        pid = int(text)
        if pid in ancestors or not _alive(pid) or _started_long_after(pid, pf):
            continue
        live.append((pf, pid))
    return live, incomplete


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
        leftovers, incomplete = _live_pid_files(work_dir)
        if leftovers:
            jobs = ", ".join(f"{pf} (pid {pid})" for pf, pid in leftovers)
            reason += f"; WARNING: live background job(s) left behind: {jobs}"
        if incomplete:
            reason += "; WARNING: background-job PID scan was incomplete"
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

    live, incomplete = _live_pid_files(work_dir)
    if live:
        jobs = ", ".join(f"{pf} (pid {pid})" for pf, pid in live)
        waiter = SPECULA_ROOT / "scripts" / "infra" / "wait_for_pid.sh"
        waiter_arg = shlex.quote(str(waiter))
        first_pid_file, first_pid = live[0]
        wait_target = (
            f"--pid {first_pid}"
            if _is_registered_pid_file(first_pid_file)
            else f"--pid-file {shlex.quote(str(first_pid_file))}"
        )
        return False, (
            f"Background job(s) you started are still running: {jobs}. "
            f"Do NOT stop while they run unobserved — nothing re-invokes you when they finish. "
            f"Wait on each in the foreground now, e.g. "
            f"`bash {waiter_arg} {wait_target} --timeout 45m`, "
            f"then harvest the results and finish the phase deliverables. "
            f"If you are genuinely unable to proceed, kill the jobs and write "
            f"{work_dir / BLOCKED_LOCATIONS[0]} describing what you tried and why — "
            f"then you may stop."
        )
    if incomplete:
        return False, (
            f"Background-job PID discovery under {work_dir} timed out or hit an unreadable path. "
            "The gate cannot prove that all registered jobs finished, so stopping is blocked. "
            "Wait for the job or record the failure in BLOCKED.md, then try again."
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
    target_work_dir = os.environ.get("SPECULA_WORK_DIR") or "/nonexistent"
    work_dir = Path(os.environ.get("SPECULA_STOP_GATE_WORK_DIR") or target_work_dir)

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
    leftovers, incomplete = _live_pid_files(work_dir)
    if not leftovers and not incomplete:
        return ""
    details: list[str] = []
    if leftovers:
        details.append("live background job(s) left behind: " + ", ".join(f"{pf} (pid {pid})" for pf, pid in leftovers))
    if incomplete:
        details.append("background-job PID scan was incomplete")
    return "; " + "; ".join(details)


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
            orphan = _orphan_note(work_dir)
            if orphan:
                print(f"phase deliverable exists, but completion audit failed{orphan}")
                return 1
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
    orphan = _orphan_note(work_dir)
    if orphan:
        print(f"phase left unfinished background work{orphan}")
        return 1
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
