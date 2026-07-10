#!/usr/bin/env python3
"""Specula phase launchers — Python framework (port of scripts/launch/launch_*.sh).

Each historical `launch_<phase>.sh` spawns one agent per target: parse args,
check prerequisites, build a per-phase prompt that defers to a skill, run the
agent adapter (throttled, in the background), then summarize. This module folds
that shared skeleton into one `Phase` base + a small subclass per phase, so the
`launch_<phase>.sh` scripts become thin shims (`exec python3 phaselib.py <phase>`).

Behavior is a faithful port of the original bash launchers; the phase logic is
covered by tests/unit and the end-to-end CLI chain by tests/e2e.

Usage:  python3 phaselib.py <phase> [options] "<target>" [...]
"""

from __future__ import annotations

import contextlib
import locale
import os
import re
import signal
import subprocess
import sys
import time
from pathlib import Path
from typing import TypedDict

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import specula.progress as progress

SCRIPT_DIR = Path(__file__).resolve().parent  # src/specula
SPECULA_ROOT = SCRIPT_DIR.parent.parent
# the launch_*.sh shims and the agent adapters stay under scripts/launch/
LAUNCH_DIR = SPECULA_ROOT / "scripts" / "launch"

# bash pathname expansion (`for d in .../*/`) orders by the locale collating
# sequence; adopt the ambient locale so find_repo_dir picks the same repo the
# bash launcher did (codepoint sort can order e.g. 'Backup-old' before 'braft'
# where strcoll does the reverse). Falls back to bytewise (C) if unset/invalid.
with contextlib.suppress(locale.Error):
    locale.setlocale(locale.LC_COLLATE, "")


def _ts() -> str:
    """[HH:MM:SS] — mirrors bash `date '+%H:%M:%S'`."""
    return time.strftime("%H:%M:%S")


def _trim(s: str) -> str:
    """Mirror bash `echo "$x" | xargs` word-trim (leading/trailing whitespace)."""
    return s.strip()


def _wc_l(path: Path) -> int:
    """Line count matching bash `wc -l < file` (counts newlines, NOT splitlines —
    they differ by 1 when the file has no trailing newline). Byte-oriented like
    wc: agent-written files aren't guaranteed valid UTF-8, and a summary must
    never crash after the agents already ran."""
    return path.read_bytes().count(b"\n")


def _logical_cwd() -> Path:
    """bash `$PWD`: the logical path (symlink components preserved) when the
    inherited PWD still names the current directory; physical getcwd otherwise
    (bash performs the same same-directory validation at startup)."""
    pwd = os.environ.get("PWD", "")
    if pwd.startswith("/"):
        with contextlib.suppress(OSError):
            if os.path.samefile(pwd, os.curdir):
                return Path(pwd)
    return Path.cwd()


def _grep_num(text: str, prefix: str) -> str:
    """First integer on the first line starting with `prefix`, else '?' — mirrors
    bash `grep -E "^prefix" | grep -oE '[0-9]+' | head -1`."""
    for ln in text.splitlines():
        if ln.startswith(prefix):
            m = re.search(r"\d+", ln)
            return m.group(0) if m else "?"
    return "?"


class AgentFiles(TypedDict):
    """Shape of `Phase.agent_files`: per-agent paths + dirs to create."""

    log: Path
    pid: Path
    prompt: Path
    mkdirs: list[Path]


class Workspace:
    """Path resolution for a run.

    Legacy (no `SPECULA_RUN_DIR`): faithful to the bash `get_work_dir` /
    `find_repo_dir` — single-target writes to `$PWD/.specula-output`; batch to
    `$PWD/<name>/.specula-output`.

    Isolated (`SPECULA_RUN_DIR` set, step 4 workspace control): every output
    lands under `<run>/<name>/.specula-output` — uniform batch-style layout,
    single/batch no longer fork — and canonical *inputs* (artifact checkout,
    .prompt-extra.md) fall back to `case-studies/<name>` since no cd into the
    case directory happens anymore.
    """

    def __init__(
        self,
        targets: list[str],
        artifact: str = "",
        cwd: Path | None = None,
        opts: dict[str, str | bool] | None = None,
    ) -> None:
        self.targets = targets
        self.artifact = artifact
        self.cwd = Path(cwd) if cwd else _logical_cwd()  # bash $PWD, not the physical getcwd
        self.single = len(targets) == 1
        # phase-specific run options (e.g. validation --repair, confirmation --recheck)
        self.opts = opts or {}
        run_dir = os.environ.get("SPECULA_RUN_DIR", "")
        self.run_dir: Path | None = Path(run_dir) if run_dir else None

    def work_dir(self, name: str) -> Path:
        if self.run_dir:
            return self.run_dir / name / ".specula-output"
        if self.single:
            return self.cwd / ".specula-output"
        return self.cwd / name / ".specula-output"

    def case_dir(self, name: str) -> Path:
        """Canonical `case-studies/<name>` — the fallback root for canonical
        inputs when the run is isolated (the legacy flow reached these via the
        single-target cd)."""
        return SPECULA_ROOT / "case-studies" / name

    @staticmethod
    def _repo_under(artifact_dir: Path) -> str:
        """First `<artifact_dir>/<repo-with-.git>/` (bash keeps the trailing slash)."""
        if artifact_dir.is_dir():
            for d in sorted(artifact_dir.iterdir(), key=lambda p: locale.strxfrm(p.name)):
                # bash `for d in "$artifact_dir"/*/` — the glob never matches
                # dotdirs, so a hidden .git-bearing dir (stale backup, tool
                # cache) must not shadow the real repo.
                if d.name.startswith("."):
                    continue
                if d.is_dir() and (d / ".git").exists():
                    return str(d) + "/"
        return ""

    def find_repo_dir(self, name: str) -> str:
        # Explicit --artifact wins.
        if self.artifact:
            return self.artifact
        if self.run_dir:
            # Isolated: the run root holds no sources, so neither the batch
            # cwd search nor the single-target "source is $PWD" rule applies —
            # only the canonical checkout can supply the repo.
            return self._repo_under(self.case_dir(name) / "artifact")
        found = self._repo_under(self.cwd / name / "artifact")
        if found:
            return found
        # Single target: source is $PWD.
        if self.single:
            return str(self.cwd)
        return ""


class Phase:
    """Base launcher. Subclasses set the per-phase specifics; `run` is shared."""

    key = ""  # cli name (e.g. "code_analysis")
    title = ""  # banner title
    usage = ""  # --help text: the bash launcher's header comment, extracted verbatim
    check_header = "Checking prerequisites..."
    check_fail_msg = "ERROR: Missing prerequisites."
    check_ok_msg = "All prerequisites OK."  # code_analysis says "All repos OK."
    accepts_artifact = True  # bug_classification takes no --artifact (rejects it)
    dry_prompt_flag = "--prompt"  # bug_classification's dry-run line shows --prompt-file
    progress_config = progress.ProgressConfig()

    # ── per-phase hooks ──
    def parse_flag(self, arg: str, extra: dict[str, str | bool]) -> bool:
        """Consume a phase-specific flag into `extra`; return True if handled.
        Override for extra flags (validation --repair; confirmation --recheck /
        --max-repair-rounds). `extra` is exposed to hooks as `ws.opts`."""
        return False

    def target_name(self, target: str) -> str:
        """Extract the display/work name from a target string. Downstream phases
        get name-only targets, so the whole (trimmed) string is the name;
        code_analysis overrides this to split the 'name|github|lang|ref' form."""
        return _trim(target)

    def check(self, ws: Workspace, names: list[str]) -> bool:
        """Print a per-target prerequisite line; return True iff all satisfied."""
        raise NotImplementedError

    def agent_files(self, ws: Workspace, name: str) -> AgentFiles:
        """Return {log, pid, prompt, mkdir} paths for this phase's agent run."""
        raise NotImplementedError

    def build_prompt(self, ws: Workspace, target: str) -> str:
        raise NotImplementedError

    def summarize(self, ws: Workspace, names: list[str]) -> None:
        raise NotImplementedError

    def monitor_line(self, ws: Workspace) -> str | None:
        """The '  Monitor: tail -f ...' hint printed once after all agents launch
        (per-phase; code_analysis prints none). Legacy is faithful to each bash
        launcher's hand-written glob — quirks and all: some omit the
        .specula-output/ segment, and spec_validation uses an absolute ${PWD}
        path. Isolated runs re-root the glob under the run dir (see _monitor)."""
        return None

    def _monitor(self, ws: Workspace, logname: str, legacy: str) -> str:
        """Monitor hint. Isolated (SPECULA_RUN_DIR set): an accurate run-rooted
        glob — the legacy relative `*/` points at the launch cwd, which an
        isolated run no longer writes to. Legacy: the bash launcher's original
        string, verbatim."""
        if ws.run_dir:
            return f"  Monitor: tail -f {ws.run_dir}/*/.specula-output/{logname}"
        return legacy

    def _reap_agents(
        self, running: list[progress.RunningAgent], show_progress: bool
    ) -> tuple[list[progress.RunningAgent], list[tuple[str, int]]]:
        """Drop completed children and return their nonzero exit statuses."""
        live: list[progress.RunningAgent] = []
        failures: list[tuple[str, int]] = []
        for agent in running:
            rc = agent.proc.poll()
            if rc is None:
                live.append(agent)
            else:
                if rc != 0:
                    failures.append((agent.name, rc))
            if rc is not None and show_progress:
                print(f"[{_ts()}] {agent.name}: completed (exit {rc})")
        return live, failures

    @staticmethod
    def _terminate_agents(running: list[progress.RunningAgent]) -> None:
        live = [agent for agent in running if agent.proc.poll() is None]
        if not live:
            return
        print(f"\n[{_ts()}] Interrupt received; stopping {len(live)} agent(s)...")
        for agent in live:
            with contextlib.suppress(ProcessLookupError):
                os.killpg(agent.proc.pid, signal.SIGTERM)
        deadline = time.monotonic() + 2.0
        while time.monotonic() < deadline and any(agent.proc.poll() is None for agent in live):
            time.sleep(0.05)
        for agent in live:
            if agent.proc.poll() is None:
                with contextlib.suppress(ProcessLookupError):
                    os.killpg(agent.proc.pid, signal.SIGKILL)
            with contextlib.suppress(subprocess.TimeoutExpired):
                agent.proc.wait(timeout=0.5)

    @staticmethod
    def _failure_code(failures: list[tuple[str, int]]) -> int:
        if not failures:
            return 0
        rc = failures[0][1]
        return 128 - rc if rc < 0 else rc

    # ── shared prompt-extra injection (identical across phases) ──
    def _read_prompt_extra(self, ws: Workspace, name: str) -> str:
        """The target's .prompt-extra.md as an appendable block (with its section
        header), or '' if none. Isolated runs never cd into the case dir, so the
        cwd fallback would silently drop the canonical case-studies/<name> extra —
        target-specific instructions must survive isolation."""
        extra = ws.work_dir(name) / ".prompt-extra.md"
        if not extra.is_file():
            fallback = ws.case_dir(name) if ws.run_dir else ws.cwd
            extra = fallback / ".prompt-extra.md"
        if extra.is_file():
            # errors="replace": bash `cat` concatenated raw bytes; a stray
            # non-UTF-8 byte in a user's .prompt-extra.md must not crash the run.
            return "\n## Target-Specific Instructions\n\n" + extra.read_text(errors="replace")
        return ""

    def _with_extra(self, ws: Workspace, name: str, prompt: str) -> str:
        return prompt + self._read_prompt_extra(ws, name)

    # ── shared driver ──
    def run(self, argv: list[str]) -> int:
        max_parallel = 1
        max_turns = "0"
        dry_run = False
        check_only = False
        agent = "claude-code"
        # `or`: bash ${CLAUDE_ALIAS:-claude} treats an exported-but-empty var as unset
        claude_alias = os.environ.get("CLAUDE_ALIAS") or "claude"
        artifact = ""
        targets: list[str] = []
        extra: dict[str, str | bool] = {}

        for arg in argv:
            if arg == "--dry-run":
                dry_run = True
            elif arg == "--check":
                check_only = True
            elif arg.startswith("--max-parallel="):
                val = arg[len("--max-parallel=") :]
                try:
                    max_parallel = int(val)
                except ValueError:
                    # bash never validated this; a garbage value hung its throttle
                    # loop forever (empty crashed the arithmetic mid-run). Fail fast
                    # instead — pinned by bad_max_parallel_code_analysis.
                    print(f"Invalid --max-parallel: '{val}' (expected an integer)")
                    return 1
                if max_parallel < 1:
                    print(f"Invalid --max-parallel: '{val}' (expected an integer >= 1)")
                    return 1
            elif arg.startswith("--max-turns="):
                # Deprecated passthrough the adapter ignores. bash forwarded it
                # verbatim, so keep it a string: `--max-turns=$VAR` with VAR unset
                # or non-numeric must not crash the launcher.
                max_turns = arg[len("--max-turns=") :]
            elif arg.startswith("--agent="):
                agent = arg[len("--agent=") :]
            elif arg.startswith("--claude-alias="):
                claude_alias = arg[len("--claude-alias=") :]
            elif arg.startswith("--artifact=") and self.accepts_artifact:
                artifact = arg[len("--artifact=") :]
            elif arg in ("--help", "-h"):
                sys.stdout.write(self.usage)
                return 0
            elif self.parse_flag(arg, extra):
                pass
            elif arg.startswith("-"):
                print(f"Unknown option: {arg}")
                return 1
            else:
                targets.append(arg)

        if not targets:
            targets = [_logical_cwd().name]  # bash `basename "$PWD"` (logical under symlinks)

        adapter = LAUNCH_DIR / "adapters" / f"{agent}.sh"
        if not adapter.is_file():
            print(f"ERROR: Unknown agent '{agent}' — adapter not found at {adapter}")
            return 1

        ws = Workspace(targets, artifact=artifact, opts=extra)
        names = [self.target_name(t) for t in targets]

        print("========================================")
        print(f" {self.title}")
        print("========================================")
        print(f"Targets:      {len(targets)}")
        print(f"Max parallel: {max_parallel}")
        print(f"Max turns:    {max_turns}")
        print()

        print(self.check_header)
        if not self.check(ws, names):
            print()
            print(self.check_fail_msg)
            return 1
        print()

        if check_only:
            print(self.check_ok_msg)
            return 0

        # A phase may take over its own per-target execution (e.g. parallel
        # per-finding bug confirmation) instead of the default single-agent
        # `_launch` loop below. None = fall through to the single-agent loop.
        alt = self.run_alternate(
            ws,
            names,
            adapter=adapter,
            claude_alias=claude_alias,
            max_parallel=max_parallel,
            dry_run=dry_run,
        )
        if alt is not None:
            return alt

        show_progress = progress.enabled()
        running: list[progress.RunningAgent] = []
        failures: list[tuple[str, int]] = []
        try:
            for target in targets:
                name = self.target_name(target)
                prompt = self.build_prompt(ws, target)
                # Throttle.
                while len(running) >= max_parallel:
                    if show_progress:
                        progress.report(running, self.progress_config)
                    running, completed_failures = self._reap_agents(running, show_progress)
                    failures.extend(completed_failures)
                    if len(running) >= max_parallel:
                        time.sleep(self.progress_config.poll_seconds)
                proc = self._launch(ws, name, prompt, dry_run, max_turns, claude_alias, adapter)
                if not dry_run and proc is not None:
                    running.append(proc)
                print()

            if not dry_run:
                print(f"[{_ts()}] All agents launched. Waiting...")
                monitor = self.monitor_line(ws)
                if monitor is not None:
                    print(monitor)
                print()
                while running:
                    if show_progress:
                        progress.report(running, self.progress_config)
                    running, completed_failures = self._reap_agents(running, show_progress)
                    failures.extend(completed_failures)
                    if running:
                        time.sleep(self.progress_config.poll_seconds)
                print(f"[{_ts()}] All agents completed.")
        except BaseException:
            self._terminate_agents(running)
            raise

        self.summarize(ws, names)
        if not dry_run:
            self._acceptance(ws, names)
        if failures:
            print()
            print("Agent failures:")
            for name, rc in failures:
                print(f"  FAILED  {name}: adapter exited {rc}")
        return self._failure_code(failures)

    def run_alternate(
        self,
        ws: Workspace,
        names: list[str],
        *,
        adapter: Path,
        claude_alias: str,
        max_parallel: int,
        dry_run: bool,
    ) -> int | None:
        """Hook: let a phase run its targets its own way instead of the default
        single-agent `_launch` loop. Return an exit code to mean "handled, stop
        here"; return None (the default) to fall through to the single-agent
        loop. Overridden by BugConfirmationPhase for parallel per-finding
        confirmation."""
        return None

    # ── acceptance layer (stop gate) ──
    def _acceptance(self, ws: Workspace, names: list[str]) -> None:
        """Audit each target's phase contract after the agents exit: deliverable
        present, or an explicit BLOCKED.md declaring failure. Alarm-only by
        design — the exit code stays 0 (downstream prerequisite gates still stop
        the pipeline); this makes a slipped-through failure loud instead of a
        silent all-OK summary. Contract lives in src/specula/stop_gate.py."""
        gate = SPECULA_ROOT / "src" / "specula" / "stop_gate.py"
        failures: list[tuple[str, str]] = []
        for name in names:
            try:
                r = subprocess.run(
                    [sys.executable, str(gate), "accept", self.key, str(ws.work_dir(name))],
                    capture_output=True,
                    text=True,
                )
            except OSError:
                continue  # fail-open for THIS target only; still audit the rest
            if r.returncode != 0:
                failures.append((name, (r.stdout or r.stderr).strip()))
        if failures:
            print()
            print("Acceptance gate:")
            for name, msg in failures:
                print(f"  FAILED  {name}: {msg}")

    def _launch(
        self,
        ws: Workspace,
        name: str,
        prompt: str,
        dry_run: bool,
        max_turns: str,
        claude_alias: str,
        adapter: Path,
    ) -> progress.RunningAgent | None:
        files = self.agent_files(ws, name)
        for d in files["mkdirs"]:
            d.mkdir(parents=True, exist_ok=True)
        files["prompt"].write_text(prompt)
        print(f"[{_ts()}] Launching agent: {name}")
        if dry_run:
            print(
                f"  [DRY RUN] {adapter} {self.dry_prompt_flag}=<prompt> "
                f"--max-turns={max_turns} --log={files['log']} --background"
            )
            print(f"  Prompt saved: {files['prompt']}")
            return None
        # Generic stop-gate interface (src/specula/stop_gate.py): tell the
        # adapter which phase this agent runs and where its work dir is, so
        # hook-capable adapters arm the completion gate. Per-launch env copy,
        # not os.environ: targets differ under --max-parallel.
        env = os.environ.copy()
        env["SPECULA_PHASE"] = self.key
        env["SPECULA_WORK_DIR"] = str(ws.work_dir(name))
        work_dir = ws.work_dir(name)
        activity_sidecar = files["log"].with_suffix(".activity.jsonl")
        with contextlib.suppress(OSError):
            activity_sidecar.unlink()
        # SPECULA_PROGRESS=off is a full opt-out, not a mute: without the sidecar
        # the adapters fall back to their legacy argv (`--output-format json`, no
        # `codex --json`, no copilot `--stream on`) and the legacy result-only
        # agent.log. A CLI that predates the streaming flags would otherwise have
        # no escape hatch — and an adapter failure now aborts the whole run.
        env.pop("SPECULA_ACTIVITY_LOG", None)
        if progress.enabled():
            env["SPECULA_ACTIVITY_LOG"] = str(activity_sidecar)
        # Do not report launcher plumbing as agent work. The generic adapter
        # contract derives raw/usage data from the .log stem, so ignore those
        # files as well when they live in the workspace.
        runtime_files = (
            files["prompt"],
            files["pid"],
            files["log"],
            activity_sidecar,
            files["log"].with_suffix(".raw.json"),
            files["log"].with_suffix(".usage.json"),
        )
        ignored: set[Path] = set()
        for path in runtime_files:
            with contextlib.suppress(ValueError):
                ignored.add(path.relative_to(work_dir))
        snapshot = progress.workspace_snapshot(work_dir, ignored)
        started_at = time.monotonic()
        prelaunch_log_stamp = progress.file_stamp(files["log"])
        activity_log = activity_sidecar
        prelaunch_activity_stamp = progress.file_stamp(activity_log)
        proc = subprocess.Popen(
            [
                str(adapter),
                f"--prompt-file={files['prompt']}",
                f"--max-turns={max_turns}",
                f"--claude-alias={claude_alias}",
                "--effort=max",
                f"--log={files['log']}",
                "--background",
            ],
            env=env,
            start_new_session=True,
        )
        files["pid"].write_text(f"{proc.pid}\n")
        print(f"  PID={proc.pid}  Log: {files['log']}")
        return progress.RunningAgent(
            name=name,
            proc=proc,
            work_dir=work_dir,
            log=files["log"],
            activity_log=activity_log,
            ignored=ignored,
            snapshot=snapshot,
            reported_snapshot=snapshot,
            last_observed_at=started_at,
            log_stamp=prelaunch_log_stamp,
            activity_stamp=prelaunch_activity_stamp,
            adapter_name=adapter.stem,
        )


def run_agent_blocking(
    adapter: Path,
    prompt: str,
    prompt_file: Path,
    log_file: Path,
    *,
    phase_key: str,
    work_dir: Path,
    claude_alias: str,
    max_turns: str = "0",
    stop_gate: bool = False,
) -> tuple[int, str]:
    """Run ONE agent invocation, blocking, and return (returncode, log text).

    The blocking sibling of `Phase._launch`: it shares the same adapter path, the
    same flag set (`--prompt-file` / `--max-turns` / `--claude-alias` /
    `--effort=max` / `--log`), and the same stop-gate env keys
    (`SPECULA_PHASE` / `SPECULA_WORK_DIR`) — but drops `--background` so the
    caller can read the result before issuing the next turn. That is the shape a
    per-finding confirmation debate needs (turn N+1 reads turn N's output),
    which the fire-all-then-wait `_launch` loop cannot express.

    The completion stop-gate is OFF per turn by default: it audits a *phase*
    deliverable (`confirmed-bugs.md`) that exists only after all findings are
    aggregated, never after a single turn; the phase-level acceptance check
    (`Phase._acceptance`) covers it once at the end. Rate-limit (exit 75) is the
    caller's concern — this runs exactly one invocation.
    """
    prompt_file.parent.mkdir(parents=True, exist_ok=True)
    prompt_file.write_text(prompt)
    env = os.environ.copy()
    env["SPECULA_PHASE"] = phase_key
    env["SPECULA_WORK_DIR"] = str(work_dir)
    if not stop_gate:
        env["SPECULA_STOP_GATE"] = "off"
    cmd = [
        str(adapter),
        f"--prompt-file={prompt_file}",
        f"--max-turns={max_turns}",
        f"--claude-alias={claude_alias}",
        "--effort=max",
        f"--log={log_file}",
    ]
    rc = subprocess.run(cmd, env=env).returncode
    text = log_file.read_text(errors="replace") if log_file.is_file() else ""
    return rc, text


class CodeAnalysisPhase(Phase):
    key = "code_analysis"
    title = "Specula — Code Analysis Batch Runner"
    usage = r"""
Batch launcher: spawn one agent per target system for code analysis.
Each agent follows the code-analysis skill methodology and produces a modeling brief.

Usage:
  bash scripts/launch/launch_code_analysis.sh [options] "name|github|lang|reference" [...]

Single-target (run from your project directory):
  cd my-project
  bash ~/Specula/scripts/launch/launch_code_analysis.sh "myproject|me/myproject|Go|Raft"

Batch (run from a directory containing multiple targets):
  cd case-studies
  bash ../scripts/launch/launch_code_analysis.sh \
    "braft|brpc/braft|C++|Raft (Ongaro 2014)" \
    "sofa-jraft|sofastack/sofa-jraft|Java|Raft (Ongaro 2014)"

Options:
  --dry-run           Print commands without executing
  --check             Only verify repos exist
  --max-parallel=N    Max concurrent agents (default: 1)
  --max-turns=N       Max agent turns (default: 0 = unlimited)
  --agent=NAME        Agent adapter to use (default: claude-code)
  --claude-alias=NAME Claude CLI profile (default: claude)
  --artifact=PATH     Source code path (default: $PWD for single target,
                      $PWD/<name>/artifact/<repo>/ for batch)

"""
    check_header = "Checking repositories..."
    check_fail_msg = (
        "ERROR: Some repositories are missing. Use --artifact=<path> or place repos under <name>/artifact/<repo>/."
    )
    check_ok_msg = "All repos OK."

    def target_name(self, target: str) -> str:
        # code_analysis targets are "name|github|lang|reference"; name is field 1.
        return _trim(target.split("|", 1)[0])

    def check(self, ws: Workspace, names: list[str]) -> bool:
        ok = True
        for name in names:
            repo_dir = ws.find_repo_dir(name)
            if repo_dir:
                # --artifact is returned verbatim (may not exist); mirror bash
                # `cd "$repo_dir" && git ... || echo "?"` — degrade to "?" on a
                # bad/unreadable path instead of crashing on subprocess cwd.
                commits = "?"
                if Path(repo_dir).is_dir():
                    r = subprocess.run(
                        ["git", "rev-list", "--count", "HEAD"],
                        cwd=repo_dir,
                        capture_output=True,
                        text=True,
                    )
                    if r.returncode == 0:
                        commits = r.stdout.strip()
                print(f"  OK  {name} ({commits} commits)")
            else:
                print(f"  MISSING  {name} — use --artifact=<path> or place repo at {name}/artifact/<repo>/")
                ok = False
        return ok

    def agent_files(self, ws: Workspace, name: str) -> AgentFiles:
        wd = ws.work_dir(name)
        return {"log": wd / "agent.log", "pid": wd / "agent.pid", "prompt": wd / ".prompt.md", "mkdirs": [wd]}

    def build_prompt(self, ws: Workspace, target: str) -> str:
        # maxsplit=3: bash `IFS='|' read -r name github lang reference` folds any
        # further '|'-separated content (pipes included) into the reference field.
        parts = [_trim(x) for x in target.split("|", 3)]
        parts += [""] * (4 - len(parts))
        name, github, language, reference = parts[0], parts[1], parts[2], parts[3]
        repo_dir = ws.find_repo_dir(name)
        work_dir = ws.work_dir(name)
        prompt = f"""# Code Analysis Task

You are analyzing the following system:

- **Name**: {name}
- **GitHub**: {github}
- **Language**: {language}
- **Reference Algorithm**: {reference}
- **Repository**: {repo_dir}
- **Working Directory**: {work_dir}

## Instructions

Follow the **code-analysis** skill exactly — it is the single source of methodology (its 4 phases, references, rules, bug-family modeling-brief format, and Category A/B handling). Read and execute it in full:
  {SPECULA_ROOT}/.claude/skills/code_analysis/guide.md

Do everything the skill specifies. Do not add, relax, or override any step here.

## Output

Write your outputs to:
- `{work_dir}/modeling-brief.md` — The primary deliverable (handoff to Spec Generation)
- `{work_dir}/analysis-report.md` — Detailed audit trail of all findings
"""
        return self._with_extra(ws, name, prompt)

    def summarize(self, ws: Workspace, names: list[str]) -> None:
        print()
        print("========================================")
        print(" Results")
        print("========================================")
        for name in names:
            wd = ws.work_dir(name)
            brief = wd / "modeling-brief.md"
            report = wd / "analysis-report.md"
            if brief.is_file():
                n = _wc_l(brief)
                print(f"  OK  {name} -> modeling-brief.md ({n} lines)")
            elif report.is_file():
                n = _wc_l(report)
                print(f"  ~~  {name} -> analysis-report.md only ({n} lines, no modeling brief)")
            else:
                print(f"  --  {name} (no output)")


class SpecGenerationPhase(Phase):
    key = "spec_generation"
    title = "Specula — Spec Generation Batch Runner"
    usage = r"""
Batch launcher: spawn one Claude Code agent per target system for TLA+ spec generation.
Each agent follows the spec-generation skill methodology and produces base/MC/Trace specs.

Usage:
  bash scripts/launch/launch_spec_generation.sh [options] "name" [...]

Example:
  bash scripts/launch/launch_spec_generation.sh cometbft
  bash scripts/launch/launch_spec_generation.sh braft sofa-jraft dragonboat

Options:
  --dry-run           Print commands without executing
  --check             Only verify prerequisites exist
  --max-parallel=N    Max concurrent agents (default: 1)
  --max-turns=N       Max agent turns (default: 0 = unlimited)
  --agent=NAME        Agent adapter to use (default: claude-code)
  --claude-alias=NAME Claude CLI profile (default: claude)
  --artifact=PATH     Explicit path to the artifact repo (bypasses auto-detection)

Prerequisites:
  - claude CLI installed and authenticated
  - modeling-brief.md exists at <name>/.specula-output/modeling-brief.md
  - Source repo cloned at <name>/artifact/<repo>/ (or supplied via --artifact)

"""
    check_header = "Checking prerequisites..."
    check_fail_msg = "ERROR: Missing prerequisites. Run code analysis first."

    def check(self, ws: Workspace, names: list[str]) -> bool:
        ok = True
        for name in names:
            brief = ws.work_dir(name) / "modeling-brief.md"
            repo_dir = ws.find_repo_dir(name)
            if brief.is_file():
                lines = _wc_l(brief)
                line = f"  {name:<20} modeling-brief.md ({lines} lines)"
            else:
                line = f"  {name:<20} MISSING modeling-brief.md"
                ok = False
            line += "  repo OK" if repo_dir else "  repo MISSING"
            if not repo_dir:
                ok = False
            print(line)
        return ok

    def agent_files(self, ws: Workspace, name: str) -> AgentFiles:
        wd = ws.work_dir(name)
        return {
            "log": wd / "spec-gen.log",
            "pid": wd / "spec-gen.pid",
            "prompt": wd / ".spec-gen-prompt.md",
            "mkdirs": [wd / "spec"],
        }

    def build_prompt(self, ws: Workspace, target: str) -> str:
        name = self.target_name(target)
        wd = ws.work_dir(name)
        spec_dir = wd / "spec"
        brief = wd / "modeling-brief.md"
        repo_dir = ws.find_repo_dir(name)
        prompt = f"""# TLA+ Spec Generation Task

You are generating a TLA+ specification for: **{name}**

## Inputs

- **Modeling Brief**: {brief}
- **Source Code**: {repo_dir}
- **Output Directory**: {spec_dir}

## Instructions

Follow the **spec-generation** skill exactly — it is the single source of methodology (its phases, references, rules, Category A/B handling, and the mandatory brief-coverage self-audit). Read and execute it in full:
  {SPECULA_ROOT}/.claude/skills/spec_generation/guide.md

Do everything the skill specifies. Do not add, relax, or override any step here.

## Output

Create the output directory and write all files to:
  {spec_dir}/

Expected files:
- `{spec_dir}/base.tla` — Base specification
- `{spec_dir}/base.cfg` — Base config
- `{spec_dir}/MC.tla` — Model checking specification
- `{spec_dir}/MC.cfg` — Model checking config
- `{spec_dir}/brief-coverage.md` — Coverage audit mapping brief §2/§5/§6.1 to hunt cfgs and invariants
- `{spec_dir}/Trace.tla` — Trace validation specification
- `{spec_dir}/Trace.cfg` — Trace validation config
- `{spec_dir}/instrumentation-spec.md` — Instrumentation mapping
"""
        return self._with_extra(ws, name, prompt)

    def summarize(self, ws: Workspace, names: list[str]) -> None:
        print()
        print("========================================")
        print(" Results")
        print("========================================")
        for name in names:
            spec_dir = ws.work_dir(name) / "spec"
            base = spec_dir / "base.tla"
            mc = spec_dir / "MC.tla"
            trace = spec_dir / "Trace.tla"
            instr = spec_dir / "instrumentation-spec.md"
            count = sum(f.is_file() for f in (base, mc, trace, instr))
            if count == 4:
                n = _wc_l(base)
                print(f"  OK  {name} -> {count}/4 files (base.tla: {n} lines)")
            elif count > 0:
                print(f"  ~~  {name} -> {count}/4 files (incomplete)")
                if not base.is_file():
                    print("        missing: base.tla")
                if not mc.is_file():
                    print("        missing: MC.tla")
                if not trace.is_file():
                    print("        missing: Trace.tla")
                if not instr.is_file():
                    print("        missing: instrumentation-spec.md")
            else:
                print(f"  --  {name} (no output)")

    def monitor_line(self, ws: Workspace) -> str | None:
        return self._monitor(ws, "spec-gen.log", "  Monitor: tail -f */.specula-output/spec-gen.log")


class HarnessGenerationPhase(Phase):
    key = "harness_generation"
    title = "Specula — Harness Generation (Phase 2.5)"
    usage = r"""
Batch launcher: spawn one Claude Code agent per target system for harness generation (Phase 2.5).
Each agent instruments the source code and collects NDJSON traces for spec validation.

Usage:
  bash scripts/launch/launch_harness_generation.sh [options] "name" [...]

Example:
  bash scripts/launch/launch_harness_generation.sh cometbft
  bash scripts/launch/launch_harness_generation.sh braft sofa-jraft dragonboat
  bash scripts/launch/launch_harness_generation.sh --artifact=/path/to/repo myproject

Options:
  --dry-run           Print commands without executing
  --check             Only verify prerequisites exist
  --max-parallel=N    Max concurrent agents (default: 1)
  --max-turns=N       Max agent turns (default: 0 = unlimited)
  --agent=NAME        Agent adapter to use (default: claude-code)
  --claude-alias=NAME Claude CLI profile (default: claude)
  --artifact=PATH     Explicit path to artifact repo (overrides auto-detection)

Prerequisites:
  - claude CLI installed and authenticated
  - Phase 2 complete: spec/base.tla, spec/Trace.tla, spec/instrumentation-spec.md
  - Source repo at <name>/artifact/<repo>/ or specified via --artifact

"""
    check_header = "Checking prerequisites..."
    check_fail_msg = "ERROR: Missing prerequisites. Run spec generation (Phase 2) first."

    def check(self, ws: Workspace, names: list[str]) -> bool:
        ok = True
        for name in names:
            spec_dir = ws.work_dir(name) / "spec"
            repo_dir = ws.find_repo_dir(name)
            line = f"  {name:<20}"
            if (spec_dir / "base.tla").is_file() and (spec_dir / "Trace.tla").is_file():
                line += "specs OK"
            else:
                line += "specs MISSING"
                ok = False
            if (spec_dir / "instrumentation-spec.md").is_file():
                line += "  instr OK"
            else:
                line += "  instr MISSING"
                ok = False
            line += "  repo OK" if repo_dir else "  repo MISSING"
            if not repo_dir:
                ok = False
            print(line)
        return ok

    def agent_files(self, ws: Workspace, name: str) -> AgentFiles:
        wd = ws.work_dir(name)
        return {
            "log": wd / "harness-gen.log",
            "pid": wd / "harness-gen.pid",
            "prompt": wd / ".harness-gen-prompt.md",
            "mkdirs": [wd / "harness", wd / "traces"],
        }

    def build_prompt(self, ws: Workspace, target: str) -> str:
        name = self.target_name(target)
        wd = ws.work_dir(name)
        spec_dir = wd / "spec"
        repo_dir = ws.find_repo_dir(name)
        prompt = f"""# Trace Harness Generation Task: {name}

You are generating a trace harness for **{name}** — instrumenting the real source code to produce NDJSON traces for TLA+ trace validation.

## Inputs

- **Instrumentation spec**: {spec_dir}/instrumentation-spec.md
- **Trace spec**: {spec_dir}/Trace.tla + {spec_dir}/Trace.cfg
- **Base spec**: {spec_dir}/base.tla (for understanding spec actions)
- **Source code**: {repo_dir}

## Workflow

Follow the **harness-generation** skill exactly — it is the single source of methodology (instrument real code, trace format, run.sh, end-to-end validation). Read and execute it in full:
  {SPECULA_ROOT}/.claude/skills/harness-generation/guide.md

Do everything the skill specifies. Do not add, relax, or override any step here.

## Output

Write all harness files to: {wd}/harness/
Collect traces to: {wd}/traces/

Expected outputs:
- `{wd}/harness/src/` — Trace emission module + test scenarios
- `{wd}/harness/apply.sh` — Apply instrumentation to artifact
- `{wd}/harness/run.sh` — One-command build + run + collect traces
- `{wd}/harness/INSTRUMENTATION.md` — Guide for Phase 3 agent to adjust instrumentation
- `{wd}/traces/*.ndjson` — Trace files from test runs
"""
        return self._with_extra(ws, name, prompt)

    def summarize(self, ws: Workspace, names: list[str]) -> None:
        print()
        print("========================================")
        print(" Results")
        print("========================================")
        for name in names:
            wd = ws.work_dir(name)
            harness_dir = wd / "harness"
            traces_dir = wd / "traces"
            has_run = (harness_dir / "run.sh").is_file()
            has_guide = (harness_dir / "INSTRUMENTATION.md").is_file()
            trace_count = len(list(traces_dir.rglob("*.ndjson"))) if traces_dir.is_dir() else 0
            if has_run and trace_count > 0:
                print(f"  OK  {name} -> run.sh: yes, traces: {trace_count}")
                if not has_guide:
                    print("        warning: missing INSTRUMENTATION.md")
            elif has_run:
                print(f"  ~~  {name} -> run.sh: yes, traces: 0 (no traces generated)")
            else:
                print(f"  --  {name} (no harness output)")

    def monitor_line(self, ws: Workspace) -> str | None:
        return self._monitor(ws, "harness-gen.log", "  Monitor: tail -f */.specula-output/harness-gen.log")


class BugClassificationPhase(Phase):
    key = "bug_classification"
    title = "Specula — Bug Classification Batch Runner"
    usage = r"""
Batch launcher: spawn one Claude Code agent per target system for Phase 4b
severity classification. Each agent reads the confirmed-bugs.md produced by
Phase 4a (bug-confirmation) and writes a separate bug-severity.md table
assigning Critical / High / Medium / Low per bug. No new analysis, no repro
work, no modification to confirmed-bugs.md.

Usage:
  bash scripts/launch/launch_bug_classification.sh [options] "name" [...]

Example:
  bash scripts/launch/launch_bug_classification.sh libgomp_3 autobahn_3

Options:
  --dry-run           Print commands without executing
  --check             Only verify prerequisites exist
  --max-parallel=N    Max concurrent agents (default: 1)
  --max-turns=N       Max agent turns (default: 0 = unlimited)
  --agent=NAME        Agent adapter to use (default: claude-code)
  --claude-alias=NAME Claude CLI profile (default: claude)

Prerequisites:
  - Confirmed bug report at <name>/spec/confirmed-bugs.md (from Phase 4a)

"""
    check_header = "Checking prerequisites..."
    check_fail_msg = "ERROR: Missing prerequisites. Run Phase 4a (launch_bug_confirmation.sh) first."
    accepts_artifact = False  # this launcher takes no --artifact
    dry_prompt_flag = "--prompt-file"  # its dry-run line shows --prompt-file=<prompt>

    def check(self, ws: Workspace, names: list[str]) -> bool:
        ok = True
        for name in names:
            cb = ws.work_dir(name) / "spec" / "confirmed-bugs.md"
            line = f"  {name:<20}"
            if cb.is_file() and cb.stat().st_size > 0:
                line += "confirmed-bugs OK"
            else:
                line += "confirmed-bugs MISSING"
                ok = False
            print(line)
        return ok

    def agent_files(self, ws: Workspace, name: str) -> AgentFiles:
        wd = ws.work_dir(name)
        return {
            "log": wd / "bug-classification.log",
            "pid": wd / "bug-classification.pid",
            "prompt": wd / ".bug-classification-prompt.md",
            "mkdirs": [],  # bash does not mkdir; work_dir already exists (has confirmed-bugs.md)
        }

    def build_prompt(self, ws: Workspace, target: str) -> str:
        # NOTE: bash bug_classification generate_prompt does NOT inject .prompt-extra.
        name = self.target_name(target)
        spec_dir = ws.work_dir(name) / "spec"
        return f"""# Bug Classification Task: {name}

You are assigning a Severity tier to each bug in **{name}**'s already-confirmed bug report.

## Input

- **Confirmed bug report (from Phase 4a)**: {spec_dir}/confirmed-bugs.md

## Output

- **Severity classification**: {spec_dir}/bug-severity.md (you create this file)

## Methodology

Follow the **bug-classification** skill exactly — it is the single source of methodology (the four-tier Severity rubric, the per-bug output schema and mandatory Summary block, the single-responsibility constraints — do not modify confirmed-bugs.md or its Status fields — the rule that Severity is independent of reproduction status, and the output validation checklist). Read and execute it in full:
  {SPECULA_ROOT}/.claude/skills/bug-classification/guide.md

Do everything the skill specifies. Do not add, relax, or override any step here.
"""

    def summarize(self, ws: Workspace, names: list[str]) -> None:
        print()
        print("========================================")
        print(" Results")
        print("========================================")
        for name in names:
            report = ws.work_dir(name) / "spec" / "bug-severity.md"
            if report.is_file() and report.stat().st_size > 0:
                text = report.read_text(errors="replace")  # bash grep is byte-safe
                total = _grep_num(text, "- Total bugs:")
                c = _grep_num(text, "- Critical:")
                h = _grep_num(text, "- High:")
                m = _grep_num(text, "- Medium:")
                low = _grep_num(text, "- Low:")
                fp = _grep_num(text, "- FALSE POSITIVE")
                print(f"  {name}: total={total}  C={c} H={h} M={m} L={low} FP={fp}")
            elif report.is_file():
                print(f"  {name}: bug-severity.md empty (check log)")
            else:
                print(f"  {name}: (no report — check log)")

    def monitor_line(self, ws: Workspace) -> str | None:
        # bash glob omits the .specula-output/ segment — replicated verbatim in legacy.
        return self._monitor(ws, "bug-classification.log", "  Monitor: tail -f */bug-classification.log")


class SpecValidationPhase(Phase):
    key = "spec_validation"
    title = "Specula — Spec Validation Batch Runner"
    usage = r"""
Batch launcher: spawn one Claude Code agent per target system for spec validation.
Each agent iteratively runs trace validation and invariant checking using existing
skills until both pass. Harness and traces must already exist (Phase 2.5).

Usage:
  bash scripts/launch/launch_spec_validation.sh [options] "name" [...]

Example:
  bash scripts/launch/launch_spec_validation.sh cometbft
  bash scripts/launch/launch_spec_validation.sh braft sofa-jraft dragonboat
  bash scripts/launch/launch_spec_validation.sh --artifact=/path/to/repo myproject

Options:
  --dry-run           Print commands without executing
  --check             Only verify prerequisites exist
  --repair            Repair mode: process OPEN/REOPENED repair requests (confirmation back-edge)
  --max-parallel=N    Max concurrent agents (default: 1)
  --max-turns=N       Max agent turns (default: 0 = unlimited)
  --agent=NAME        Agent adapter to use (default: claude-code)
  --claude-alias=NAME Claude CLI profile (default: claude)
  --artifact=PATH     Explicit path to the artifact repo (overrides auto-detection)

Prerequisites:
  - Spec files at <name>/.specula-output/spec/ (from Phase 2)
  - Source repo at <name>/artifact/<repo>/ or specified via --artifact

"""
    check_header = "Checking prerequisites..."
    check_fail_msg = "ERROR: Missing prerequisites. Run spec generation first."

    def parse_flag(self, arg: str, extra: dict[str, str | bool]) -> bool:
        if arg == "--repair":
            extra["repair"] = True
            return True
        return False

    def check(self, ws: Workspace, names: list[str]) -> bool:
        ok = True
        for name in names:
            spec_dir = ws.work_dir(name) / "spec"
            repo_dir = ws.find_repo_dir(name)
            line = f"  {name:<20}"
            base = spec_dir / "base.tla"
            if base.is_file() and (spec_dir / "MC.tla").is_file() and (spec_dir / "Trace.tla").is_file():
                line += f"specs OK ({_wc_l(base)}L)"
            else:
                line += "specs MISSING"
                ok = False
            if (spec_dir / "instrumentation-spec.md").is_file():
                line += "  instr OK"
            else:
                line += "  instr MISSING"
                ok = False
            line += "  repo OK" if repo_dir else "  repo MISSING"
            if not repo_dir:
                ok = False
            traces_dir = ws.work_dir(name) / "traces"
            n = len(list(traces_dir.rglob("*.ndjson"))) if traces_dir.is_dir() else 0
            line += f"  traces OK ({n})" if n > 0 else "  traces WARN (0 ndjson files)"
            print(line)
        return ok

    def agent_files(self, ws: Workspace, name: str) -> AgentFiles:
        wd = ws.work_dir(name)
        tag = "spec-repair" if ws.opts.get("repair") else "spec-validation"
        return {
            "log": wd / f"{tag}.log",
            "pid": wd / "spec-validation.pid",  # bash always writes spec-validation.pid
            "prompt": wd / f".{tag}-prompt.md",
            "mkdirs": [wd / "traces"],
        }

    def build_prompt(self, ws: Workspace, target: str) -> str:
        name = self.target_name(target)
        wd = ws.work_dir(name)
        spec_dir = wd / "spec"
        repo_dir = ws.find_repo_dir(name)
        if ws.opts.get("repair"):
            prompt = f"""# Spec Repair Task (confirmation back-edge): {name}

You are running spec validation in **REPAIR MODE**. The bug-confirmation phase handed
back counterexamples it judged to be spec / fault-model / invariant **artifacts** (not
real bugs), each recorded as a repair request. Repair the spec so the artifact no longer
arises, re-validate, then hand each request to re-check.

## Inputs
- **Repair requests**: {spec_dir}/repair-requests/   (process ONLY status OPEN or REOPENED)
- **Spec directory**: {spec_dir}   (base.tla, MC.tla, Trace.tla, *.cfg, MC_hunt_*.cfg)
- **Source code**: {repo_dir}
- **Modeling brief**: {wd}/modeling-brief.md
- **Traces**: {wd}/traces/

## Methodology — read and follow exactly (single source of repair-mode method)
- **{SPECULA_ROOT}/.claude/skills/bug-confirmation/references/repair-request-format.md** — the artifact, the state machine, and the per-request repair procedure (how to repair each target, the full-trace soundness gate, and the OPEN/REOPENED → IN_REPAIR → RECHECK transitions you own).
- **{SPECULA_ROOT}/.claude/skills/validation-workflow/guide.md** (+ its sub-skills tla-trace-workflow, tla-checking-workflow) — how to repair the spec and re-validate without overfitting.

Process ONLY OPEN/REOPENED requests. Do everything those docs specify; do not add, relax, or override any step here.
"""
        else:
            prompt = f"""# Spec Validation Task: {name}

You are validating the TLA+ specification for **{name}** through iterative trace validation and invariant checking.

## Inputs

- **Spec directory**: {spec_dir}
  - base.tla, base.cfg — Base specification
  - MC.tla, MC.cfg — Model checking specification
  - Trace.tla, Trace.cfg — Trace validation specification
  - instrumentation-spec.md — Action-to-code mapping for harness generation
- **Source code**: {repo_dir}
- **Modeling brief**: {wd}/modeling-brief.md

## Workflow

Follow the **validation-workflow** skill exactly — it is the single source of methodology (its iterative trace-validation ↔ model-checking loop, the Case A/B/C classification, convergence, bug hunting, and required artifacts such as changelog.md / bug-report.md). Read and execute it in full, including the two sub-skills it delegates to:
  {SPECULA_ROOT}/.claude/skills/validation-workflow/guide.md
  (sub-skills: {SPECULA_ROOT}/.claude/skills/tla-trace-workflow/guide.md and {SPECULA_ROOT}/.claude/skills/tla-checking-workflow/guide.md)

Do everything the skill specifies. Do not add, relax, or override any step here. Harness and traces already exist from Phase 2.5 under `{wd}/traces/` and `{wd}/harness/`; the skill's Phase 0 covers verifying and (if needed) regenerating them.
"""
        return self._with_extra(ws, name, prompt)

    def summarize(self, ws: Workspace, names: list[str]) -> None:
        print()
        print("========================================")
        print(" Results")
        print("========================================")
        for name in names:
            changelog = ws.work_dir(name) / "spec" / "changelog.md"
            if changelog.is_file() and changelog.stat().st_size > 0:
                print(f"  {name}: changelog written ({_wc_l(changelog)} lines)")
            elif changelog.is_file():
                print(f"  {name}: changelog empty (check log)")
            else:
                print(f"  {name}: no changelog (check log)")

    def monitor_line(self, ws: Workspace) -> str | None:
        # bash uses an absolute ${PWD} path and always spec-validation.log (even
        # in --repair mode, whose log is spec-repair.log) — replicated verbatim in legacy.
        return self._monitor(
            ws, "spec-validation.log", f"  Monitor: tail -f {ws.cwd}/*/.specula-output/spec-validation.log"
        )


class BugConfirmationPhase(Phase):
    key = "bug_confirmation"
    title = "Specula — Bug Confirmation Batch Runner"
    usage = r"""
Bug confirmation for each target system. By DEFAULT this runs parallel
per-finding confirmation (step 0 consolidate + dedup, then one Reproducer agent
per finding, in parallel — see confirmlib.py). `--legacy-confirm` reverts to the
single agent that consolidates and reproduces every finding in one context.

Usage:
  bash scripts/launch/launch_bug_confirmation.sh [options] "name" [...]

Example:
  bash scripts/launch/launch_bug_confirmation.sh hashicorp-raft nuraft

Options:
  --dry-run           Print commands without executing
  --check             Only verify prerequisites exist
  --legacy-confirm    Single-agent confirmation (one agent, all findings) instead of parallel
  --recheck           Re-check mode: settle RECHECK repair requests (confirmation back-edge; single-agent)
  --max-repair-rounds=N  Per-request repair cap honored in --recheck (default: 0 = unlimited)
  --max-parallel=N    Concurrent findings in parallel mode / concurrent agents in --legacy-confirm (default: 1)
  --max-turns=N       Max agent turns (default: 0 = unlimited)
  --agent=NAME        Agent adapter to use (default: claude-code)
  --claude-alias=NAME Claude CLI profile (default: claude)
  --artifact=PATH     Explicit path to the artifact repo (overrides auto-detection)

Prerequisites:
  - Bug report at <name>/spec/bug-report.md (from Phase 3)
  - Modeling brief at <name>/modeling-brief.md (from Phase 1)
  - Source repo at <name>/artifact/<repo>/ (or supplied via --artifact)

"""
    check_header = "Checking prerequisites..."
    check_fail_msg = "ERROR: Missing prerequisites. Run full pipeline first."

    def parse_flag(self, arg: str, extra: dict[str, str | bool]) -> bool:
        if arg == "--recheck":
            extra["recheck"] = True
            return True
        if arg.startswith("--max-repair-rounds="):
            extra["max_repair_rounds"] = arg[len("--max-repair-rounds=") :]
            return True
        if arg == "--legacy-confirm":
            extra["legacy"] = True
            return True
        return False

    def run_alternate(
        self,
        ws: Workspace,
        names: list[str],
        *,
        adapter: Path,
        claude_alias: str,
        max_parallel: int,
        dry_run: bool,
    ) -> int | None:
        """Parallel per-finding confirmation — the DEFAULT first-pass mode.
        `--legacy-confirm` falls back to the single-agent path; `--recheck`
        always uses it (re-check is single-agent). None defers to the
        single-agent loop in Phase.run."""
        if ws.opts.get("legacy") or ws.opts.get("recheck"):
            return None
        # Local import: confirmlib imports phaselib, so a top-level import here
        # would be circular.
        from specula.confirmlib import ConfirmConfig, run_parallel_confirmation

        # `max_parallel` here is the per-finding concurrency. The pipeline default
        # is 1 — it means "concurrent targets" for the other phases, but that is
        # degenerate for per-finding fan-out (findings would run one at a time, so
        # "parallel" would not actually be parallel). Use a real concurrency
        # default; an explicit --max-parallel=N>1 still wins.
        findings_parallel = max_parallel if max_parallel > 1 else 4
        rc = 0
        for name in names:
            if not dry_run:
                print(f"  Monitor: tail -f {ws.work_dir(name)}/bug-confirmation.log")
            cfg = ConfirmConfig(
                name=name,
                ws=ws,
                adapter=adapter,
                repo_dir=ws.find_repo_dir(name),
                max_parallel=findings_parallel,
                claude_alias=claude_alias,
                dry_run=dry_run,
                prompt_extra=self._read_prompt_extra(ws, name),
            )
            code = run_parallel_confirmation(cfg)
            if code != 0:
                rc = code
        self.summarize(ws, names)
        if not dry_run:
            self._acceptance(ws, names)
        return rc

    def check(self, ws: Workspace, names: list[str]) -> bool:
        ok = True
        for name in names:
            wd = ws.work_dir(name)
            repo_dir = ws.find_repo_dir(name)
            line = f"  {name:<20}"
            if (wd / "spec" / "bug-report.md").is_file():
                line += "bug-report OK"
            else:
                line += "bug-report MISSING"
                ok = False
            if (wd / "modeling-brief.md").is_file():
                line += "  brief OK"
            else:
                line += "  brief MISSING"
                ok = False
            line += "  repo OK" if repo_dir else "  repo MISSING"
            if not repo_dir:
                ok = False
            print(line)
        return ok

    def agent_files(self, ws: Workspace, name: str) -> AgentFiles:
        wd = ws.work_dir(name)
        tag = "bug-recheck" if ws.opts.get("recheck") else "bug-confirmation"
        return {
            "log": wd / f"{tag}.log",
            "pid": wd / "bug-confirmation.pid",  # bash always writes bug-confirmation.pid
            "prompt": wd / f".{tag}-prompt.md",
            "mkdirs": [],
        }

    def build_prompt(self, ws: Workspace, target: str) -> str:
        name = self.target_name(target)
        wd = ws.work_dir(name)
        spec_dir = wd / "spec"
        repo_dir = ws.find_repo_dir(name)
        if ws.opts.get("recheck"):
            rounds = ws.opts.get("max_repair_rounds", "0")
            prompt = f"""# Bug Re-check Task (confirmation back-edge): {name}

You are running the bug-confirmation **RE-CHECK** pass. Phase 3 (repair mode) has repaired
the spec for the open repair requests and moved them to `status: RECHECK`. Settle each
finding and transition its request out of RECHECK.

## Inputs
- **Repair requests**: {spec_dir}/repair-requests/   (process ONLY status RECHECK)
- **Updated bug report + TLC output**: {spec_dir}/bug-report.md , {spec_dir}/output/
- **Confirmed bugs (you update this)**: {spec_dir}/confirmed-bugs.md
- **Source code**: {repo_dir}
- **Per-request cap**: --max-repair-rounds={rounds}   (0 = unlimited)

## Methodology — read and follow
- {SPECULA_ROOT}/.claude/skills/bug-confirmation/phases/03-recheck.md
- {SPECULA_ROOT}/.claude/skills/bug-confirmation/references/repair-request-format.md

## Instructions
Do everything `03-recheck.md` and `repair-request-format.md` specify, exactly — process ONLY `status: RECHECK` requests, and honor the per-request cap (`--max-repair-rounds` above). Do not add, relax, or override any step here.
"""
        else:
            prompt = f"""# Bug Confirmation Task: {name}

You are confirming and reproducing bugs found in **{name}** by both model checking and code review.

## Inputs

- **Bug report (MC findings)**: {spec_dir}/bug-report.md
- **Modeling brief (code review findings)**: {wd}/modeling-brief.md
- **Source code**: {repo_dir}
- **Spec directory**: {spec_dir}

## Methodology

Read and follow the **bug-confirmation** skill:
  {SPECULA_ROOT}/.claude/skills/bug-confirmation/guide.md

## Task

Consolidate the two finding sources into one candidate list:
- **MC findings** (with counterexamples): `{spec_dir}/bug-report.md`
- **Code-review findings**: `{wd}/modeling-brief.md`

Then process every candidate **strictly per the bug-confirmation skill's Flow** — do not restate, relax, or override it here. In particular:
- Apply **only** the skill's single pre-filter (code-review-sourced **and** already-known → drop before Phase 2, exactly as the skill defines it). Invent no other pre-filter — never skip a candidate as "defensive coding", "style", or "theoretical-only".
- Follow the skill's Phase 1 (investigation) and Phase 2 (strict Level 0→3 escalation ladder), and use its per-bug output schema and statuses.

Write the consolidated report to `{spec_dir}/confirmed-bugs.md`, with one `repro/` test per non-dropped finding under `{wd}/repro/`, exactly as the skill specifies.
"""
        return self._with_extra(ws, name, prompt)

    def summarize(self, ws: Workspace, names: list[str]) -> None:
        print()
        print("========================================")
        print(" Results")
        print("========================================")
        for name in names:
            wd = ws.work_dir(name)
            report = wd / "spec" / "confirmed-bugs.md"
            repro_dir = wd / "repro"
            repro_count = len([p for p in repro_dir.rglob("test_bug*") if p.is_file()]) if repro_dir.is_dir() else 0
            if report.is_file() and report.stat().st_size > 0:
                n = _wc_l(report)
                print(f"  {name}: confirmed-bugs.md written ({n} lines, repro/ tests: {repro_count})")
            elif report.is_file():
                print(f"  {name}: confirmed-bugs.md empty (check log; repro/ tests: {repro_count})")
            else:
                print(f"  {name}: (no report — check log; repro/ tests: {repro_count})")

    def monitor_line(self, ws: Workspace) -> str | None:
        # bash glob omits the .specula-output/ segment and always bug-confirmation.log
        # (even in --recheck, whose log is bug-recheck.log) — replicated verbatim in legacy.
        return self._monitor(ws, "bug-confirmation.log", "  Monitor: tail -f */bug-confirmation.log")


class ReviewPhase(Phase):
    """Inter-phase review agent (used by launch_pipeline.sh between phases; off by
    default). The outlier: args are `<phase> <name...>`, no --dry-run/--check, an
    inline --prompt, and hardcoded --max-turns=30 — so it overrides run() wholesale
    instead of using the shared driver. The review's contract is the agent-facing
    prompt it assembles."""

    key = "review"
    usage = r"""
Run a Claude Code review agent on phase outputs.
Used by launch_pipeline.sh between phases. Can also be used standalone.

Usage:
  bash scripts/launch/launch_review.sh <phase> <name> [name ...]

Phases:
  analysis    — Review code analysis output (modeling-brief.md, analysis-report.md)
  specgen     — Review spec generation output (base.tla, MC.tla, Trace.tla)
  validation  — Review validation results (validation-report.md)

Output:
  .specula-output/review-<phase>.md

"""

    def run(self, argv: list[str]) -> int:
        phase = argv[0] if argv else ""
        agent = "claude-code"
        claude_alias = os.environ.get("CLAUDE_ALIAS") or "claude"
        targets: list[str] = []
        for arg in argv[1:]:
            if arg.startswith("--agent="):
                agent = arg[len("--agent=") :]
            elif arg.startswith("--claude-alias="):
                claude_alias = arg[len("--claude-alias=") :]
            elif arg in ("--help", "-h"):
                sys.stdout.write(self.usage)
                return 0
            else:
                targets.append(arg)

        if not phase or not targets:
            print(f"Usage: {SCRIPT_DIR}/phaselib.py review <analysis|specgen|validation> name [name ...]")
            return 1

        adapter = LAUNCH_DIR / "adapters" / f"{agent}.sh"
        if not adapter.is_file():
            print(f"ERROR: Unknown agent '{agent}' — adapter not found at {adapter}")
            return 1

        ws = Workspace(targets)
        names = [_trim(t) for t in targets]

        print("========================================")
        print(f" Specula — Review Agent ({phase})")
        print("========================================")

        for name in names:
            rc = self._launch_review(ws, name, phase, adapter, claude_alias)
            if rc != 0:
                # bash ran under `set -euo pipefail`: a failing adapter (notably
                # exit 75 = EX_TEMPFAIL on rate limit) aborted the launcher with
                # that code so the pipeline can wait/retry instead of treating
                # the review as done.
                return rc

        print()
        print("Waiting for review agents to complete...")
        # The adapter call ran synchronously above (mirroring bash's `pid=$(...)`
        # command substitution), so there is nothing left to wait on here.

        print()
        print("========================================")
        print(" Review Results")
        print("========================================")
        for name in names:
            wd = ws.work_dir(name)
            if phase == "specgen":
                review_file = wd / "spec" / "review-specgen.md"
            elif phase == "validation":
                review_file = wd / "spec" / "review-validation.md"
            else:  # analysis
                review_file = wd / "review-analysis.md"
            if review_file.is_file() and review_file.stat().st_size > 0:
                print(f"  {name}: review written ({_wc_l(review_file)} lines)")
            elif review_file.is_file():
                print(f"  {name}: review empty (check log)")
            else:
                print(f"  {name}: (no review file generated — check log)")
        return 0

    def _launch_review(self, ws: Workspace, name: str, phase: str, adapter: Path, claude_alias: str) -> int:
        wd = ws.work_dir(name)
        # specgen/validation logs go under spec/ to match pipeline summary expectations
        log_dir = wd / "spec" if phase in ("specgen", "validation") else wd
        log_file = log_dir / f"review-{phase}.log"
        if phase == "analysis":
            prompt = self._analysis_prompt(wd, name)
        elif phase == "specgen":
            prompt = self._specgen_prompt(wd, name)
        elif phase == "validation":
            prompt = self._validation_prompt(wd, name)
        else:
            print(f"Unknown phase: {phase}")
            raise SystemExit(1)
        print(f"[{_ts()}] Reviewing {name} ({phase})...")
        log_dir.mkdir(parents=True, exist_ok=True)
        # Capture only stdout (bash `pid=$(...)` command substitution); stderr is
        # inherited so adapter diagnostics ("rate limit hit", arg errors) reach
        # the console / pipeline log as they did under bash.
        proc = subprocess.run(
            [
                str(adapter),
                # bash: prompt=$(generate_..._prompt) — command substitution
                # strips trailing newlines before the adapter sees the prompt.
                f"--prompt={prompt.rstrip(chr(10))}",
                "--max-turns=30",
                f"--claude-alias={claude_alias}",
                "--effort=max",
                f"--log={log_file}",
                "--background",
            ],
            stdout=subprocess.PIPE,
            text=True,
        )
        if proc.returncode != 0:
            # bash set -e aborted here, before the pid file write / PID line.
            return proc.returncode
        pid = proc.stdout.rstrip("\n")
        (log_dir / f"review-{phase}.pid").write_text(f"{pid}\n")
        print(f"  PID={pid}  Log: {log_file}")
        return 0

    def _analysis_prompt(self, wd: Path, name: str) -> str:
        return f"""# Code Analysis Review: {name}

Review the code analysis outputs for quality and completeness.

## Files to Review

- Modeling Brief: {wd}/modeling-brief.md
- Analysis Report: {wd}/analysis-report.md

## Review Checklist

Score each item 1-5 (1=missing, 3=adequate, 5=excellent):

1. **Coverage Statistics**: Are they reported? How many issues were deeply read (target: 30+)?
2. **Bug Families**: Are they well-defined with mechanisms, not just lists? (target: 4-7 families)
3. **Evidence Quality**: Does each bug cite file:line, issue numbers, and commit references?
4. **Model-Checkable Findings**: Are findings classified? How many are model-checkable?
5. **Modeling Brief Completeness**: Variables, actions, invariants, extensions all specified?
6. **False Positive Control**: Were excluded issues documented with reasons?
7. **Source Code Annotations**: Are file:line references present throughout?

## Output

Write your review to: {wd}/review-analysis.md

Format:
```markdown
# Code Analysis Review: {name}

## Scores
| Criterion | Score | Notes |
|-----------|-------|-------|
| Coverage Statistics | X/5 | ... |
| Bug Families | X/5 | ... |
| Evidence Quality | X/5 | ... |
| Model-Checkable Findings | X/5 | ... |
| Modeling Brief Completeness | X/5 | ... |
| False Positive Control | X/5 | ... |
| Source Code Annotations | X/5 | ... |

## Overall: X/35

## Issues Found
- ...

## Verdict: PASS / NEEDS_IMPROVEMENT
```
"""

    def _specgen_prompt(self, wd: Path, name: str) -> str:
        spec_dir = wd / "spec"
        return f"""# Spec Generation Review: {name}

Review the generated TLA+ specs for correctness and completeness.

## Files to Review

- Base Spec: {spec_dir}/base.tla
- Base Config: {spec_dir}/base.cfg
- MC Spec: {spec_dir}/MC.tla
- MC Config: {spec_dir}/MC.cfg
- Trace Spec: {spec_dir}/Trace.tla
- Trace Config: {spec_dir}/Trace.cfg
- Instrumentation: {spec_dir}/instrumentation-spec.md
- Modeling Brief (reference): {wd}/modeling-brief.md

## Review Checklist

Score each item 1-5:

1. **Bug Family Coverage**: Does each Bug Family in the brief have corresponding spec extensions?
2. **Action Design**: Are actions named after impl functions? Are code paths split where they diverge?
3. **Source Annotations**: Does every logic block cite file:line?
4. **Invariant Coverage**: Are standard + extension invariants present for each Bug Family?
5. **MC Spec Structure**: Are only fault-injection actions bounded? Symmetry/view/constraints present?
6. **Trace Spec Design**: Are silent actions tightly constrained? Post-state validation present?
7. **Instrumentation Mapping**: Is there a 1:1 mapping between spec actions and code locations?
8. **Logical Correctness**: Check for tautologies, impossible guards, typos in temporal properties.

## Output

Write your review to: {spec_dir}/review-specgen.md

Format:
```markdown
# Spec Generation Review: {name}

## Scores
| Criterion | Score | Notes |
|-----------|-------|-------|
| Bug Family Coverage | X/5 | ... |
| Action Design | X/5 | ... |
| Source Annotations | X/5 | ... |
| Invariant Coverage | X/5 | ... |
| MC Spec Structure | X/5 | ... |
| Trace Spec Design | X/5 | ... |
| Instrumentation Mapping | X/5 | ... |
| Logical Correctness | X/5 | ... |

## Overall: X/40

## Issues Found
- ...

## Verdict: PASS / NEEDS_IMPROVEMENT
```
"""

    def _validation_prompt(self, wd: Path, name: str) -> str:
        spec_dir = wd / "spec"
        return f"""# Validation Review: {name}

Review the spec validation results and summarize readiness for trace validation.

## Files to Review

- Validation Report: {spec_dir}/validation-report.md
- Quick MC Log (if exists): {spec_dir}/quick-mc.log

## Review Checklist

1. **Syntax**: Did all specs pass SANY?
2. **MC Results**: Any violations found? Expected or unexpected?
3. **Readiness**: Is the spec ready for trace validation? What needs instrumentation first?

## Output

Write your review to: {spec_dir}/review-validation.md

Format:
```markdown
# Validation Review: {name}

## Status
- Syntax: PASS/FAIL
- MC: PASS/FAIL/TIMEOUT/SKIPPED
- Ready for trace validation: YES/NO

## Next Steps
- ...

## Verdict: PASS / NEEDS_IMPROVEMENT
```
"""


PHASES: dict[str, Phase] = {
    p.key: p
    for p in [
        CodeAnalysisPhase(),
        SpecGenerationPhase(),
        HarnessGenerationPhase(),
        BugClassificationPhase(),
        SpecValidationPhase(),
        BugConfirmationPhase(),
        ReviewPhase(),
    ]
}


def main(argv: list[str]) -> int:
    # bash echo flushed per line; python block-buffers when stdout is a pipe
    # (launch_pipeline.sh tees everything), which would hold progress lines —
    # including the Monitor hint — in the buffer for the hours p.wait() blocks.
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(line_buffering=True)
    if not argv or argv[0] not in PHASES:
        print(f"usage: phaselib.py <phase> [options] <target>...\nphases: {', '.join(PHASES)}", file=sys.stderr)
        return 2
    return PHASES[argv[0]].run(argv[1:])


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
