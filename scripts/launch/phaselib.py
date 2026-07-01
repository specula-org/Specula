#!/usr/bin/env python3
"""Specula phase launchers — Python framework (port of scripts/launch/launch_*.sh).

Each historical `launch_<phase>.sh` spawns one agent per target: parse args,
check prerequisites, build a per-phase prompt that defers to a skill, run the
agent adapter (throttled, in the background), then summarize. This module folds
that shared skeleton into one `Phase` base + a small subclass per phase, so the
`launch_<phase>.sh` scripts become thin shims (`exec python3 phaselib.py <phase>`).

Behavior is a faithful port; the characterization suite in tests/characterization/
pins each launcher's --dry-run output and precondition gate against the bash.

Usage:  python3 phaselib.py <phase> [options] "<target>" [...]

Lives in scripts/launch/ for now (no packaging dependency); moves into the
`specula/` package once that exists (migration step 2).
"""

from __future__ import annotations

import os
import subprocess
import sys
import time
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
SPECULA_ROOT = SCRIPT_DIR.parent.parent


def _ts() -> str:
    """[HH:MM:SS] — mirrors bash `date '+%H:%M:%S'`."""
    return time.strftime("%H:%M:%S")


def _trim(s: str) -> str:
    """Mirror bash `echo "$x" | xargs` word-trim (leading/trailing whitespace)."""
    return s.strip()


class Workspace:
    """Path resolution for a run — the object step 4 (workspace control) extends.

    Faithful to the bash `get_work_dir` / `find_repo_dir`: single-target writes to
    `$PWD/.specula-output`; batch to `$PWD/<name>/.specula-output`.
    """

    def __init__(self, targets: list[str], artifact: str = "", cwd: Path | None = None):
        self.targets = targets
        self.artifact = artifact
        self.cwd = Path(cwd) if cwd else Path.cwd()
        self.single = len(targets) == 1

    def work_dir(self, name: str) -> Path:
        if self.single:
            return self.cwd / ".specula-output"
        return self.cwd / name / ".specula-output"

    def find_repo_dir(self, name: str) -> str:
        # Explicit --artifact wins.
        if self.artifact:
            return self.artifact
        # Batch: <cwd>/<name>/artifact/<repo-with-.git>/ (bash keeps the trailing slash).
        artifact_dir = self.cwd / name / "artifact"
        if artifact_dir.is_dir():
            for d in sorted(artifact_dir.iterdir()):
                if d.is_dir() and (d / ".git").exists():
                    return str(d) + "/"
        # Single target: source is $PWD.
        if self.single:
            return str(self.cwd)
        return ""


class Phase:
    """Base launcher. Subclasses set the per-phase specifics; `run` is shared."""

    key = ""  # cli name (e.g. "code_analysis")
    title = ""  # banner title
    check_header = "Checking prerequisites..."
    check_fail_msg = "ERROR: Missing prerequisites."

    # ── per-phase hooks ──
    def check(self, ws: Workspace, names: list[str]) -> bool:
        """Print a per-target prerequisite line; return True iff all satisfied."""
        raise NotImplementedError

    def agent_files(self, ws: Workspace, name: str) -> dict:
        """Return {log, pid, prompt, mkdir} paths for this phase's agent run."""
        raise NotImplementedError

    def build_prompt(self, ws: Workspace, target: str) -> str:
        raise NotImplementedError

    def summarize(self, ws: Workspace, names: list[str]) -> None:
        raise NotImplementedError

    # ── shared prompt-extra injection (identical across phases) ──
    def _with_extra(self, ws: Workspace, name: str, prompt: str) -> str:
        extra = ws.work_dir(name) / ".prompt-extra.md"
        if not extra.is_file():
            extra = ws.cwd / ".prompt-extra.md"
        if extra.is_file():
            prompt += "\n## Target-Specific Instructions\n\n" + extra.read_text()
        return prompt

    # ── shared driver ──
    def run(self, argv: list[str]) -> int:
        max_parallel = 1
        max_turns = 0
        dry_run = False
        check_only = False
        agent = "claude-code"
        claude_alias = os.environ.get("CLAUDE_ALIAS", "claude")
        artifact = ""
        targets: list[str] = []

        for arg in argv:
            if arg == "--dry-run":
                dry_run = True
            elif arg == "--check":
                check_only = True
            elif arg.startswith("--max-parallel="):
                max_parallel = int(arg[len("--max-parallel=") :])
            elif arg.startswith("--max-turns="):
                max_turns = int(arg[len("--max-turns=") :])
            elif arg.startswith("--agent="):
                agent = arg[len("--agent=") :]
            elif arg.startswith("--claude-alias="):
                claude_alias = arg[len("--claude-alias=") :]
            elif arg.startswith("--artifact="):
                artifact = arg[len("--artifact=") :]
            elif arg in ("--help", "-h"):
                print(self.__doc__ or self.title)
                return 0
            elif arg.startswith("-"):
                print(f"Unknown option: {arg}")
                return 1
            else:
                targets.append(arg)

        if not targets:
            targets = [Path.cwd().name]

        adapter = SCRIPT_DIR / "adapters" / f"{agent}.sh"
        if not adapter.is_file():
            print(f"ERROR: Unknown agent '{agent}' — adapter not found at {adapter}")
            return 1

        ws = Workspace(targets, artifact=artifact)
        names = [_trim(t.split("|", 1)[0]) for t in targets]

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
            print("All prerequisites OK.")
            return 0

        running: list[subprocess.Popen] = []
        for target in targets:
            name = _trim(target.split("|", 1)[0])
            prompt = self.build_prompt(ws, target)
            # Throttle.
            while len(running) >= max_parallel:
                running = [p for p in running if p.poll() is None]
                if len(running) >= max_parallel:
                    time.sleep(5)
            proc = self._launch(ws, name, prompt, dry_run, max_turns, claude_alias, adapter)
            if not dry_run and proc is not None:
                running.append(proc)
            print()

        if not dry_run:
            print(f"[{_ts()}] All agents launched. Waiting...")
            print()
            for p in running:
                p.wait()
            print(f"[{_ts()}] All agents completed.")

        self.summarize(ws, names)
        return 0

    def _launch(self, ws, name, prompt, dry_run, max_turns, claude_alias, adapter):
        files = self.agent_files(ws, name)
        files["mkdir"].mkdir(parents=True, exist_ok=True)
        files["prompt"].write_text(prompt)
        print(f"[{_ts()}] Launching agent: {name}")
        if dry_run:
            print(f"  [DRY RUN] {adapter} --prompt=<prompt> --max-turns={max_turns} --log={files['log']} --background")
            print(f"  Prompt saved: {files['prompt']}")
            return None
        proc = subprocess.Popen(
            [
                str(adapter),
                f"--prompt-file={files['prompt']}",
                f"--max-turns={max_turns}",
                f"--claude-alias={claude_alias}",
                "--effort=max",
                f"--log={files['log']}",
                "--background",
            ]
        )
        files["pid"].write_text(f"{proc.pid}\n")
        print(f"  PID={proc.pid}  Log: {files['log']}")
        return proc


class CodeAnalysisPhase(Phase):
    key = "code_analysis"
    title = "Specula — Code Analysis Batch Runner"
    check_header = "Checking repositories..."
    check_fail_msg = (
        "ERROR: Some repositories are missing. Use --artifact=<path> or place repos under <name>/artifact/<repo>/."
    )

    def check(self, ws, names):
        ok = True
        for name in names:
            repo_dir = ws.find_repo_dir(name)
            if repo_dir:
                r = subprocess.run(
                    ["git", "rev-list", "--count", "HEAD"],
                    cwd=repo_dir,
                    capture_output=True,
                    text=True,
                )
                commits = r.stdout.strip() if r.returncode == 0 else "?"
                print(f"  OK  {name} ({commits} commits)")
            else:
                print(f"  MISSING  {name} — use --artifact=<path> or place repo at {name}/artifact/<repo>/")
                ok = False
        return ok

    def agent_files(self, ws, name):
        wd = ws.work_dir(name)
        return {"log": wd / "agent.log", "pid": wd / "agent.pid", "prompt": wd / ".prompt.md", "mkdir": wd}

    def build_prompt(self, ws, target):
        parts = [_trim(x) for x in target.split("|")]
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

    def summarize(self, ws, names):
        print()
        print("========================================")
        print(" Results")
        print("========================================")
        for name in names:
            wd = ws.work_dir(name)
            brief = wd / "modeling-brief.md"
            report = wd / "analysis-report.md"
            if brief.is_file():
                n = len(brief.read_text().splitlines())
                print(f"  OK  {name} -> modeling-brief.md ({n} lines)")
            elif report.is_file():
                n = len(report.read_text().splitlines())
                print(f"  ~~  {name} -> analysis-report.md only ({n} lines, no modeling brief)")
            else:
                print(f"  --  {name} (no output)")


PHASES: dict[str, Phase] = {p.key: p for p in [CodeAnalysisPhase()]}


def main(argv: list[str]) -> int:
    if not argv or argv[0] not in PHASES:
        print(f"usage: phaselib.py <phase> [options] <target>...\nphases: {', '.join(PHASES)}", file=sys.stderr)
        return 2
    return PHASES[argv[0]].run(argv[1:])


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
