"""Python port of scripts/exp/scheduler.sh (migration step 6).

Overnight batch scheduler: runs queue tasks through launch_pipeline.sh with N
parallel workers, pausing on quota and retrying transient API failures. Every
observable behavior (log lines, status files, summary tallies, exit codes) is
pinned by the sched_* characterization goldens, captured from the bash
original — including its quirks (the doubled setup logs inside run_task, the
FAIL line's exit=0, dry-run tasks counted in no tally, the phantom task from a
tabs-only queue line). Path strings shown in logs are assembled by string
interpolation, not pathlib, so bash artifacts like `case-studies//artifact/`
survive byte-identically.

Concurrency: bash forked a subshell per task; here each task runs in a thread
whose only work is spawning the pipeline subprocess, log/status bookkeeping and
backoff sleeps — the actual parallelism is the pipeline child processes, same
as bash. A task aborted mid-setup (SystemExit in the thread) dies without
writing a status file, mirroring the bash subshell's set -e death
("not-started" in the summary).

Sleeps go through the external `sleep` command deliberately: the
characterization harness stubs `sleep` on PATH, and both implementations must
honor the same stub.

Sanctioned deviations from the bash (agreed 2026-07-04, unit-test pinned):
  - malformed resets_at timestamps: bash's `date -d` died under set -e and took
    the whole scheduler down; _epoch degrades to the 60s floor instead
    (pipelinelib semantics).
  - numeric flags (--workers/--windows/--max-turns/--threshold*) are validated
    at parse time; bash accepted garbage and then hung or spun in arithmetic.
  - a flag missing its value errors out cleanly; bash died on `set -u`.
  - a relative --prompt whose directory doesn't exist resolves via abspath;
    bash died in `cd "$(dirname ...)"`.
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
import threading
import time
from contextlib import suppress
from datetime import datetime
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
SPECULA_ROOT = SCRIPT_DIR.parent.parent

# the bash --help printed the scheduler.sh header comment via sed (lines 2 to
# the first blank line, `# ` stripped); the text is pinned by help_scheduler
HELP = """
Overnight batch scheduler for Specula pipeline.

Runs tasks from a queue file with N parallel workers.
Pauses when usage exceeds threshold, waits for 5-hour window reset, resumes.
Stops after exhausting MAX_WINDOWS resets.

Usage:
  bash scripts/exp/scheduler.sh [options]

Options:
  --workers N         Parallel workers (default: 3)
  --threshold N       5-hour window usage % to pause at (default: 80)
  --threshold-7day N  7-day window usage % to pause at (default: 95)
  --windows N         Max resets to wait through (default: 3)
  --queue FILE     Task queue file (default: scripts/exp/tasks.queue)
  --max-turns N    Max agent turns per task (default: 0 = unlimited)
  --setup-only     Only clone repos and write prompts, don't run pipeline
  --dry-run        Print commands without executing
  --claude-alias NAME  Claude CLI profile (default: claude).
                       Forwarded to launch_pipeline.sh and used by usage.sh
                       so quota checks target the same account.

Queue format (tab-separated):
  name|github|lang|reference[TAB]flags[TAB]prompt_file

  - flags: optional launch_pipeline.sh flags (e.g. --skip-analysis)
  - prompt_file: optional path to extra prompt (relative to queue dir)
    Content is written to case-studies/<name>/.prompt-extra.md before launch.
"""

_TRANSIENT_RE = re.compile(r"API Error: 5[0-9][0-9]|Internal server error|overloaded_error|Overloaded")


def _epoch(ts: str) -> int:
    """`date -d "$ts" +%s`. On unparseable input the bash died under set -e
    (sanctioned deviation): degrade to 0 → hugely negative wait → the 60s
    floor, matching pipelinelib._epoch."""
    try:
        return int(datetime.fromisoformat(ts.replace("Z", "+00:00")).timestamp())
    except ValueError:
        return 0


def _grep(path: str, pattern: re.Pattern[str] | str) -> bool:
    """`grep -q <pattern> <path> 2>/dev/null` — byte-tolerant, missing file is
    just a miss."""
    try:
        text = Path(path).read_text(errors="replace")
    except OSError:
        return False
    if isinstance(pattern, str):
        return pattern in text
    return pattern.search(text) is not None


class Scheduler:
    def __init__(self) -> None:
        self.workers = 3
        self.threshold = "80"  # raw strings: displayed verbatim + exported to QUOTA_5H/7D
        self.threshold_7day = "95"
        self.max_windows = 3
        self.queue_file = str(SCRIPT_DIR / "tasks.queue")
        self.max_turns = 0
        self.prompt_file = ""
        self.dry_run = False
        self.setup_only = False
        self.claude_alias = os.environ.get("CLAUDE_ALIAS") or "claude"

        self.run_id = ""
        self.log_dir = ""
        self.windows_used = 0
        self.task_targets: list[str] = []
        self.task_flags: list[str] = []
        self._log_lock = threading.Lock()

    # ── logging ─────────────────────────────────────────────────────────────
    def log(self, msg: str) -> None:
        """`echo "[$(date ...)] $*" | tee -a scheduler.log`."""
        line = f"[{time.strftime('%Y-%m-%d %H:%M:%S')}] {msg}"
        with self._log_lock:
            print(line, flush=True)
            with open(f"{self.log_dir}/scheduler.log", "a") as f:
                f.write(line + "\n")

    def _sleep(self, secs: int) -> None:
        subprocess.run(["sleep", str(secs)], check=False)

    # ── arg parsing ─────────────────────────────────────────────────────────
    def parse_args(self, argv: list[str]) -> int | None:
        def val(i: int, flag: str) -> str | None:
            if i + 1 >= len(argv):
                print(f"ERROR: {flag} requires a value", file=sys.stderr)
                return None
            return argv[i + 1]

        def num(flag: str, v: str, as_int: bool) -> str | None:
            try:
                (int if as_int else float)(v)
            except ValueError:
                print(f"ERROR: invalid value for {flag}: '{v}'", file=sys.stderr)
                return None
            return v

        i = 0
        while i < len(argv):
            a = argv[i]
            if a in (
                "--workers",
                "--threshold",
                "--threshold-7day",
                "--windows",
                "--queue",
                "--max-turns",
                "--prompt",
                "--claude-alias",
            ):
                v = val(i, a)
                if v is None:
                    return 1
                if a in ("--workers", "--windows", "--max-turns"):
                    if num(a, v, as_int=True) is None:
                        return 1
                if a in ("--threshold", "--threshold-7day") and num(a, v, as_int=False) is None:
                    return 1
                if a == "--workers":
                    self.workers = int(v)
                elif a == "--threshold":
                    self.threshold = v
                elif a == "--threshold-7day":
                    self.threshold_7day = v
                elif a == "--windows":
                    self.max_windows = int(v)
                elif a == "--queue":
                    self.queue_file = v
                elif a == "--max-turns":
                    self.max_turns = int(v)
                elif a == "--prompt":
                    self.prompt_file = v
                else:
                    self.claude_alias = v
                i += 2
            elif a.startswith("--claude-alias="):
                self.claude_alias = a.split("=", 1)[1]
                i += 1
            elif a == "--setup-only":
                self.setup_only = True
                i += 1
            elif a == "--dry-run":
                self.dry_run = True
                i += 1
            elif a in ("-h", "--help"):
                print(HELP.rstrip("\n"))
                return 0
            else:
                print(f"Unknown: {a}", file=sys.stderr)
                return 1
        return None

    # ── usage gate ──────────────────────────────────────────────────────────
    def check_usage(self) -> bool:
        """True = under quota, proceed. Over-threshold writes the earliest
        resets_at into .reset_at and returns False. A fetch failure warns and
        proceeds; unparseable JSON is treated as over (the bash's embedded
        python died nonzero — kept as-is, revisited in the cutover commit)."""
        tmp = f"{self.log_dir}/.usage.json"
        proc = subprocess.run(
            ["bash", str(SCRIPT_DIR / "usage.sh")],
            env={**os.environ, "CLAUDE_ALIAS": self.claude_alias},
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            check=False,
        )
        Path(tmp).write_bytes(proc.stdout)
        if proc.returncode != 0:
            self.log("WARN: usage fetch failed")
            return True
        try:
            d = json.loads(Path(tmp).read_text())
            resets: list[str] = []
            for key, thr in (("five_hour", self.threshold), ("seven_day", self.threshold_7day)):
                obj = d.get(key)
                if obj and obj.get("utilization", 0) > float(thr):
                    resets.append(obj.get("resets_at", ""))
            if resets:
                earliest = sorted([r for r in resets if r])[0] if any(resets) else ""
                Path(f"{self.log_dir}/.reset_at").write_text(earliest)
                return False
            return True
        except Exception:
            return False

    def wait_for_quota(self) -> bool:
        """Block until under quota; False once MAX_WINDOWS resets are exhausted."""
        while not self.check_usage():
            self.windows_used += 1
            if self.windows_used > self.max_windows:
                self.log(f"Max resets ({self.max_windows}) exhausted, stopping scheduler")
                return False
            reset_at = ""
            with suppress(OSError):
                reset_at = Path(f"{self.log_dir}/.reset_at").read_text().rstrip("\n")
            if reset_at:
                sleep_secs = _epoch(reset_at) - int(time.time()) + 120
                if sleep_secs < 60:
                    sleep_secs = 60
                self.log(
                    f"Over {self.threshold}%, sleeping {sleep_secs}s until {reset_at}"
                    f" (reset {self.windows_used}/{self.max_windows})"
                )
            else:
                sleep_secs = 600
                self.log(f"Over {self.threshold}%, no reset time, sleeping {sleep_secs}s")
            self._sleep(sleep_secs)
        return True

    # ── task queue ──────────────────────────────────────────────────────────
    def load_queue(self) -> None:
        if not os.path.isfile(self.queue_file):
            self.log(f"Queue file not found: {self.queue_file}")
            raise SystemExit(1)
        text = Path(self.queue_file).read_text()
        # bash `while IFS= read -r`: an unterminated final line is dropped; a
        # tabs-only line is NOT blank (the check strips spaces only) — both
        # pinned (sched_queue_variants, unit tests)
        for line in text.split("\n")[:-1]:
            if not line.replace(" ", "") or re.match(r"^\s*#", line):
                continue
            if "\t" in line:
                target, flags = line.split("\t", 1)
                flags = flags.lstrip("\t")
            else:
                target, flags = line, ""
            self.task_targets.append(target)
            self.task_flags.append(flags)
        self.log(f"Loaded {len(self.task_targets)} tasks from {self.queue_file}")

    # ── setup: clone repo + write .prompt-extra.md ──────────────────────────
    def setup_task(self, idx: int) -> None:
        target = self.task_targets[idx]
        fields = target.split("|")
        name = fields[0]
        github = fields[1] if len(fields) > 1 else ""

        work_dir = f"{SPECULA_ROOT}/case-studies/{name}"
        Path(work_dir, "spec").mkdir(parents=True, exist_ok=True)
        Path(work_dir, "artifact").mkdir(parents=True, exist_ok=True)

        repo_name = github.split("/")[-1]
        artifact_dir = f"{work_dir}/artifact/{repo_name}"
        dotgit = Path(artifact_dir) / ".git"
        if not dotgit.is_dir() and not dotgit.is_file():
            self.log(f"CLONE {name}: github.com/{github} -> {artifact_dir}")
            if self.dry_run:
                self.log(f"DRY-RUN: git clone --depth 1 https://github.com/{github} {artifact_dir}")
            else:
                proc = subprocess.run(
                    ["git", "clone", "--depth", "1", f"https://github.com/{github}", artifact_dir],
                    stdout=subprocess.PIPE,
                    stderr=subprocess.STDOUT,
                    text=True,
                    check=False,
                )
                lines = proc.stdout.splitlines()
                if lines:  # bash: `git clone ... 2>&1 | tail -1` (raw stdout, not log())
                    print(lines[-1], flush=True)
                if proc.returncode != 0:
                    # set -e parity: kills the setup phase; in a worker thread the
                    # task dies without a status file ("not-started"), like the
                    # bash subshell
                    raise SystemExit(proc.returncode)

        if self.prompt_file and os.path.isfile(self.prompt_file):
            if self.dry_run:
                self.log(f"DRY-RUN: cp {self.prompt_file} -> {work_dir}/.prompt-extra.md")
            else:
                Path(work_dir, ".prompt-extra.md").write_bytes(Path(self.prompt_file).read_bytes())
                self.log(f"PROMPT {name}: wrote .prompt-extra.md")

    # ── worker ──────────────────────────────────────────────────────────────
    def _write_status(self, idx: int, status: str) -> None:
        Path(f"{self.log_dir}/status/{idx}").write_text(status + "\n")

    def run_task(self, idx: int) -> None:
        target = self.task_targets[idx]
        flags = self.task_flags[idx]
        name = target.split("|")[0]
        task_log = f"{self.log_dir}/{name}.log"

        self.setup_task(idx)

        self.log(f"START #{idx + 1} {name}")
        self._write_status(idx, "running")

        cmd = ["bash", f"{SPECULA_ROOT}/scripts/launch/launch_pipeline.sh", f"--claude-alias={self.claude_alias}"]
        if flags:
            cmd += flags.split()  # bash `read -ra` word-splitting: no quote handling
        if self.max_turns > 0:
            cmd.append(f"--max-turns={self.max_turns}")
        cmd.append(target)

        if self.dry_run:
            self.log("DRY-RUN: " + " ".join(cmd))
            self._write_status(idx, "dry-run")
            return

        max_retries = 3
        for attempt in range(1, max_retries + 1):
            start_ts = int(time.time())
            with open(task_log, "w") as lf:
                ok = subprocess.run(cmd, stdout=lf, stderr=subprocess.STDOUT, check=False).returncode == 0
            elapsed = int(time.time()) - start_ts
            if ok:
                self.log(f"DONE  #{idx + 1} {name}  (success, {elapsed}s, attempt {attempt})")
                self._write_status(idx, "success")
                return

            # bash quirk kept for parity: `local rc=$?` ran after the failed `if`
            # *statement*, whose own status is 0 — the FAIL line always says
            # exit=0 (the real code is only in the task log)
            rc = 0

            is_transient = _grep(task_log, _TRANSIENT_RE)
            # stale path kept as-is: the real agent log lives under
            # .specula-output/, so this probe never fires in practice (made
            # run-dir aware in the cutover commit)
            agent_log = f"{SPECULA_ROOT}/case-studies/{name}/agent.log"
            if os.path.isfile(agent_log) and _grep(agent_log, "API Error:"):
                is_transient = True

            if is_transient and attempt < max_retries:
                backoff = 180 * attempt
                self.log(f"RETRY #{idx + 1} {name}  (API error, attempt {attempt}/{max_retries}, backoff {backoff}s)")
                self._sleep(backoff)
                continue

            self.log(f"FAIL  #{idx + 1} {name}  (exit={rc}, {elapsed}s, attempt {attempt})")
            self._write_status(idx, "failed")
            return

        # unreachable in practice (attempt 3's failure returns above) — bash had
        # the same dead tail, kept for parity
        self.log(f"FAIL  #{idx + 1} {name}  (exhausted {max_retries} retries)")
        self._write_status(idx, "failed")

    def _worker(self, idx: int) -> None:
        """Thread target: a SystemExit from setup (clone failure) ends only this
        task — the bash subshell's set -e death, no status file written."""
        with suppress(SystemExit):
            self.run_task(idx)

    # ── main loop ───────────────────────────────────────────────────────────
    def main_loop(self) -> None:
        task_idx = 0
        active: list[threading.Thread] = []
        stopped = False

        while task_idx < len(self.task_targets) or active:
            # reap finished workers (bash: kill -0 sweep)
            active = [t for t in active if t.is_alive()]

            # fill worker slots
            while len(active) < self.workers and task_idx < len(self.task_targets):
                if not self.wait_for_quota():
                    self.log(f"Draining {len(active)} active tasks...")
                    for t in active:
                        t.join()
                    active = []
                    stopped = True
                    break
                t = threading.Thread(target=self._worker, args=(task_idx,))
                t.start()
                active.append(t)
                task_idx += 1
                self._sleep(3)
            if stopped:
                break

            self._sleep(30)

        for t in active:
            t.join()

    def summary(self) -> None:
        self.log("===========================================")
        self.log("SUMMARY")
        total = len(self.task_targets)
        success = failed = other = 0
        for i in range(total):
            name = self.task_targets[i].split("|")[0]
            try:
                s = Path(f"{self.log_dir}/status/{i}").read_text().rstrip("\n")
            except OSError:
                s = "not-started"
            if s == "success":
                success += 1
                self.log(f"  OK   {name}")
            elif s == "failed":
                failed += 1
                self.log(f"  FAIL {name}")
            elif s == "dry-run":
                self.log(f"  DRY  {name}")
            else:
                other += 1
                self.log(f"  ---- {name} ({s})")
        self.log(f"Total={total}  Success={success}  Failed={failed}  Skipped={other}  Resets={self.windows_used}")
        self.log(f"Logs: {self.log_dir}/")
        self.log("===========================================")

    def main(self) -> int:
        self.log("===========================================")
        self.log(f"Specula Scheduler  run={self.run_id}")
        self.log(f"Workers={self.workers}  Threshold={self.threshold}%  MaxWindows={self.max_windows}")
        self.log("===========================================")

        self.load_queue()
        if not self.task_targets:
            self.log("Empty queue")
            return 0

        self.log("--- Setup phase ---")
        for i in range(len(self.task_targets)):
            self.setup_task(i)
        self.log("--- Setup complete ---")

        if self.setup_only:
            self.log("Setup-only mode, exiting")
            return 0

        self.main_loop()
        self.summary()
        return 0

    def run(self, argv: list[str]) -> int:
        rc = self.parse_args(argv)
        if rc is not None:
            return rc

        # forward thresholds to launch_pipeline.sh's internal quota gate (its
        # QUOTA_5H/QUOTA_7D defaults don't read --threshold flags)
        os.environ["QUOTA_5H"] = self.threshold
        os.environ["QUOTA_7D"] = self.threshold_7day

        if self.prompt_file and not self.prompt_file.startswith("/"):
            self.prompt_file = os.path.abspath(self.prompt_file)

        self.run_id = time.strftime("%Y%m%d_%H%M%S")
        self.log_dir = f"{SPECULA_ROOT}/logs/scheduler/{self.run_id}"
        Path(self.log_dir, "status").mkdir(parents=True, exist_ok=True)

        return self.main()


def main(argv: list[str]) -> int:
    return Scheduler().run(argv)


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
