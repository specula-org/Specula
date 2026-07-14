"""Python port of scripts/exp/scheduler.sh (migration step 6).

Overnight batch scheduler: runs queue tasks through launch_pipeline.sh with N
parallel workers, pausing on quota and retrying transient API failures. Every
observable behavior (log lines, status files, summary tallies, exit codes) is
pinned by tests/unit/test_schedulerlib.py and the batch dry-run in tests/e2e.
The cutover changes and wart fixes below are deliberate deviations from the
bash original (git history preserves it).

Cutover changes (per-task isolation, agreed 2026-07-04):
  - every task's pipeline gets --run-id=<scheduler-run>-<n>-<name>: outputs go
    to an isolated runs/<id>/ workspace instead of the canonical
    case-studies/<name>/ dirs (which keep holding the *inputs* this scheduler
    sets up: the artifact clone and .prompt-extra.md). One run dir per task,
    not per scheduler run — the run-scoped artifacts (pipeline.log, run.json)
    live at the run root and would collide across parallel workers.
  - the transient-retry agent.log probe reads the isolated run's real phase-1
    log; the bash probed case-studies/<name>/agent.log, which was never
    written, so that whole retry branch was dead.
  - the FAIL line reports the pipeline's real exit code (bash always said
    exit=0: `local rc=$?` read the failed `if` statement's own status).
  - unparseable usage JSON warns and proceeds like the pipeline's quota gate
    (bash treated it as over-quota and slept through reset windows).
  - queue parsing: an unterminated final line is kept (bash dropped the task);
    a whitespace-only line is blank (a tabs-only line was a phantom task); the
    queue-format help no longer advertises the never-implemented per-task
    prompt_file column.

Wart fixes (step 7, 2026-07-04 — goldens intentionally regenerated):
  - setup runs once, in main()'s setup phase. The bash ran setup_task again
    inside every run_task, doubling the setup logs and rewriting
    .prompt-extra.md mid-run; a clone failure now aborts the scheduler in the
    setup phase (the bash main-scope set -e did the same) instead of also
    having a silent per-task death path.
  - the summary tally counts dry-run tasks (`Dry=N`); the bash printed their
    DRY lines but counted them nowhere, so the tally didn't add up to Total.
  - the exit code is 1 when any task failed (0 otherwise); the bash always
    exited 0, invisible to cron/CI wrappers. Quota-drained ("not-started")
    tasks are a scheduling outcome, not a failure — they don't flip it.
  - setup paths are pathlib joins; the bash string interpolation leaked
    artifacts like `case-studies//artifact/` into logs when a malformed queue
    line yielded an empty name/repo field (identical for well-formed names).

Concurrency: bash forked a subshell per task; here each task runs in a thread
whose only work is spawning the pipeline subprocess, log/status bookkeeping and
backoff sleeps — the actual parallelism is the pipeline child processes, same
as bash.

Sleeps go through the external `sleep` command deliberately, so a test can stub
`sleep` on PATH to run the poll loop instantly (tests/e2e stubs it for the batch
dry-run).

Sanctioned deviations from the bash (agreed 2026-07-04, unit-test pinned):
  - malformed resets_at timestamps: bash's `date -d` died under set -e and took
    the whole scheduler down; _epoch degrades to the 60s floor instead
    (pipelinelib semantics).
  - numeric flags (--workers/--windows/--max-turns/--threshold*) are validated
    at parse time; bash accepted garbage and then hung or spun in arithmetic.
    --workers additionally requires >= 1: bash took 0/negative and the fill
    loop spun forever without ever dispatching a task.
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

SCRIPT_DIR = Path(__file__).resolve().parent  # src/specula
SPECULA_ROOT = SCRIPT_DIR.parent.parent
# usage.sh and the default tasks.queue stay under scripts/exp/
EXP_DIR = SPECULA_ROOT / "scripts" / "exp"

# the bash --help printed the scheduler.sh header comment via sed (lines 2 to
# the first blank line, `# ` stripped); the text is pinned by help_scheduler
HELP = """
Overnight batch scheduler for Specula pipeline.

Runs tasks from a queue file with N parallel workers.
Pauses when usage exceeds threshold, waits for 5-hour window reset, resumes.
Stops after exhausting MAX_WINDOWS resets.

Usage:
  specula batch [options]

Options:
  --workers N         Parallel workers (default: 3)
  --threshold N       5-hour window usage % to pause at (default: 80)
  --threshold-7day N  7-day window usage % to pause at (default: 95)
  --windows N         Max resets to wait through (default: 3)
  --queue FILE     Task queue file (default: scripts/exp/tasks.queue)
  --max-turns N    Max agent turns per task (default: 0 = unlimited)
  --prompt FILE     Copy extra instructions into every task workspace
  --setup-only     Only clone repos and write prompts, don't run pipeline
  --dry-run        Print commands without executing
  --claude-alias NAME  Claude CLI profile (default: claude).
                       Forwarded to specula run so quota checks target the
                       same account.

Queue format (tab-separated):
  name|github|lang|reference[TAB]flags

  - flags: optional specula run flags (e.g. --skip-analysis)
  - --run-id, --isolate, and --no-isolate are reserved for the scheduler

Workspace: every task's pipeline runs isolated under runs/<run>-<n>-<name>/
(scheduler passes --run-id; canonical inputs stay in case-studies/<name>/).
A --prompt file is copied to case-studies/<name>/.prompt-extra.md for ALL
tasks; for per-task prompts, place .prompt-extra.md there yourself first.
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
        self.queue_file = str(EXP_DIR / "tasks.queue")
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
                    if self.workers < 1:  # 0/negative would spin the fill loop forever
                        print(f"ERROR: --workers must be >= 1 (got {v})", file=sys.stderr)
                        return 1
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
            ["bash", str(EXP_DIR / "usage.sh")],
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
            # cutover fix: the bash treated unparseable usage JSON as over-quota
            # (its embedded python died nonzero) and slept through reset windows
            # on garbage input; align with the pipeline gate's WARN + proceed
            self.log("WARN: usage parse failed")
            return True

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
        # cutover fixes over the bash `while IFS= read -r` loop: an unterminated
        # final line is kept (bash silently dropped the task), and a
        # whitespace-only line is blank (bash stripped spaces only, so a
        # tabs-only line became a phantom task with an empty name)
        for line_number, line in enumerate(text.split("\n"), start=1):
            if not line.strip() or re.match(r"^\s*#", line):
                continue
            if "\t" in line:
                target, flags = line.split("\t", 1)
                flags = flags.lstrip("\t")
            else:
                target, flags = line, ""
            for flag in flags.split():
                if flag in {"--run-id", "--isolate", "--no-isolate"} or flag.startswith("--run-id="):
                    self.log(f"Queue line {line_number}: scheduler-reserved flag {flag}")
                    raise SystemExit(1)
            self.task_targets.append(target)
            self.task_flags.append(flags)
        self.log(f"Loaded {len(self.task_targets)} tasks from {self.queue_file}")

    # ── setup: clone repo + write .prompt-extra.md ──────────────────────────
    def setup_task(self, idx: int) -> None:
        target = self.task_targets[idx]
        fields = target.split("|")
        name = fields[0]
        github = fields[1] if len(fields) > 1 else ""

        work_dir = SPECULA_ROOT / "case-studies" / name
        (work_dir / "spec").mkdir(parents=True, exist_ok=True)
        (work_dir / "artifact").mkdir(parents=True, exist_ok=True)

        repo_name = github.split("/")[-1]
        artifact_dir = work_dir / "artifact" / repo_name
        dotgit = artifact_dir / ".git"
        if not dotgit.is_dir() and not dotgit.is_file():
            self.log(f"CLONE {name}: github.com/{github} -> {artifact_dir}")
            if self.dry_run:
                self.log(f"DRY-RUN: git clone --depth 1 https://github.com/{github} {artifact_dir}")
            else:
                proc = subprocess.run(
                    ["git", "clone", "--depth", "1", f"https://github.com/{github}", str(artifact_dir)],
                    stdout=subprocess.PIPE,
                    stderr=subprocess.STDOUT,
                    text=True,
                    check=False,
                )
                lines = proc.stdout.splitlines()
                if lines:  # bash: `git clone ... 2>&1 | tail -1` (raw stdout, not log())
                    print(lines[-1], flush=True)
                if proc.returncode != 0:
                    # set -e parity: aborts the scheduler from main()'s setup
                    # phase before any task starts
                    raise SystemExit(proc.returncode)

        if self.prompt_file and os.path.isfile(self.prompt_file):
            if self.dry_run:
                self.log(f"DRY-RUN: cp {self.prompt_file} -> {work_dir}/.prompt-extra.md")
            else:
                (work_dir / ".prompt-extra.md").write_bytes(Path(self.prompt_file).read_bytes())
                self.log(f"PROMPT {name}: wrote .prompt-extra.md")

    # ── worker ──────────────────────────────────────────────────────────────
    def _write_status(self, idx: int, status: str) -> None:
        Path(f"{self.log_dir}/status/{idx}").write_text(status + "\n")

    def task_run_id(self, idx: int) -> str:
        """The pipeline --run-id for task idx: <scheduler-run>-<n>-<name>,
        sanitized to the run-id charset (it becomes a path segment under
        runs/). The index keeps duplicate queue names from attaching to the
        same run dir."""
        name = self.task_targets[idx].split("|")[0]
        return f"{self.run_id}-{idx + 1}-" + re.sub(r"[^A-Za-z0-9._-]", "_", name)

    def run_task(self, idx: int) -> None:
        target = self.task_targets[idx]
        flags = self.task_flags[idx]
        name = target.split("|")[0]
        task_log = f"{self.log_dir}/{idx + 1}-{name}.log"

        self.log(f"START #{idx + 1} {name}")
        self._write_status(idx, "running")

        # Every task runs in an isolated per-task workspace: runs/<run-id>/.
        # load_queue rejects isolation flags before dispatch, so this generated
        # ID cannot be overridden. One run dir per TASK (not per scheduler run):
        # the run-scoped artifacts (pipeline.log, run.json,
        # pipeline-summary.md) would otherwise collide across workers.
        task_run_id = self.task_run_id(idx)
        cmd = [
            "bash",
            f"{SPECULA_ROOT}/scripts/launch/launch_pipeline.sh",
            f"--claude-alias={self.claude_alias}",
            f"--run-id={task_run_id}",
        ]
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
                rc = subprocess.run(cmd, stdout=lf, stderr=subprocess.STDOUT, check=False).returncode
            elapsed = int(time.time()) - start_ts
            if rc == 0:
                self.log(f"DONE  #{idx + 1} {name}  (success, {elapsed}s, attempt {attempt})")
                self._write_status(idx, "success")
                return
            # cutover fix: the bash FAIL line always said exit=0 (`local rc=$?`
            # read the failed `if` statement's own status); report the real code

            is_transient = _grep(task_log, _TRANSIENT_RE)
            # cutover fix: the bash probed case-studies/<name>/agent.log, a path
            # the pipeline never wrote (phase agent logs live under the work
            # dir); probe the isolated run's actual phase-1 agent log.
            # Best-effort, two known edges: retries reuse the run dir (run-id is
            # per task, not per attempt), so an attempt that dies before phase 1
            # truncates agent.log can read the previous attempt's API error and
            # misclassify a real failure as transient — costs at most the
            # remaining bounded backoffs.
            agent_log = f"{SPECULA_ROOT}/runs/{task_run_id}/{name}/.specula-output/agent.log"
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
                t = threading.Thread(target=self.run_task, args=(task_idx,))
                t.start()
                active.append(t)
                task_idx += 1
                self._sleep(3)
            if stopped:
                break

            self._sleep(30)

        for t in active:
            t.join()

    def summary(self) -> int:
        self.log("===========================================")
        self.log("SUMMARY")
        total = len(self.task_targets)
        success = failed = dry = other = 0
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
                dry += 1
                self.log(f"  DRY  {name}")
            else:
                other += 1
                self.log(f"  ---- {name} ({s})")
        self.log(
            f"Total={total}  Success={success}  Failed={failed}  Dry={dry}  Skipped={other}  Resets={self.windows_used}"
        )
        self.log(f"Logs: {self.log_dir}/")
        self.log("===========================================")
        return failed

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
        # wart fix (step 7): task failures surface in the exit code — the bash
        # always exited 0, so cron/CI wrappers couldn't tell a wiped-out run
        # from a clean one
        return 1 if self.summary() > 0 else 0

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
