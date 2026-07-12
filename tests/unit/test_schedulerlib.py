"""Unit tests for schedulerlib (migration step 6 port of scripts/exp/scheduler.sh).

The batch dry-run in tests/e2e covers the end-to-end observable behavior;
these tests pin the helper-level semantics — the
queue-parsing edges, the quota decision table, the transient-retry classifier
(including the isolated-run agent.log probe the cutover introduced), the FAIL
line's real exit code (the bash always said exit=0), and the sanctioned
deviations (robust _epoch, fail-fast numeric args).

stdlib unittest:  uv run python -m unittest tests.unit.test_schedulerlib -v
"""

from __future__ import annotations

import contextlib
import io
import os
import re
import tempfile
import threading
import time
import unittest
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from specula import schedulerlib as sl


class Sched(sl.Scheduler):
    """Instrumented scheduler: sleeps recorded instead of blocking, log lines
    captured in memory (the tee-to-file contract is golden-pinned, not re-tested
    here)."""

    def __init__(self) -> None:
        super().__init__()
        self.sleeps: list[int] = []
        self.lines: list[str] = []

    def _sleep(self, secs: int) -> None:
        self.sleeps.append(secs)

    def log(self, msg: str) -> None:
        self.lines.append(msg)


class Base(unittest.TestCase):
    def setUp(self) -> None:
        saved = {k: os.environ.get(k) for k in ("CLAUDE_ALIAS", "QUOTA_5H", "QUOTA_7D")}

        def restore() -> None:
            for k, v in saved.items():
                if v is None:
                    os.environ.pop(k, None)
                else:
                    os.environ[k] = v

        self.addCleanup(restore)
        os.environ.pop("CLAUDE_ALIAS", None)

    def tmp(self) -> Path:
        d = tempfile.TemporaryDirectory()
        self.addCleanup(d.cleanup)
        return Path(d.name).resolve()

    def patch_mod(self, name: str, value: Any) -> None:
        module: Any = sl
        old = getattr(module, name)

        def restore() -> None:
            setattr(module, name, old)

        self.addCleanup(restore)
        setattr(module, name, value)

    def sched(self) -> Sched:
        s = Sched()
        s.log_dir = str(self.tmp())
        Path(s.log_dir, "status").mkdir()
        return s


# ── argument parsing ─────────────────────────────────────────────────────────
class TestParseArgs(Base):
    def test_defaults(self) -> None:
        s = Sched()
        self.assertEqual(
            (s.workers, s.threshold, s.threshold_7day, s.max_windows, s.max_turns),
            (3, "80", "95", 3, 0),
        )
        self.assertEqual(s.queue_file, str(sl.EXP_DIR / "tasks.queue"))
        self.assertEqual((s.prompt_file, s.dry_run, s.setup_only, s.claude_alias), ("", False, False, "claude"))

    def test_all_flags_space_style(self) -> None:
        s = Sched()
        rc = s.parse_args(
            [
                "--workers",
                "5",
                "--threshold",
                "70",
                "--threshold-7day",
                "90",
                "--windows",
                "2",
                "--queue",
                "q.tsv",
                "--max-turns",
                "40",
                "--prompt",
                "p.md",
                "--claude-alias",
                "other",
                "--dry-run",
                "--setup-only",
            ]
        )
        self.assertIsNone(rc)
        self.assertEqual((s.workers, s.threshold, s.threshold_7day, s.max_windows), (5, "70", "90", 2))
        self.assertEqual((s.queue_file, s.max_turns, s.prompt_file), ("q.tsv", 40, "p.md"))
        self.assertEqual((s.claude_alias, s.dry_run, s.setup_only), ("other", True, True))

    def test_claude_alias_equals_form(self) -> None:
        s = Sched()
        self.assertIsNone(s.parse_args(["--claude-alias=exp"]))
        self.assertEqual(s.claude_alias, "exp")

    def test_claude_alias_env_default(self) -> None:
        os.environ["CLAUDE_ALIAS"] = "ambient"
        self.assertEqual(Sched().claude_alias, "ambient")

    def test_help_prints_header_and_wins_early(self) -> None:
        s = Sched()
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            rc = s.parse_args(["--help", "--bogus"])  # --bogus never reached
        self.assertEqual(rc, 0)
        self.assertIn("Overnight batch scheduler", out.getvalue())
        self.assertIn("Queue format (tab-separated):", out.getvalue())

    def test_unknown_flag(self) -> None:
        s = Sched()
        err = io.StringIO()
        with contextlib.redirect_stderr(err):
            rc = s.parse_args(["--bogus"])
        self.assertEqual(rc, 1)
        self.assertIn("Unknown: --bogus", err.getvalue())

    def test_missing_value_fails_cleanly(self) -> None:
        # deviation: bash died on set -u ($2 unbound); the port errors out
        for argv in (["--workers"], ["--queue"], ["--claude-alias"]):
            with self.subTest(argv=argv), contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(Sched().parse_args(argv), 1)

    def test_numeric_validation(self) -> None:
        # deviation: bash accepted garbage and hung/spun in arithmetic later
        bad = [
            ["--workers", "abc"],
            ["--windows", "1.5"],
            ["--max-turns", ""],
            ["--threshold", "high"],
            ["--threshold-7day", "9%"],
        ]
        for argv in bad:
            with self.subTest(argv=argv), contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(Sched().parse_args(argv), 1)
        s = Sched()
        self.assertIsNone(s.parse_args(["--threshold", "80.5"]))  # float thresholds fine
        self.assertEqual(s.threshold, "80.5")

    def test_workers_must_be_positive(self) -> None:
        # deviation: bash took --workers 0 (or negative) and the fill loop spun
        # forever without dispatching; the port rejects it at parse time
        for v in ("0", "-3"):
            with self.subTest(v=v):
                err = io.StringIO()
                with contextlib.redirect_stderr(err):
                    self.assertEqual(Sched().parse_args(["--workers", v]), 1)
                self.assertIn("must be >= 1", err.getvalue())
        s = Sched()
        self.assertIsNone(s.parse_args(["--workers", "1"]))
        self.assertEqual(s.workers, 1)


# ── queue parsing ────────────────────────────────────────────────────────────
class TestLoadQueue(Base):
    def load(self, text: str) -> Sched:
        s = self.sched()
        qf = self.tmp() / "tasks.queue"
        qf.write_text(text)
        s.queue_file = str(qf)
        s.load_queue()
        return s

    def test_basic_and_comments(self) -> None:
        s = self.load("# c1\n  # indented\n\n   \na|g/h|Go|ref\nb|i/j|Rust|r2\n")
        self.assertEqual(s.task_targets, ["a|g/h|Go|ref", "b|i/j|Rust|r2"])
        self.assertEqual(s.task_flags, ["", ""])
        self.assertEqual(s.lines[-1], f"Loaded 2 tasks from {s.queue_file}")

    def test_whitespace_only_line_is_blank(self) -> None:
        # cutover fix: the bash blank check stripped spaces only, so a tabs-only
        # line became a phantom task with an empty name (cloning github.com/!)
        s = self.load("\t\t\na|g/h|Go|r\n")
        self.assertEqual(s.task_targets, ["a|g/h|Go|r"])

    def test_first_tab_splits_and_leading_tabs_stripped(self) -> None:
        s = self.load("a|g/h|Go|r\t\t--skip-analysis --max-parallel=2\n")
        self.assertEqual(s.task_flags, ["--skip-analysis --max-parallel=2"])

    def test_third_column_folds_into_flags(self) -> None:
        # the header's per-task prompt_file column was never implemented: the
        # third column survives inside flags (word-split forwards it verbatim)
        s = self.load("a|g/h|Go|r\t--flag-one\tthird-col.md\n")
        self.assertEqual(s.task_flags, ["--flag-one\tthird-col.md"])
        self.assertEqual(s.task_flags[0].split(), ["--flag-one", "third-col.md"])

    def test_unterminated_final_line_kept(self) -> None:
        # cutover fix: bash `while IFS= read -r` silently dropped a final line
        # with no trailing newline — a whole task vanished from the queue
        s = self.load("a|g/h|Go|r\nb|i/j|Rust|r2")
        self.assertEqual(s.task_targets, ["a|g/h|Go|r", "b|i/j|Rust|r2"])

    def test_scheduler_owned_isolation_flags_rejected(self) -> None:
        for flag in ("--run-id", "--run-id=shared", "--isolate", "--no-isolate"):
            with self.subTest(flag=flag):
                s = self.sched()
                qf = self.tmp() / "tasks.queue"
                qf.write_text(f"# comment\n\na|g/h|Go|r\t--agent=codex {flag}\n")
                s.queue_file = str(qf)
                with self.assertRaises(SystemExit) as cm:
                    s.load_queue()
                self.assertEqual(cm.exception.code, 1)
                self.assertEqual(s.lines[-1], f"Queue line 3: scheduler-reserved flag {flag}")

    def test_similar_queue_flag_is_not_reserved(self) -> None:
        s = self.load("a|g/h|Go|r\t--run-id-suffix=shared\n")
        self.assertEqual(s.task_flags, ["--run-id-suffix=shared"])

    def test_missing_queue_file(self) -> None:
        s = self.sched()
        s.queue_file = "/nonexistent/tasks.queue"
        with self.assertRaises(SystemExit) as cm:
            s.load_queue()
        self.assertEqual(cm.exception.code, 1)
        self.assertEqual(s.lines[-1], "Queue file not found: /nonexistent/tasks.queue")


# ── quota gate ───────────────────────────────────────────────────────────────
def _usage_json(u5: float, u7: float, r5: str | None, r7: str | None) -> str:
    five: dict[str, object] = {"utilization": u5}
    seven: dict[str, object] = {"utilization": u7}
    if r5 is not None:
        five["resets_at"] = r5
    if r7 is not None:
        seven["resets_at"] = r7
    import json

    return json.dumps({"five_hour": five, "seven_day": seven})


class TestCheckUsage(Base):
    def gated(self, stub_body: str | None) -> Sched:
        root = self.tmp()
        if stub_body is not None:
            (root / "usage.sh").write_text(stub_body)
        self.patch_mod("EXP_DIR", root)
        return self.sched()

    def json_stub(self, payload: str, rc: int = 0) -> str:
        return f"#!/usr/bin/env bash\ncat <<'J'\n{payload}\nJ\nexit {rc}\n"

    def reset_at(self, s: Sched) -> str | None:
        p = Path(s.log_dir) / ".reset_at"
        return p.read_text() if p.is_file() else None

    def test_under_both(self) -> None:
        s = self.gated(self.json_stub(_usage_json(10, 10, "2099-01-01T00:00:00+00:00", None)))
        self.assertTrue(s.check_usage())
        self.assertIsNone(self.reset_at(s))

    def test_strictly_over_5h(self) -> None:
        s = self.gated(self.json_stub(_usage_json(86, 10, "2099-01-02T00:00:00+00:00", None)))
        self.assertFalse(s.check_usage())
        self.assertEqual(self.reset_at(s), "2099-01-02T00:00:00+00:00")

    def test_at_limit_is_not_over(self) -> None:
        s = self.gated(self.json_stub(_usage_json(80, 95, "2099-01-01T00:00:00+00:00", None)))
        self.assertTrue(s.check_usage())

    def test_over_7d_uses_its_own_threshold(self) -> None:
        s = self.gated(self.json_stub(_usage_json(10, 96, None, "2099-01-08T00:00:00+00:00")))
        self.assertFalse(s.check_usage())
        self.assertEqual(self.reset_at(s), "2099-01-08T00:00:00+00:00")

    def test_both_over_earliest_reset_wins(self) -> None:
        s = self.gated(self.json_stub(_usage_json(86, 96, "2099-01-05T00:00:00+00:00", "2099-01-02T00:00:00+00:00")))
        self.assertFalse(s.check_usage())
        self.assertEqual(self.reset_at(s), "2099-01-02T00:00:00+00:00")

    def test_over_without_resets_at_writes_empty(self) -> None:
        s = self.gated(self.json_stub(_usage_json(86, 10, None, None)))
        self.assertFalse(s.check_usage())
        self.assertEqual(self.reset_at(s), "")

    def test_malformed_json_warns_and_proceeds(self) -> None:
        # cutover fix: bash treated unparseable JSON as over-quota (its embedded
        # python died nonzero) and slept through reset windows on garbage input;
        # aligned with the pipeline gate's WARN + proceed
        for payload in ("not json {", "3", '{"five_hour":{"utilization":"lots"}}'):
            with self.subTest(payload=payload):
                s = self.gated(self.json_stub(payload))
                self.assertTrue(s.check_usage())
                self.assertEqual(s.lines[-1], "WARN: usage parse failed")

    def test_fetch_failure_warns_and_proceeds(self) -> None:
        s = self.gated("#!/usr/bin/env bash\nexit 3\n")
        self.assertTrue(s.check_usage())
        self.assertEqual(s.lines[-1], "WARN: usage fetch failed")

    def test_missing_usage_script_warns_and_proceeds(self) -> None:
        s = self.gated(None)
        self.assertTrue(s.check_usage())
        self.assertEqual(s.lines[-1], "WARN: usage fetch failed")

    def test_usage_json_written_and_alias_forwarded(self) -> None:
        s = self.gated('#!/usr/bin/env bash\necho "{\\"alias\\": \\"$CLAUDE_ALIAS\\"}"\n')
        s.claude_alias = "myalias"
        self.assertTrue(s.check_usage())  # no five_hour/seven_day keys -> under
        self.assertIn('"myalias"', (Path(s.log_dir) / ".usage.json").read_text())


class QuotaSched(Sched):
    """check_usage scripted from a canned answer list."""

    def __init__(self, answers: list[bool]) -> None:
        super().__init__()
        self.answers = list(answers)

    def check_usage(self) -> bool:
        return self.answers.pop(0)


class TestWaitForQuota(Base):
    def quota(self, answers: list[bool], reset_at: str | None = None) -> QuotaSched:
        s = QuotaSched(answers)
        s.log_dir = str(self.tmp())
        if reset_at is not None:
            (Path(s.log_dir) / ".reset_at").write_text(reset_at)
        return s

    def test_under_immediately(self) -> None:
        s = self.quota([True])
        self.assertTrue(s.wait_for_quota())
        self.assertEqual((s.sleeps, s.windows_used), ([], 0))

    def test_past_reset_clamps_to_60(self) -> None:
        s = self.quota([False, True], reset_at="2000-01-01T00:00:00+00:00")
        self.assertTrue(s.wait_for_quota())
        self.assertEqual(s.sleeps, [60])
        self.assertEqual(s.windows_used, 1)
        self.assertIn("sleeping 60s until 2000-01-01T00:00:00+00:00 (reset 1/3)", s.lines[-1])

    def test_no_reset_time_sleeps_600(self) -> None:
        s = self.quota([False, True])
        self.assertTrue(s.wait_for_quota())
        self.assertEqual(s.sleeps, [600])
        self.assertIn("no reset time, sleeping 600s", s.lines[-1])

    def test_future_reset_sleeps_delta_plus_120(self) -> None:
        future = datetime.now(timezone.utc).replace(microsecond=0)
        ts = future.isoformat()
        expect = sl._epoch(ts) - int(time.time()) + 120
        s = self.quota([False, True], reset_at=ts)
        self.assertTrue(s.wait_for_quota())
        self.assertEqual(len(s.sleeps), 1)
        self.assertLessEqual(abs(s.sleeps[0] - expect), 2)

    def test_garbage_reset_at_degrades_to_floor(self) -> None:
        # sanctioned deviation: bash's `date -d` died under set -e
        s = self.quota([False, True], reset_at="not a timestamp")
        self.assertTrue(s.wait_for_quota())
        self.assertEqual(s.sleeps, [60])

    def test_windows_exhaustion_is_strictly_greater(self) -> None:
        s = self.quota([False, False, False], reset_at="2000-01-01T00:00:00+00:00")
        s.max_windows = 1
        self.assertFalse(s.wait_for_quota())
        self.assertEqual(s.sleeps, [60])  # used=1 not > 1 -> one sleep; used=2 > 1 -> stop
        self.assertEqual(s.windows_used, 2)
        self.assertEqual(s.lines[-1], "Max resets (1) exhausted, stopping scheduler")


# ── epoch parsing ────────────────────────────────────────────────────────────
class TestEpoch(Base):
    def test_iso_offset(self) -> None:
        self.assertEqual(sl._epoch("1970-01-01T01:00:00+00:00"), 3600)

    def test_z_suffix(self) -> None:
        self.assertEqual(sl._epoch("1970-01-01T01:00:00Z"), 3600)

    def test_garbage_is_zero(self) -> None:
        self.assertEqual(sl._epoch("soon"), 0)


# ── transient classification ─────────────────────────────────────────────────
class TestTransientGrep(Base):
    def test_patterns(self) -> None:
        hits = ["API Error: 500 boom", "API Error: 529", "Internal server error", "x overloaded_error y", "Overloaded"]
        misses = ["API Error: 404 not found", "all good", "overloaded"]  # case-sensitive, 5xx only
        for text in hits:
            with self.subTest(text=text):
                self.assertRegex(text, sl._TRANSIENT_RE)
        for text in misses:
            with self.subTest(text=text):
                self.assertNotRegex(text, sl._TRANSIENT_RE)

    def test_grep_missing_file_and_bytes(self) -> None:
        self.assertFalse(sl._grep("/nonexistent/x.log", sl._TRANSIENT_RE))
        f = self.tmp() / "x.log"
        f.write_bytes(b"\xff\xfe API Error: 503 \xff\n")
        self.assertTrue(sl._grep(str(f), sl._TRANSIENT_RE))


# ── setup / worker ───────────────────────────────────────────────────────────
class WorkerBase(Base):
    """A patched SPECULA_ROOT tree with a scriptable fake launch_pipeline.sh."""

    def root(self, pipeline_body: str = "#!/usr/bin/env bash\nexit 0\n") -> Path:
        root = self.tmp()
        (root / "scripts" / "launch").mkdir(parents=True)
        (root / "scripts" / "launch" / "launch_pipeline.sh").write_text(pipeline_body)
        (root / "case-studies").mkdir()
        self.patch_mod("SPECULA_ROOT", root)
        return root

    def seed_repo(self, root: Path, name: str, repo: str) -> None:
        (root / "case-studies" / name / "artifact" / repo / ".git").mkdir(parents=True)

    def task(self, s: Sched, target: str, flags: str = "") -> None:
        s.task_targets.append(target)
        s.task_flags.append(flags)


class TestSetupTask(WorkerBase):
    def test_degenerate_empty_target_collapses_paths(self) -> None:
        # wart fix (step 7): pathlib joins — a malformed queue line with an
        # empty name no longer leaks `case-studies//artifact/` into the logs
        # (still garbage-in-garbage-out, but the path is at least well-formed)
        root = self.root()
        s = self.sched()
        s.dry_run = True
        self.task(s, "")
        s.setup_task(0)
        self.assertEqual(s.lines[0], f"CLONE : github.com/ -> {root}/case-studies/artifact")
        self.assertTrue((root / "case-studies" / "spec").is_dir())

    def test_wellformed_target_paths_unchanged(self) -> None:
        # for real names the pathlib join renders byte-identically to the bash
        root = self.root()
        s = self.sched()
        s.dry_run = True
        self.task(s, "footest|foo/bar|Go|r")
        s.setup_task(0)
        self.assertEqual(
            s.lines[0],
            f"CLONE footest: github.com/foo/bar -> {root}/case-studies/footest/artifact/bar",
        )

    def test_git_file_worktree_style_skips_clone(self) -> None:
        root = self.root()
        gitfile = root / "case-studies" / "footest" / "artifact" / "bar" / ".git"
        gitfile.parent.mkdir(parents=True)
        gitfile.write_text("gitdir: elsewhere\n")
        s = self.sched()
        self.task(s, "footest|foo/bar|Go|r")
        s.setup_task(0)
        self.assertEqual([ln for ln in s.lines if ln.startswith("CLONE")], [])

    def test_prompt_copied_only_when_file_exists(self) -> None:
        root = self.root()
        self.seed_repo(root, "footest", "bar")
        s = self.sched()
        self.task(s, "footest|foo/bar|Go|r")
        s.prompt_file = str(self.tmp() / "missing.md")
        s.setup_task(0)  # silently skipped, bash [[ -f ]] parity
        self.assertEqual(s.lines, [])
        pf = self.tmp() / "p.md"
        pf.write_text("extra instructions\n")
        s.prompt_file = str(pf)
        s.setup_task(0)
        self.assertEqual(s.lines[-1], "PROMPT footest: wrote .prompt-extra.md")
        self.assertEqual((root / "case-studies" / "footest" / ".prompt-extra.md").read_text(), "extra instructions\n")

    def test_clone_failure_dies_like_set_e(self) -> None:
        self.root()
        bindir = self.tmp()
        (bindir / "git").write_text("#!/bin/sh\necho 'fatal: nope'\nexit 128\n")
        (bindir / "git").chmod(0o755)
        old_path = os.environ["PATH"]
        self.addCleanup(lambda: os.environ.__setitem__("PATH", old_path))
        os.environ["PATH"] = f"{bindir}:{old_path}"
        s = self.sched()
        self.task(s, "footest|foo/bar|Go|r")
        out = io.StringIO()
        with contextlib.redirect_stdout(out), self.assertRaises(SystemExit) as cm:
            s.setup_task(0)
        self.assertEqual(cm.exception.code, 128)
        self.assertIn("fatal: nope", out.getvalue())  # bash: `... 2>&1 | tail -1`

    def test_clone_failure_aborts_scheduler_before_any_task(self) -> None:
        # wart fix (step 7): setup runs once, in main()'s setup phase — a clone
        # failure there kills the whole scheduler (bash main-scope set -e did
        # the same); no task starts, no status file appears
        self.root()
        bindir = self.tmp()
        (bindir / "git").write_text("#!/bin/sh\nexit 128\n")
        (bindir / "git").chmod(0o755)
        old_path = os.environ["PATH"]
        self.addCleanup(lambda: os.environ.__setitem__("PATH", old_path))
        os.environ["PATH"] = f"{bindir}:{old_path}"
        s = self.sched()
        qf = self.tmp() / "tasks.queue"
        qf.write_text("footest|foo/bar|Go|r\n")
        s.queue_file = str(qf)
        with self.assertRaises(SystemExit) as cm:
            s.main()
        self.assertEqual(cm.exception.code, 128)
        self.assertFalse((Path(s.log_dir) / "status" / "0").exists())
        self.assertEqual([ln for ln in s.lines if ln.startswith("START")], [])

    def test_run_task_does_not_rerun_setup(self) -> None:
        # wart fix (step 7): the bash ran setup_task again inside run_task,
        # doubling the CLONE/PROMPT logs; run_task now only runs the pipeline
        root = self.root("#!/usr/bin/env bash\nexit 0\n")
        s = self.sched()
        pf = self.tmp() / "p.md"
        pf.write_text("extra\n")
        s.prompt_file = str(pf)
        self.task(s, "footest|foo/bar|Go|r")
        s.run_task(0)
        setup_lines = [ln for ln in s.lines if ln.startswith(("CLONE", "PROMPT", "DRY-RUN: git", "DRY-RUN: cp"))]
        self.assertEqual(setup_lines, [])
        self.assertFalse((root / "case-studies" / "footest").exists())


class TestRunTask(WorkerBase):
    def test_success(self) -> None:
        root = self.root('#!/usr/bin/env bash\necho "pipeline ran"\nexit 0\n')
        self.seed_repo(root, "footest", "bar")
        s = self.sched()
        self.task(s, "footest|foo/bar|Go|r")
        s.run_task(0)
        self.assertEqual((Path(s.log_dir) / "status" / "0").read_text(), "success\n")
        self.assertRegex(s.lines[-1], r"^DONE  #1 footest  \(success, \d+s, attempt 1\)$")
        self.assertEqual((Path(s.log_dir) / "1-footest.log").read_text(), "pipeline ran\n")

    def test_dry_run_command_line(self) -> None:
        root = self.root()
        s = self.sched()
        s.run_id = "20990101_000000"
        s.dry_run = True
        s.max_turns = 7
        s.claude_alias = "myalias"
        self.task(s, "footest|foo/bar|Go|Raft demo", "--skip-analysis\t--skip-specgen")
        s.run_task(0)
        self.assertEqual(
            s.lines[-1],
            f"DRY-RUN: bash {root}/scripts/launch/launch_pipeline.sh --claude-alias=myalias"
            " --run-id=20990101_000000-1-footest"
            " --skip-analysis --skip-specgen --max-turns=7 footest|foo/bar|Go|Raft demo",
        )
        self.assertEqual((Path(s.log_dir) / "status" / "0").read_text(), "dry-run\n")

    def test_max_turns_zero_omitted(self) -> None:
        root = self.root()
        s = self.sched()
        s.run_id = "20990101_000000"
        s.dry_run = True
        self.task(s, "footest|foo/bar|Go|r")
        s.run_task(0)
        self.assertEqual(
            s.lines[-1],
            f"DRY-RUN: bash {root}/scripts/launch/launch_pipeline.sh --claude-alias=claude"
            " --run-id=20990101_000000-1-footest footest|foo/bar|Go|r",
        )

    def test_task_run_id_sanitized_and_indexed(self) -> None:
        s = self.sched()
        s.run_id = "20990101_000000"
        s.task_targets = ["we ird|a/b|Go|r", "we ird|a/b|Go|r"]
        s.task_flags = ["", ""]
        # invalid run-id chars replaced; the index keeps duplicate names apart
        self.assertEqual(s.task_run_id(0), "20990101_000000-1-we_ird")
        self.assertEqual(s.task_run_id(1), "20990101_000000-2-we_ird")

    def test_nontransient_fail_reports_real_exit(self) -> None:
        # cutover fix: the bash FAIL line always said exit=0 (`local rc=$?`
        # read the failed `if` statement's own status, not the pipeline's)
        root = self.root('#!/usr/bin/env bash\necho "boom"\nexit 7\n')
        self.seed_repo(root, "footest", "bar")
        s = self.sched()
        self.task(s, "footest|foo/bar|Go|r")
        s.run_task(0)
        self.assertRegex(s.lines[-1], r"^FAIL  #1 footest  \(exit=7, \d+s, attempt 1\)$")
        self.assertEqual((Path(s.log_dir) / "status" / "0").read_text(), "failed\n")
        self.assertEqual(s.sleeps, [])

    def test_transient_retries_then_succeeds(self) -> None:
        root = self.root()
        state = self.tmp() / "n"
        (root / "scripts" / "launch" / "launch_pipeline.sh").write_text(
            "#!/usr/bin/env bash\n"
            f'n=$(cat "{state}" 2>/dev/null || echo 0); n=$((n+1)); printf %s "$n" > "{state}"\n'
            'if [ "$n" -le 1 ]; then echo "API Error: 529 overloaded_error"; exit 1; fi\n'
            "exit 0\n"
        )
        self.seed_repo(root, "footest", "bar")
        s = self.sched()
        self.task(s, "footest|foo/bar|Go|r")
        s.run_task(0)
        self.assertEqual(s.sleeps, [180])
        retries = [ln for ln in s.lines if ln.startswith("RETRY")]
        self.assertRegex(retries[0], r"^RETRY #1 footest  \(API error, attempt 1/3, backoff 180s\)$")
        self.assertRegex(s.lines[-1], r"attempt 2\)$")
        self.assertEqual((Path(s.log_dir) / "status" / "0").read_text(), "success\n")

    def test_transient_attempt3_fails_without_third_backoff(self) -> None:
        root = self.root('#!/usr/bin/env bash\necho "Internal server error"\nexit 1\n')
        self.seed_repo(root, "footest", "bar")
        s = self.sched()
        self.task(s, "footest|foo/bar|Go|r")
        s.run_task(0)
        self.assertEqual(s.sleeps, [180, 360])
        self.assertRegex(s.lines[-1], r"^FAIL  #1 footest  \(exit=1, \d+s, attempt 3\)$")

    def test_agentlog_probe_reads_isolated_run_dir(self) -> None:
        # cutover fix: the probe reads the isolated run's real phase-1 agent log
        # (runs/<task-run-id>/<name>/.specula-output/agent.log); the bash probed
        # case-studies/<name>/agent.log, which the pipeline never wrote
        root = self.root("#!/usr/bin/env bash\nexit 1\n")  # silent failure
        self.seed_repo(root, "footest", "bar")
        s = self.sched()
        s.run_id = "20990101_000000"
        self.task(s, "footest|foo/bar|Go|r")
        (root / "case-studies" / "footest").mkdir(parents=True, exist_ok=True)
        (root / "case-studies" / "footest" / "agent.log").write_text("API Error: 529\n")
        s.run_task(0)
        self.assertEqual(s.sleeps, [])  # the bash's stale location is ignored now
        rundir = root / "runs" / s.task_run_id(0) / "footest" / ".specula-output"
        rundir.mkdir(parents=True)
        (rundir / "agent.log").write_text("API Error: 529\n")
        s.lines.clear()
        s.run_task(0)
        self.assertEqual(s.sleeps, [180, 360])  # isolated run dir honored


# ── main loop / summary ──────────────────────────────────────────────────────
class LoopSched(Sched):
    """run_task replaced by a concurrency recorder; quota scripted."""

    def __init__(self, quota_answers: list[bool] | None = None) -> None:
        super().__init__()
        self.quota_answers = quota_answers
        self.spawned: list[int] = []
        self._cur = 0
        self.peak = 0
        self._cnt_lock = threading.Lock()

    def wait_for_quota(self) -> bool:
        if self.quota_answers is None:
            return True
        return self.quota_answers.pop(0)

    def run_task(self, idx: int) -> None:
        with self._cnt_lock:
            self.spawned.append(idx)
            self._cur += 1
            self.peak = max(self.peak, self._cur)
        time.sleep(0.05)
        with self._cnt_lock:
            self._cur -= 1


class TestMainLoop(Base):
    def test_worker_cap_respected(self) -> None:
        s = LoopSched()
        s.log_dir = str(self.tmp())
        s.workers = 2
        s.task_targets = [f"t{i}|a/b|Go|r" for i in range(5)]
        s.task_flags = [""] * 5
        s.main_loop()
        self.assertEqual(sorted(s.spawned), [0, 1, 2, 3, 4])
        self.assertLessEqual(s.peak, 2)

    def test_quota_stop_drains_and_skips_rest(self) -> None:
        # workers=2: the second slot's quota check happens while task 0 is
        # still alive, so the drain sees 1 active task (with workers=1 the
        # refill can only run after task 0 is reaped — bash identical)
        s = LoopSched(quota_answers=[True, False])
        s.log_dir = str(self.tmp())
        s.workers = 2
        s.task_targets = ["t0|a/b|Go|r", "t1|a/b|Go|r"]
        s.task_flags = ["", ""]
        s.main_loop()
        self.assertEqual(s.spawned, [0])
        self.assertIn("Draining 1 active tasks...", s.lines)


class TestSummary(Base):
    def test_tallies_and_line_formats(self) -> None:
        s = self.sched()
        s.task_targets = ["a|x/y|Go|r", "b|x/y|Go|r", "c|x/y|Go|r", "d|x/y|Go|r", "e|x/y|Go|r"]
        s.windows_used = 2
        for idx, status in ((0, "success"), (1, "failed"), (2, "dry-run"), (4, "weird")):
            (Path(s.log_dir) / "status" / str(idx)).write_text(status + "\n")
        s.summary()
        self.assertIn("  OK   a", s.lines)
        self.assertIn("  FAIL b", s.lines)
        self.assertIn("  DRY  c", s.lines)
        self.assertIn("  ---- d (not-started)", s.lines)
        self.assertIn("  ---- e (weird)", s.lines)
        # wart fix (step 7): Dry counted — the bash tally didn't add up to Total
        self.assertIn("Total=5  Success=1  Failed=1  Dry=1  Skipped=2  Resets=2", s.lines)

    def test_returns_failed_count_for_exit_code(self) -> None:
        # wart fix (step 7): failures surface in the exit code (bash exited 0)
        s = self.sched()
        s.task_targets = ["a|x/y|Go|r", "b|x/y|Go|r", "c|x/y|Go|r"]
        for idx, status in ((0, "success"), (1, "failed"), (2, "failed")):
            (Path(s.log_dir) / "status" / str(idx)).write_text(status + "\n")
        self.assertEqual(s.summary(), 2)
        s2 = self.sched()
        s2.task_targets = ["a|x/y|Go|r"]
        # not-started (quota drain) is a scheduling outcome, not a failure
        self.assertEqual(s2.summary(), 0)


# ── run() wiring ─────────────────────────────────────────────────────────────
class TestRun(Base):
    def test_quota_env_export_and_run_layout(self) -> None:
        root = self.tmp()
        self.patch_mod("SPECULA_ROOT", root)
        qf = root / "tasks.queue"
        qf.write_text("# empty\n")
        s = Sched()
        rc = s.run(["--queue", str(qf), "--threshold", "70", "--threshold-7day", "90"])
        self.assertEqual(rc, 0)
        self.assertEqual((os.environ["QUOTA_5H"], os.environ["QUOTA_7D"]), ("70", "90"))
        self.assertRegex(s.run_id, r"^\d{8}_\d{6}$")
        self.assertEqual(s.log_dir, f"{root}/logs/scheduler/{s.run_id}")
        self.assertTrue((Path(s.log_dir) / "status").is_dir())
        self.assertEqual(s.lines[-1], "Empty queue")

    def test_relative_prompt_resolved_against_cwd(self) -> None:
        root = self.tmp()
        self.patch_mod("SPECULA_ROOT", root)
        qf = root / "tasks.queue"
        qf.write_text("# empty\n")
        old_cwd = os.getcwd()
        self.addCleanup(lambda: os.chdir(old_cwd))
        os.chdir(root)
        s = Sched()
        rc = s.run(["--queue", str(qf), "--prompt", "notes/extra.md"])
        self.assertEqual(rc, 0)
        self.assertEqual(s.prompt_file, f"{root}/notes/extra.md")

    def test_parse_error_short_circuits_before_log_dir(self) -> None:
        root = self.tmp()
        self.patch_mod("SPECULA_ROOT", root)
        s = Sched()
        with contextlib.redirect_stderr(io.StringIO()):
            rc = s.run(["--bogus"])
        self.assertEqual(rc, 1)
        self.assertFalse((root / "logs").exists())


RUN_ID_RE = re.compile(r"^\d{8}_\d{6}$")


if __name__ == "__main__":
    unittest.main()
