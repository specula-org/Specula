"""Unit tests for scripts/launch/pipelinelib.py (migration step 5).

The characterization suite pins end-to-end behavior against the bash goldens;
these tests pin the state-transition and decision tables at function level —
the repair-request state machine, the quota gate, and the small parsing rules
whose edge inputs are awkward to reach through a full pipeline run.

stdlib unittest (no pytest/pip needed — the repo .venv is corrupted; pytest
collects unittest.TestCase natively once step 2 wires CI):

    python3 -m unittest discover -s tests/unit -v
"""

from __future__ import annotations

import contextlib
import io
import os
import subprocess
import sys
import tempfile
import time
import unittest
from pathlib import Path

LAUNCH = Path(__file__).resolve().parents[2] / "scripts" / "launch"
sys.path.insert(0, str(LAUNCH))
import pipelinelib as pl  # noqa: E402

RR_TEMPLATE = """\
---
id: {rr_id}
bug_id: {bug_id}
target: base.tla
status: {status}
round: {round}
---

# Repair Request {rr_id}

body

## History
- created
"""


def make_rr(dirpath: Path, rr_id: str, status: str, bug_id: str = "B-1", round_: int = 1) -> Path:
    f = dirpath / f"{rr_id}.md"
    f.write_text(RR_TEMPLATE.format(rr_id=rr_id, bug_id=bug_id, status=status, round=round_))
    return f


def quiet(fn, *args, **kwargs):
    """Run fn with stdout captured (helpers log progress lines)."""
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        result = fn(*args, **kwargs)
    return result, buf.getvalue()


class TmpCwd(unittest.TestCase):
    """Base: run each test chdir'd into a fresh tempdir (the pipeline resolves
    work dirs off $PWD)."""

    def setUp(self):
        self._old_cwd = os.getcwd()
        self._td = tempfile.TemporaryDirectory()
        self.tmp = Path(self._td.name).resolve()
        os.chdir(self.tmp)
        self.addCleanup(self._td.cleanup)
        self.addCleanup(os.chdir, self._old_cwd)


# ──────────────────────────────────────────────────────────
# RR primitives
# ──────────────────────────────────────────────────────────
class TestRRField(TmpCwd):
    def _write(self, text: str) -> Path:
        f = self.tmp / "RR-x.md"
        f.write_text(text)
        return f

    def test_basic_fields(self):
        f = make_rr(self.tmp, "RR-1", "OPEN", bug_id="DA-1 | pipe", round_=3)
        self.assertEqual(pl.rr_field(f, "id"), "RR-1")
        self.assertEqual(pl.rr_field(f, "status"), "OPEN")
        self.assertEqual(pl.rr_field(f, "round"), "3")
        self.assertEqual(pl.rr_field(f, "bug_id"), "DA-1 | pipe")

    def test_whitespace_stripped_but_internal_kept(self):
        f = self._write("status:   OPEN  \nother: y\n")
        self.assertEqual(pl.rr_field(f, "status"), "OPEN")
        f = self._write("bug_id: a  b\n")
        self.assertEqual(pl.rr_field(f, "bug_id"), "a  b")

    def test_first_match_wins(self):
        f = self._write("status: OPEN\nstatus: RESOLVED\n")
        self.assertEqual(pl.rr_field(f, "status"), "OPEN")

    def test_25_line_window(self):
        pad = "".join(f"k{i}: v\n" for i in range(25))
        f = self._write(pad + "status: LATE\n")
        self.assertEqual(pl.rr_field(f, "status"), "")
        f = self._write("".join(f"k{i}: v\n" for i in range(24)) + "status: EDGE\n")
        self.assertEqual(pl.rr_field(f, "status"), "EDGE")  # line 25: inside the window

    def test_missing_file_and_field(self):
        self.assertEqual(pl.rr_field(self.tmp / "nope.md", "status"), "")
        f = self._write("id: RR-1\n")
        self.assertEqual(pl.rr_field(f, "status"), "")

    def test_prefix_must_be_line_start(self):
        f = self._write("  status: INDENTED\n")
        self.assertEqual(pl.rr_field(f, "status"), "")

    def test_rr_status_strips_all_whitespace(self):
        f = self._write("status: IN REPAIR\n")  # tr -d '[:space:]' collapses internal too
        self.assertEqual(pl.rr_status(f), "INREPAIR")


class TestRRSetStatus(TmpCwd):
    def test_transition_and_history(self):
        f = make_rr(self.tmp, "RR-1", "OPEN")
        pl.rr_set_status(f, "IN_REPAIR", "picked up")
        self.assertEqual(pl.rr_status(f), "IN_REPAIR")
        self.assertTrue(f.read_text().endswith("- picked up\n"))

    def test_appends_even_without_status_line(self):
        f = self.tmp / "RR-1.md"
        f.write_text("id: RR-1\n")
        pl.rr_set_status(f, "OPEN", "note")
        self.assertEqual(f.read_text(), "id: RR-1\n- note\n")

    def test_repairs_missing_trailing_newline(self):
        f = self.tmp / "RR-1.md"
        f.write_text("status: OPEN\nlast line")
        pl.rr_set_status(f, "RESOLVED", "done")
        self.assertEqual(f.read_text(), "status: RESOLVED\nlast line\n- done\n")

    def test_rewrites_only_first_status(self):
        f = self.tmp / "RR-1.md"
        f.write_text("status: OPEN\nstatus: RESOLVED\n")
        pl.rr_set_status(f, "IN_REPAIR", "n")
        self.assertEqual(f.read_text(), "status: IN_REPAIR\nstatus: RESOLVED\n- n\n")

    def test_status_past_window_untouched(self):
        pad = "".join(f"k{i}: v\n" for i in range(25))
        f = self.tmp / "RR-1.md"
        f.write_text(pad + "status: LATE\n")
        pl.rr_set_status(f, "OPEN", "n")
        self.assertIn("status: LATE\n", f.read_text())


# ──────────────────────────────────────────────────────────
# Quota gate
# ──────────────────────────────────────────────────────────
def usage(u5, u7, r5="2099-01-01T00:00:00+00:00", r7="2099-01-08T00:00:00+00:00") -> str:
    import json

    d = {}
    if u5 is not None:
        d["five_hour"] = {"utilization": u5, **({"resets_at": r5} if r5 else {})}
    if u7 is not None:
        d["seven_day"] = {"utilization": u7, **({"resets_at": r7} if r7 else {})}
    return json.dumps(d)


class TestQuotaCheck(unittest.TestCase):
    def check(self, j, q5="85", q7="95"):
        return pl._quota_check(j, q5, q7)

    def test_under_both(self):
        self.assertEqual(self.check(usage(50, 50)), "ok")

    def test_at_limit_is_ok(self):
        self.assertEqual(self.check(usage(85, 95)), "ok")  # strictly >

    def test_over_5h(self):
        self.assertEqual(self.check(usage(86, 50)), "5h=86% (limit 85%) resets_at=2099-01-01T00:00:00+00:00")

    def test_over_7d(self):
        self.assertEqual(self.check(usage(50, 96)), "7d=96% (limit 95%) resets_at=2099-01-08T00:00:00+00:00")

    def test_5h_checked_before_7d(self):
        self.assertTrue(self.check(usage(86, 96)).startswith("5h="))

    def test_float_utilization(self):
        self.assertTrue(self.check(usage(85.1, 50)).startswith("5h=85.1%"))

    def test_null_and_missing_sections(self):
        self.assertEqual(self.check('{"five_hour": null, "seven_day": null}'), "ok")
        self.assertEqual(self.check("{}"), "ok")
        self.assertEqual(self.check('{"five_hour": {"utilization": null}}'), "ok")

    def test_missing_resets_at_message_ends_empty(self):
        self.assertEqual(self.check(usage(86, 50, r5=None)), "5h=86% (limit 85%) resets_at=")

    def test_parse_failures_return_none(self):
        self.assertIsNone(self.check("not json {"))
        self.assertIsNone(self.check(usage("86", 50)))  # string utilization: bash TypeError
        self.assertIsNone(self.check(usage(86, 50), q5="abc"))  # garbage threshold


class TestEpoch(unittest.TestCase):
    def test_offset_and_z(self):
        self.assertEqual(pl._epoch("1970-01-01T00:02:00+00:00"), 120)
        self.assertEqual(pl._epoch("1970-01-01T00:02:00Z"), 120)  # py3.10 fromisoformat lacks Z

    def test_garbage_is_zero(self):
        self.assertEqual(pl._epoch("soon"), 0)  # → negative wait → 60s floor upstream


class TestWaitForQuota(TmpCwd):
    def gate(self, json_text=None, exit_code=0, max_waits="1", q5="85", q7="95", script_body=None):
        """Run wait_for_quota against a stub usage.sh; returns (rc, sleeps, out).
        The abort path raises SystemExit(1) — folded into rc so every test can
        assert on the recorded sleeps with a single call."""
        script = self.tmp / "usage.sh"
        if script_body is not None:
            script.write_bytes(script_body)
        elif json_text is None:
            script.write_text(f"#!/usr/bin/env bash\nexit {exit_code}\n")
        else:
            script.write_text(f"#!/usr/bin/env bash\ncat <<'J'\n{json_text}\nJ\n")
        script.chmod(0o755)
        sleeps = []
        buf = io.StringIO()
        try:
            with contextlib.redirect_stdout(buf):
                rc = pl.wait_for_quota(
                    usage_script=script,
                    q5=q5,
                    q7=q7,
                    max_waits=max_waits,
                    claude_alias="claude",
                    sleep_fn=sleeps.append,
                )
        except SystemExit as e:
            rc = e.code
        return rc, sleeps, buf.getvalue()

    def test_missing_script_proceeds_silently(self):
        rc, out = quiet(
            pl.wait_for_quota,
            usage_script=self.tmp / "nope.sh",
            q5="85",
            q7="95",
            max_waits="1",
            claude_alias="claude",
            sleep_fn=lambda s: None,
        )
        self.assertEqual((rc, out), (0, ""))

    def test_fetch_fail_warns_and_proceeds(self):
        rc, _, out = self.gate(exit_code=3)
        self.assertEqual(rc, 0)
        self.assertIn("usage fetch failed", out)

    def test_parse_fail_warns_and_proceeds(self):
        rc, _, out = self.gate("not json")
        self.assertEqual(rc, 0)
        self.assertIn("usage parse failed", out)

    def test_under_proceeds(self):
        rc, sleeps, _ = self.gate(usage(50, 50))
        self.assertEqual((rc, sleeps), (0, []))

    def test_nonutf8_output_is_a_parse_failure(self):
        # bash: undecodable bytes broke the `python3 -c` heredoc → WARN + proceed;
        # the gate must never abort the run on garbage usage output
        rc, _, out = self.gate(script_body=b"#!/usr/bin/env bash\nprintf '\\xff\\xfe{bad}'\n")
        self.assertEqual(rc, 0)
        self.assertIn("usage parse failed", out)

    def test_over_aborts_after_max_waits(self):
        rc, _, out = self.gate(usage(86, 50))
        self.assertEqual(rc, 1)
        self.assertIn("quota still over limit", out)

    def test_over_sleep_derived_from_resets_at(self):
        future = time.strftime("%Y-%m-%dT%H:%M:%S+00:00", time.gmtime(time.time() + 1000))
        rc, sleeps, _ = self.gate(usage(86, 50, r5=future))
        self.assertEqual(rc, 1)
        self.assertEqual(len(sleeps), 1)
        self.assertTrue(1000 - 60 + 120 <= sleeps[0] <= 1000 + 120 + 5)

    def test_no_resets_at_sleeps_600(self):
        rc, sleeps, _ = self.gate(usage(86, 50, r5=None))
        self.assertEqual(rc, 1)
        self.assertEqual(sleeps, [600])

    def test_past_resets_at_clamps_to_60(self):
        rc, sleeps, _ = self.gate(usage(86, 50, r5="2000-01-01T00:00:00+00:00"))
        self.assertEqual(rc, 1)
        self.assertEqual(sleeps, [60])

    def test_recovers_when_usage_drops(self):
        """Over once, then under: one sleep, then proceed (no abort)."""
        script = self.tmp / "usage.sh"
        flag = self.tmp / "called"
        script.write_text(
            "#!/usr/bin/env bash\n"
            f'if [ -e "{flag}" ]; then\n'
            f"cat <<'J'\n{usage(50, 50)}\nJ\n"
            "else\n"
            f'touch "{flag}"\n'
            f"cat <<'J'\n{usage(86, 50, r5=None)}\nJ\n"
            "fi\n"
        )
        script.chmod(0o755)
        sleeps = []
        rc, out = quiet(
            pl.wait_for_quota,
            usage_script=script,
            q5="85",
            q7="95",
            max_waits="6",
            claude_alias="claude",
            sleep_fn=sleeps.append,
        )
        self.assertEqual(rc, 0)
        self.assertEqual(sleeps, [600])
        self.assertIn("wait 1/6", out)


# ──────────────────────────────────────────────────────────
# Pipeline helpers
# ──────────────────────────────────────────────────────────
def make_pipeline(targets: list[str], **attrs) -> pl.Pipeline:
    p = pl.Pipeline()
    p.targets = list(targets)
    for k, v in attrs.items():
        setattr(p, k, v)
    return p


class TestParsing(TmpCwd):
    def test_extract_names_trims_and_splits_pipe(self):
        p = make_pipeline(["  braft |brpc/braft|C++|Raft", "cometbft"])
        self.assertEqual(p.extract_names(), ["braft", "cometbft"])

    def test_extract_names_flattens_internal_whitespace(self):
        # bash re-split names on whitespace (echo+read -ra); kept faithfully
        p = make_pipeline(["two words|x|y|z"])
        self.assertEqual(p.extract_names(), ["two", "words"])

    def test_parse_args_skips_and_values(self):
        p = pl.Pipeline()
        rc = p.parse_args(
            ["--skip-analysis", "--skip-repair-loop", "--max-repair-rounds=2", "--max-parallel=4", "t|g|l|r"]
        )
        self.assertIsNone(rc)
        self.assertTrue(p.skip_analysis)
        self.assertTrue(p.skip_repair_loop)
        self.assertEqual(p.max_repair_rounds, "2")
        self.assertEqual(p.max_parallel, "4")
        self.assertEqual(p.targets, ["t|g|l|r"])

    def test_parse_args_unknown_option(self):
        p = pl.Pipeline()
        rc, out = quiet(p.parse_args, ["--bogus"])
        self.assertEqual(rc, 1)
        self.assertIn("Unknown option: --bogus", out)

    def test_parse_args_help(self):
        p = pl.Pipeline()
        rc, out = quiet(p.parse_args, ["--help"])
        self.assertEqual(rc, 0)
        self.assertIn("Full Specula pipeline", out)

    def test_default_target_is_cwd_basename(self):
        p = pl.Pipeline()
        self.assertIsNone(p.parse_args([]))
        self.assertEqual(p.targets, [self.tmp.name])

    def test_max_turns_verbatim(self):
        p = pl.Pipeline()
        p.parse_args(["--max-turns=abc", "t"])
        self.assertEqual(p.max_turns, "abc")

    def test_get_work_dir_single_vs_batch(self):
        single = make_pipeline(["a|x|y|z"])
        self.assertEqual(single.get_work_dir("a"), f"{self.tmp}/.specula-output")
        batch = make_pipeline(["a|x|y|z", "b|x|y|z"])
        self.assertEqual(batch.get_work_dir("a"), f"{self.tmp}/a/.specula-output")


class RRDirCase(TmpCwd):
    """Base with a seeded single-target repair dir."""

    def setUp(self):
        super().setUp()
        self.p = make_pipeline(["footest|g|l|r"])
        self.rr_dir = self.tmp / ".specula-output" / "spec" / "repair-requests"
        self.rr_dir.mkdir(parents=True)


class TestRepairPredicates(RRDirCase):
    def test_no_dir_no_requests(self):
        p = make_pipeline(["other|g|l|r"])
        self.assertFalse(p.has_any_request())
        self.assertFalse(p.repair_work_remaining())
        self.assertEqual(p.repair_state_sig(), "")

    def test_terminal_statuses(self):
        for status, remaining in [
            ("OPEN", True),
            ("REOPENED", True),
            ("RECHECK", True),
            ("IN_REPAIR", True),
            ("RESOLVED", False),
            ("DEFERRED", False),
        ]:
            for f in self.rr_dir.glob("RR-*.md"):
                f.unlink()
            make_rr(self.rr_dir, "RR-1", status)
            self.assertTrue(self.p.has_any_request())
            self.assertEqual(self.p.repair_work_remaining(), remaining, status)

    def test_mixed_terminal_and_open(self):
        make_rr(self.rr_dir, "RR-1", "RESOLVED")
        make_rr(self.rr_dir, "RR-2", "OPEN")
        self.assertTrue(self.p.repair_work_remaining())

    def test_sig_tracks_status_and_round(self):
        f = make_rr(self.rr_dir, "RR-1", "OPEN", round_=1)
        make_rr(self.rr_dir, "RR-2", "RECHECK", round_=2)
        sig = self.p.repair_state_sig()
        self.assertEqual(sig, "RR-1.md:OPEN:1\nRR-2.md:RECHECK:2")
        pl.rr_set_status(f, "RECHECK", "n")
        self.assertNotEqual(self.p.repair_state_sig(), sig)

    def test_reset_stale_only_touches_in_repair(self):
        stale = make_rr(self.rr_dir, "RR-1", "IN_REPAIR")
        untouched = make_rr(self.rr_dir, "RR-2", "RECHECK")
        _, out = quiet(self.p.reset_stale_in_repair)
        self.assertEqual(pl.rr_status(stale), "OPEN")
        self.assertEqual(pl.rr_status(untouched), "RECHECK")
        self.assertIn("reset RR-1.md IN_REPAIR -> OPEN (crash recovery)", out)
        self.assertIn("- reset (orchestrator): repair phase did not complete; retrying", stale.read_text())

    def test_reset_stale_noop_in_dry_run(self):
        stale = make_rr(self.rr_dir, "RR-1", "IN_REPAIR")
        self.p.dry_run = True
        _, out = quiet(self.p.reset_stale_in_repair)
        self.assertEqual(pl.rr_status(stale), "IN_REPAIR")
        self.assertEqual(out, "")


class TestLedger(RRDirCase):
    def test_ledger_rows_and_pipe_escape(self):
        make_rr(self.rr_dir, "RR-1", "OPEN", bug_id="DA-1 | pipes", round_=1)
        make_rr(self.rr_dir, "RR-2", "RESOLVED", bug_id="DA-2", round_=3)
        self.p.regenerate_ledger()
        text = (self.tmp / ".specula-output" / "spec" / "repair-ledger.md").read_text()
        self.assertIn("# Repair Ledger — footest", text)
        self.assertIn("| RR-1 | DA-1 \\| pipes | base.tla | OPEN | 1 |", text)
        self.assertIn("| RR-2 | DA-2 | base.tla | RESOLVED | 3 |", text)

    def test_no_requests_no_ledger(self):
        self.p.regenerate_ledger()
        self.assertFalse((self.tmp / ".specula-output" / "spec" / "repair-ledger.md").exists())

    def test_dry_run_noop(self):
        make_rr(self.rr_dir, "RR-1", "OPEN")
        self.p.dry_run = True
        self.p.regenerate_ledger()
        self.assertFalse((self.tmp / ".specula-output" / "spec" / "repair-ledger.md").exists())

    def test_status_file_count_prefix_quirk(self):
        # grep -lE '^status:[[:space:]]*RESOLVED' matches as a PREFIX — RESOLVEDX
        # counts too. Kept faithfully; pinned so a "fix" is a conscious decision.
        f1 = make_rr(self.rr_dir, "RR-1", "RESOLVEDX")
        f2 = make_rr(self.rr_dir, "RR-2", "OPEN")
        self.assertEqual(pl.Pipeline._status_file_count([f1, f2], "RESOLVED"), 1)

    def test_status_file_count_scans_whole_file(self):
        # unlike rr_status's 25-line window, the summary grep sees the whole file
        pad = "".join(f"k{i}: v\n" for i in range(30))
        f = self.rr_dir / "RR-1.md"
        f.write_text(pad + "status: DEFERRED\n")
        self.assertEqual(pl.Pipeline._status_file_count([f], "DEFERRED"), 1)


# ──────────────────────────────────────────────────────────
# Exit-code and error-path parity (bash set -e / set -u / pipefail)
# ──────────────────────────────────────────────────────────
class TestRunLauncherExitCodes(TmpCwd):
    def _launch(self, body: str) -> int:
        (self.tmp / "fake.sh").write_text(body)
        p = make_pipeline(["t|g|l|r"])
        self.addCleanup(setattr, pl, "SCRIPT_DIR", pl.SCRIPT_DIR)
        pl.SCRIPT_DIR = self.tmp
        with self.assertRaises(SystemExit) as ctx:
            p._run_launcher("fake.sh", [])
        return ctx.exception.code

    def test_signal_death_maps_to_128_plus_n(self):
        # bash set -e reported a SIGTERM'd launcher as 143, not the mod-256
        # wraparound 241 — schedulers classify kills by 128+N
        self.assertEqual(self._launch("kill -TERM $$\n"), 143)

    def test_plain_failure_passes_through(self):
        self.assertEqual(self._launch("exit 7\n"), 7)


class TestSingleTargetGuards(TmpCwd):
    def test_empty_name_aborts_before_phases(self):
        # bash died at `names[0]: unbound variable` (set -u) before any phase;
        # the port must fail fast too, not run the pipeline with zero names
        p = make_pipeline(["|org/repo|Go|ref"])
        buf = io.StringIO()
        with self.assertRaises(SystemExit) as ctx, contextlib.redirect_stdout(buf):
            p.main()
        self.assertEqual(ctx.exception.code, 1)
        self.assertIn("ERROR: no target name parsed", buf.getvalue())
        self.assertNotIn("PHASE 1", buf.getvalue())

    def test_absolute_name_does_not_escape_case_studies(self):
        # bash string concat kept an absolute name under case-studies/ (no cd);
        # a pathlib join would discard the prefix and chdir into the named dir
        abs_case = self.tmp / "abs_case"
        abs_case.mkdir()
        p = make_pipeline(
            [f"{abs_case}|org/repo|Go|ref"],
            dry_run=True,
            skip_analysis=True,
            skip_specgen=True,
            skip_harness=True,
            skip_validation=True,
            skip_confirmation=True,
            skip_classification=True,
            skip_repair_loop=True,
        )
        rc, out = quiet(p.main)
        self.assertEqual(rc, 0)
        self.assertNotIn("Single target: cd to", out)
        self.assertEqual(os.getcwd(), str(self.tmp))


class TestLogicalCwd(TmpCwd):
    def setUp(self):
        super().setUp()
        old_pwd = os.environ.get("PWD")

        def restore():
            if old_pwd is None:
                os.environ.pop("PWD", None)
            else:
                os.environ["PWD"] = old_pwd

        self.addCleanup(restore)

    def test_symlink_component_preserved(self):
        # bash $PWD keeps the path you cd'd through; getcwd resolves symlinks
        real = self.tmp / "mysys"
        real.mkdir()
        link = self.tmp / "work"
        link.symlink_to(real)
        os.chdir(link)
        os.environ["PWD"] = str(link)
        self.assertEqual(pl._logical_cwd(), link)
        p = pl.Pipeline()
        self.assertIsNone(p.parse_args([]))
        self.assertEqual(p.targets, ["work"])  # bash `basename "$PWD"`

    def test_stale_pwd_falls_back_to_getcwd(self):
        os.environ["PWD"] = "/definitely/not/here"
        self.assertEqual(pl._logical_cwd(), Path.cwd())


class TestMainTeeTeardown(TmpCwd):
    """End-to-end pins for the `main 2>&1 | tee` teardown, driven as a
    subprocess because the entry dup2s the real fds 1/2."""

    def _run_entry(self, patch: str) -> subprocess.CompletedProcess:
        d = self.tmp / "driver.py"
        d.write_text(
            "import sys\n"
            f"sys.path.insert(0, {str(LAUNCH)!r})\n"
            "import pipelinelib as pl\n"
            f"{patch}\n"
            "sys.exit(pl.main(['t|g|l|r']))\n"
        )
        return subprocess.run([sys.executable, str(d)], cwd=self.tmp, capture_output=True, text=True)

    def test_unexpected_exception_traceback_reaches_log(self):
        # bash set -e left the failing command's stderr in pipeline.log; an
        # escaping exception must not die silently behind the devnull teardown
        r = self._run_entry(
            "def boom(self):\n    print('pre-crash progress')\n    raise ValueError('boom')\npl.Pipeline.main = boom"
        )
        self.assertEqual(r.returncode, 1)
        self.assertIn("ValueError: boom", r.stdout)  # traceback flowed through the tee
        log_text = (self.tmp / ".specula-output" / "pipeline.log").read_text()
        self.assertIn("pre-crash progress", log_text)
        self.assertIn("ValueError: boom", log_text)

    def test_failing_tee_fails_the_pipeline(self):
        # bash pipefail: `main 2>&1 | tee log` exited non-zero when tee could
        # not write the log, even though main succeeded
        out = self.tmp / ".specula-output"
        out.mkdir()
        logf = out / "pipeline.log"
        logf.write_text("")
        logf.chmod(0o444)
        self.addCleanup(logf.chmod, 0o644)
        r = self._run_entry("pl.Pipeline.main = lambda self: 0")
        self.assertEqual(r.returncode, 1)


if __name__ == "__main__":
    unittest.main()
