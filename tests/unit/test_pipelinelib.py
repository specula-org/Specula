"""Unit tests for specula.pipelinelib (migration step 5).

The end-to-end CLI chain is covered by tests/e2e; these tests pin the
state-transition and decision tables at function level —
the repair-request state machine, the quota gate, and the small parsing rules
whose edge inputs are awkward to reach through a full pipeline run.

stdlib unittest, collected natively by pytest; imports the installed package:

    uv run python -m unittest discover -s tests/unit -v
"""

from __future__ import annotations

import contextlib
import io
import os
import signal
import subprocess
import sys
import tempfile
import threading
import time
import unittest
from collections.abc import Callable
from pathlib import Path
from typing import Any

SRC = Path(__file__).resolve().parents[2] / "src"

from specula import pipelinelib as pl
from specula.phaselib import _logical_cwd

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


def quiet(fn: Callable[..., Any], *args: Any, **kwargs: Any) -> tuple[Any, str]:
    """Run fn with stdout captured (helpers log progress lines)."""
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        result = fn(*args, **kwargs)
    return result, buf.getvalue()


class TmpCwd(unittest.TestCase):
    """Base: run each test chdir'd into a fresh tempdir (the pipeline resolves
    work dirs off $PWD)."""

    def setUp(self) -> None:
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

    def test_basic_fields(self) -> None:
        f = make_rr(self.tmp, "RR-1", "OPEN", bug_id="DA-1 | pipe", round_=3)
        self.assertEqual(pl.rr_field(f, "id"), "RR-1")
        self.assertEqual(pl.rr_field(f, "status"), "OPEN")
        self.assertEqual(pl.rr_field(f, "round"), "3")
        self.assertEqual(pl.rr_field(f, "bug_id"), "DA-1 | pipe")

    def test_whitespace_stripped_but_internal_kept(self) -> None:
        f = self._write("status:   OPEN  \nother: y\n")
        self.assertEqual(pl.rr_field(f, "status"), "OPEN")
        f = self._write("bug_id: a  b\n")
        self.assertEqual(pl.rr_field(f, "bug_id"), "a  b")

    def test_first_match_wins(self) -> None:
        f = self._write("status: OPEN\nstatus: RESOLVED\n")
        self.assertEqual(pl.rr_field(f, "status"), "OPEN")

    def test_25_line_window(self) -> None:
        pad = "".join(f"k{i}: v\n" for i in range(25))
        f = self._write(pad + "status: LATE\n")
        self.assertEqual(pl.rr_field(f, "status"), "")
        f = self._write("".join(f"k{i}: v\n" for i in range(24)) + "status: EDGE\n")
        self.assertEqual(pl.rr_field(f, "status"), "EDGE")  # line 25: inside the window

    def test_missing_file_and_field(self) -> None:
        self.assertEqual(pl.rr_field(self.tmp / "nope.md", "status"), "")
        f = self._write("id: RR-1\n")
        self.assertEqual(pl.rr_field(f, "status"), "")

    def test_prefix_must_be_line_start(self) -> None:
        f = self._write("  status: INDENTED\n")
        self.assertEqual(pl.rr_field(f, "status"), "")

    def test_rr_status_strips_all_whitespace(self) -> None:
        f = self._write("status: IN REPAIR\n")  # tr -d '[:space:]' collapses internal too
        self.assertEqual(pl.rr_status(f), "INREPAIR")


class TestRRSetStatus(TmpCwd):
    def test_transition_and_history(self) -> None:
        f = make_rr(self.tmp, "RR-1", "OPEN")
        pl.rr_set_status(f, "IN_REPAIR", "picked up")
        self.assertEqual(pl.rr_status(f), "IN_REPAIR")
        self.assertTrue(f.read_text().endswith("- picked up\n"))

    def test_appends_even_without_status_line(self) -> None:
        f = self.tmp / "RR-1.md"
        f.write_text("id: RR-1\n")
        pl.rr_set_status(f, "OPEN", "note")
        self.assertEqual(f.read_text(), "id: RR-1\n- note\n")

    def test_repairs_missing_trailing_newline(self) -> None:
        f = self.tmp / "RR-1.md"
        f.write_text("status: OPEN\nlast line")
        pl.rr_set_status(f, "RESOLVED", "done")
        self.assertEqual(f.read_text(), "status: RESOLVED\nlast line\n- done\n")

    def test_rewrites_only_first_status(self) -> None:
        f = self.tmp / "RR-1.md"
        f.write_text("status: OPEN\nstatus: RESOLVED\n")
        pl.rr_set_status(f, "IN_REPAIR", "n")
        self.assertEqual(f.read_text(), "status: IN_REPAIR\nstatus: RESOLVED\n- n\n")

    def test_status_past_window_untouched(self) -> None:
        pad = "".join(f"k{i}: v\n" for i in range(25))
        f = self.tmp / "RR-1.md"
        f.write_text(pad + "status: LATE\n")
        pl.rr_set_status(f, "OPEN", "n")
        self.assertIn("status: LATE\n", f.read_text())


# ──────────────────────────────────────────────────────────
# Quota gate
# ──────────────────────────────────────────────────────────
def usage(
    u5: Any,
    u7: Any,
    r5: str | None = "2099-01-01T00:00:00+00:00",
    r7: str | None = "2099-01-08T00:00:00+00:00",
    *,
    u7_opus: Any = None,
    u7_sonnet: Any = None,
    r7_opus: str | None = "2099-01-09T00:00:00+00:00",
    r7_sonnet: str | None = "2099-01-10T00:00:00+00:00",
) -> str:
    import json

    d = {}
    if u5 is not None:
        d["five_hour"] = {"utilization": u5, **({"resets_at": r5} if r5 else {})}
    if u7 is not None:
        d["seven_day"] = {"utilization": u7, **({"resets_at": r7} if r7 else {})}
    if u7_opus is not None:
        d["seven_day_opus"] = {"utilization": u7_opus, **({"resets_at": r7_opus} if r7_opus else {})}
    if u7_sonnet is not None:
        d["seven_day_sonnet"] = {"utilization": u7_sonnet, **({"resets_at": r7_sonnet} if r7_sonnet else {})}
    return json.dumps(d)


class TestQuotaCheck(unittest.TestCase):
    def check(self, j: str, q5: str = "85", q7: str = "95") -> Any:
        return pl._quota_check(j, q5, q7)

    def test_under_both(self) -> None:
        self.assertEqual(self.check(usage(50, 50)), "ok")

    def test_at_limit_is_ok(self) -> None:
        self.assertEqual(self.check(usage(85, 95)), "ok")  # strictly >

    def test_over_5h(self) -> None:
        self.assertEqual(self.check(usage(86, 50)), "5h=86% (limit 85%) resets_at=2099-01-01T00:00:00+00:00")

    def test_over_7d(self) -> None:
        self.assertEqual(self.check(usage(50, 96)), "7d=96% (limit 95%) resets_at=2099-01-08T00:00:00+00:00")

    def test_over_7d_opus_uses_7d_threshold(self) -> None:
        self.assertEqual(
            self.check(usage(50, 50, u7_opus=96)),
            "7d_opus=96% (limit 95%) resets_at=2099-01-09T00:00:00+00:00",
        )

    def test_over_7d_sonnet_uses_7d_threshold(self) -> None:
        self.assertEqual(
            self.check(usage(50, 50, u7_sonnet=96)),
            "7d_sonnet=96% (limit 95%) resets_at=2099-01-10T00:00:00+00:00",
        )

    def test_generic_7d_is_checked_before_model_windows(self) -> None:
        self.assertTrue(self.check(usage(50, 96, u7_opus=99, u7_sonnet=99)).startswith("7d="))

    def test_5h_checked_before_7d(self) -> None:
        self.assertTrue(self.check(usage(86, 96)).startswith("5h="))

    def test_float_utilization(self) -> None:
        self.assertTrue(self.check(usage(85.1, 50)).startswith("5h=85.1%"))

    def test_null_and_missing_sections(self) -> None:
        self.assertEqual(self.check('{"five_hour": null, "seven_day": null}'), "ok")
        self.assertEqual(self.check("{}"), "ok")
        self.assertEqual(self.check('{"five_hour": {"utilization": null}}'), "ok")

    def test_missing_resets_at_message_ends_empty(self) -> None:
        self.assertEqual(self.check(usage(86, 50, r5=None)), "5h=86% (limit 85%) resets_at=")

    def test_parse_failures_return_none(self) -> None:
        self.assertIsNone(self.check("not json {"))
        self.assertIsNone(self.check(usage("86", 50)))  # string utilization: bash TypeError
        # a garbage threshold still degrades to parse-fail at this layer, but
        # parse_args rejects it before the gate ever runs (wart fix, step 7)
        self.assertIsNone(self.check(usage(86, 50), q5="abc"))


class TestEpoch(unittest.TestCase):
    def test_offset_and_z(self) -> None:
        self.assertEqual(pl._epoch("1970-01-01T00:02:00+00:00"), 120)
        self.assertEqual(pl._epoch("1970-01-01T00:02:00Z"), 120)  # py3.10 fromisoformat lacks Z

    def test_garbage_is_zero(self) -> None:
        self.assertEqual(pl._epoch("soon"), 0)  # → negative wait → 60s floor upstream


class TestWaitForQuota(TmpCwd):
    def gate(
        self,
        json_text: str | None = None,
        exit_code: int = 0,
        max_waits: str = "1",
        q5: str = "85",
        q7: str = "95",
        script_body: bytes | None = None,
    ) -> tuple[Any, list[Any], str]:
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
        sleeps: list[float] = []
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
            rc = e.code if isinstance(e.code, int) else 1
        return rc, sleeps, buf.getvalue()

    def test_missing_script_proceeds_silently(self) -> None:
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

    def test_reactive_missing_script_always_backs_off(self) -> None:
        sleeps: list[float] = []
        rc, out = quiet(
            pl.wait_for_quota,
            usage_script=self.tmp / "nope.sh",
            q5="85",
            q7="95",
            max_waits="1",
            claude_alias="claude",
            sleep_fn=sleeps.append,
            reactive=True,
        )
        self.assertEqual(rc, 0)
        self.assertEqual(sleeps, [pl.RATE_LIMIT_FALLBACK_SECONDS])
        self.assertIn("sleeping 3600s after rate limit", out)

    def test_fetch_fail_warns_and_proceeds(self) -> None:
        rc, _, out = self.gate(exit_code=3)
        self.assertEqual(rc, 0)
        self.assertIn("usage fetch failed", out)

    def test_reactive_fetch_failure_backs_off(self) -> None:
        script = self.tmp / "usage.sh"
        script.write_text("#!/usr/bin/env bash\nexit 3\n")
        script.chmod(0o755)
        sleeps: list[float] = []
        rc, out = quiet(
            pl.wait_for_quota,
            usage_script=script,
            q5="85",
            q7="95",
            max_waits="1",
            claude_alias="claude",
            sleep_fn=sleeps.append,
            reactive=True,
        )
        self.assertEqual(rc, 0)
        self.assertEqual(sleeps, [pl.RATE_LIMIT_FALLBACK_SECONDS])
        self.assertIn("usage fetch failed", out)

    def test_parse_fail_warns_and_proceeds(self) -> None:
        rc, _, out = self.gate("not json")
        self.assertEqual(rc, 0)
        self.assertIn("usage parse failed", out)

    def test_reactive_parse_failure_backs_off(self) -> None:
        script = self.tmp / "usage.sh"
        script.write_text("#!/usr/bin/env bash\nprintf 'not json'\n")
        script.chmod(0o755)
        sleeps: list[float] = []
        rc, out = quiet(
            pl.wait_for_quota,
            usage_script=script,
            q5="85",
            q7="95",
            max_waits="1",
            claude_alias="claude",
            sleep_fn=sleeps.append,
            reactive=True,
        )
        self.assertEqual(rc, 0)
        self.assertEqual(sleeps, [pl.RATE_LIMIT_FALLBACK_SECONDS])
        self.assertIn("usage parse failed", out)

    def test_under_proceeds(self) -> None:
        rc, sleeps, _ = self.gate(usage(50, 50))
        self.assertEqual((rc, sleeps), (0, []))

    def test_reactive_under_threshold_performs_real_backoff(self) -> None:
        script = self.tmp / "usage.sh"
        script.write_text(f"#!/usr/bin/env bash\nprintf '%s\\n' '{usage(50, 50)}'\n")
        script.chmod(0o755)
        started = time.monotonic()
        rc, out = quiet(
            pl.wait_for_quota,
            usage_script=script,
            q5="85",
            q7="95",
            max_waits="1",
            claude_alias="claude",
            reactive=True,
            fallback_seconds=0.03,
        )
        elapsed = time.monotonic() - started
        self.assertEqual(rc, 0)
        self.assertGreaterEqual(elapsed, 0.025)
        self.assertIn("below the configured thresholds", out)

    def test_nonutf8_output_is_a_parse_failure(self) -> None:
        # bash: undecodable bytes broke the `python3 -c` heredoc → WARN + proceed;
        # the gate must never abort the run on garbage usage output
        rc, _, out = self.gate(script_body=b"#!/usr/bin/env bash\nprintf '\\xff\\xfe{bad}'\n")
        self.assertEqual(rc, 0)
        self.assertIn("usage parse failed", out)

    def test_over_aborts_after_max_waits(self) -> None:
        rc, _, out = self.gate(usage(86, 50))
        self.assertEqual(rc, 1)
        self.assertIn("quota still over limit", out)

    def test_over_sleep_derived_from_resets_at(self) -> None:
        future = time.strftime("%Y-%m-%dT%H:%M:%S+00:00", time.gmtime(time.time() + 1000))
        rc, sleeps, _ = self.gate(usage(86, 50, r5=future))
        self.assertEqual(rc, 1)
        self.assertEqual(len(sleeps), 1)
        self.assertTrue(1000 - 60 + 120 <= sleeps[0] <= 1000 + 120 + 5)

    def test_no_resets_at_sleeps_600(self) -> None:
        rc, sleeps, _ = self.gate(usage(86, 50, r5=None))
        self.assertEqual(rc, 1)
        self.assertEqual(sleeps, [600])

    def test_past_resets_at_clamps_to_60(self) -> None:
        rc, sleeps, _ = self.gate(usage(86, 50, r5="2000-01-01T00:00:00+00:00"))
        self.assertEqual(rc, 1)
        self.assertEqual(sleeps, [60])

    def test_recovers_when_usage_drops(self) -> None:
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
        sleeps: list[float] = []
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
def make_pipeline(targets: list[str], **attrs: Any) -> pl.Pipeline:
    p = pl.Pipeline()
    p.targets = list(targets)
    for k, v in attrs.items():
        setattr(p, k, v)
    return p


class TestParsing(TmpCwd):
    def test_extract_names_trims_and_splits_pipe(self) -> None:
        p = make_pipeline(["  braft |brpc/braft|C++|Raft", "cometbft"])
        self.assertEqual(p.extract_names(), ["braft", "cometbft"])

    def test_extract_names_keeps_internal_whitespace(self) -> None:
        # wart fix (step 7): bash re-split names on whitespace (echo+read -ra),
        # turning one spaced name into phantom targets; the name stays whole now
        p = make_pipeline(["two words|x|y|z"])
        self.assertEqual(p.extract_names(), ["two words"])

    def test_extract_names_drops_whitespace_only_name(self) -> None:
        # the bash word-split contributed nothing for an all-blank name; kept
        p = make_pipeline(["   |x|y|z", "real|x|y|z"])
        self.assertEqual(p.extract_names(), ["real"])

    def test_garbage_quota_env_rejected_at_parse(self) -> None:
        # wart fix (step 7): the bash let a garbage threshold read as "usage
        # parse failed" and silently disabled the quota gate; a garbage
        # QUOTA_MAX_WAITS crashed mid-run. Both fail fast at parse time now.
        for var, val in (("QUOTA_5H", "high"), ("QUOTA_7D", "9%"), ("QUOTA_MAX_WAITS", "1.5")):
            with self.subTest(var=var):
                os.environ[var] = val
                self.addCleanup(os.environ.pop, var, None)
                err = io.StringIO()
                with contextlib.redirect_stderr(err):
                    rc = pl.Pipeline().parse_args(["t|g|l|r"])
                self.assertEqual(rc, 1)
                self.assertIn(f"{var} must be numeric, got '{val}'", err.getvalue())
                os.environ.pop(var, None)

    def test_nonfinite_quota_threshold_rejected_at_parse(self) -> None:
        # inf/nan pass float() but make the gate's `usage > limit` always False,
        # silently disabling it — the very failure the numeric check exists to
        # prevent, so a non-finite threshold fails fast too
        for var, val in (("QUOTA_5H", "inf"), ("QUOTA_5H", "nan"), ("QUOTA_7D", "Infinity")):
            with self.subTest(var=var, val=val):
                os.environ[var] = val
                self.addCleanup(os.environ.pop, var, None)
                err = io.StringIO()
                with contextlib.redirect_stderr(err):
                    rc = pl.Pipeline().parse_args(["t|g|l|r"])
                self.assertEqual(rc, 1)
                self.assertIn(f"{var} must be a finite number, got '{val}'", err.getvalue())
                os.environ.pop(var, None)

    def test_extract_names_stops_at_first_line(self) -> None:
        # bash `IFS='|' read -r name ...` consumes only the first line, so a
        # newline in the target terminates the name before the '|' split —
        # no phantom second name from a stray newline (e.g. $(cat targets.txt))
        p = make_pipeline(["foo\nbar|repo|Go|ref"])
        self.assertEqual(p.extract_names(), ["foo"])

    def test_parse_args_skips_and_values(self) -> None:
        p = pl.Pipeline()
        rc = p.parse_args(
            [
                "--skip-analysis",
                "--skip-repair-loop",
                "--max-repair-rounds=2",
                "--max-parallel=4",
                "--model=gpt-5.5",
                "--effort=high",
                "t|g|l|r",
            ]
        )
        self.assertIsNone(rc)
        self.assertTrue(p.skip_analysis)
        self.assertTrue(p.skip_repair_loop)
        self.assertEqual(p.max_repair_rounds, "2")
        self.assertEqual(p.max_parallel, "4")
        self.assertEqual(p.model, "gpt-5.5")
        self.assertEqual(p.effort, "high")
        self.assertEqual(p.targets, ["t|g|l|r"])

    def test_max_parallel_omitted_preserves_phase_defaults(self) -> None:
        p = pl.Pipeline()
        self.assertIsNone(p.parse_args(["t|g|l|r"]))
        self.assertIsNone(p.max_parallel)
        self.assertFalse(any(a.startswith("--max-parallel=") for a in p._phase_args(["t"])))

    def test_explicit_max_parallel_one_is_forwarded(self) -> None:
        p = pl.Pipeline()
        self.assertIsNone(p.parse_args(["--max-parallel=1", "t|g|l|r"]))
        self.assertEqual(p.max_parallel, "1")
        self.assertIn("--max-parallel=1", p._phase_args(["t"]))

    def test_model_effort_absent_and_explicit_empty_are_distinct(self) -> None:
        absent = pl.Pipeline()
        self.assertIsNone(absent.parse_args(["t"]))
        self.assertIsNone(absent.model)
        self.assertIsNone(absent.effort)
        absent_args = absent._phase_args(["t"])
        self.assertFalse(any(a.startswith("--model=") for a in absent_args))
        self.assertFalse(any(a.startswith("--effort=") for a in absent_args))

        empty = pl.Pipeline()
        self.assertIsNone(empty.parse_args(["--model=", "--effort=", "t"]))
        self.assertEqual(empty.model, "")
        self.assertEqual(empty.effort, "")
        empty_args = empty._phase_args(["t"])
        self.assertIn("--model=", empty_args)
        self.assertIn("--effort=", empty_args)

    def test_parse_args_unknown_option(self) -> None:
        p = pl.Pipeline()
        rc, out = quiet(p.parse_args, ["--bogus"])
        self.assertEqual(rc, 1)
        self.assertIn("Unknown option: --bogus", out)

    def test_parse_args_help(self) -> None:
        p = pl.Pipeline()
        rc, out = quiet(p.parse_args, ["--help"])
        self.assertEqual(rc, 0)
        self.assertIn("Full Specula pipeline", out)
        self.assertIn("--model=NAME", out)
        self.assertIn("--effort=LEVEL", out)

    def test_default_target_is_cwd_basename(self) -> None:
        p = pl.Pipeline()
        self.assertIsNone(p.parse_args([]))
        self.assertEqual(p.targets, [self.tmp.name])

    def test_max_turns_verbatim(self) -> None:
        p = pl.Pipeline()
        p.parse_args(["--max-turns=abc", "t"])
        self.assertEqual(p.max_turns, "abc")

    def test_get_work_dir_single_vs_batch(self) -> None:
        single = make_pipeline(["a|x|y|z"])
        self.assertEqual(single.get_work_dir("a"), f"{self.tmp}/.specula-output")
        batch = make_pipeline(["a|x|y|z", "b|x|y|z"])
        self.assertEqual(batch.get_work_dir("a"), f"{self.tmp}/a/.specula-output")


class TestRunReview(TmpCwd):
    """run_review must emit `<phase>` as the FIRST positional. launch_review.sh /
    ReviewPhase.run read the phase from argv[0] and treat every other non-flag
    arg as a target, so the phase has to lead. The pre-migration bash put the
    flags first, which made a real (non-dry-run) --enable-reviews run parse phase
    as "--agent=..." and abort with "Unknown phase"; --dry-run only logs the
    command, so the sequencing golden never caught it. Pin the arg order here."""

    def _capture(self, phase: str, *, model: str | None = None, effort: str | None = None) -> list[str]:
        p = make_pipeline(
            ["footest|foo/bar|Go|ref"],
            skip_reviews=False,
            model=model,
            effort=effort,
        )
        seen: list[list[str]] = []
        p._phase = lambda banner, script, args: seen.append(args)  # type: ignore[method-assign]
        p.run_review(phase, ["footest"])
        self.assertEqual(len(seen), 1)
        return seen[0]

    def test_phase_arg_leads(self) -> None:
        # argv[0] is exactly what ReviewPhase.run reads as the phase
        args = self._capture("analysis")
        self.assertEqual(args[0], "analysis")
        self.assertFalse(args[0].startswith("--"))

    def test_flags_and_names_preserved(self) -> None:
        args = self._capture("specgen")
        self.assertIn("--agent=claude-code", args)
        self.assertIn("--claude-alias=claude", args)
        self.assertEqual(args[-1], "footest")

    def test_model_effort_values_and_empty_are_forwarded(self) -> None:
        args = self._capture("analysis", model="gpt-5.5", effort="high")
        self.assertIn("--model=gpt-5.5", args)
        self.assertIn("--effort=high", args)
        self.assertEqual(args[0], "analysis")
        self.assertEqual(args[-1], "footest")

        args = self._capture("analysis", model="", effort="")
        self.assertIn("--model=", args)
        self.assertIn("--effort=", args)
        self.assertEqual(args[0], "analysis")
        self.assertEqual(args[-1], "footest")


class RRDirCase(TmpCwd):
    """Base with a seeded single-target repair dir."""

    def setUp(self) -> None:
        super().setUp()
        self.p = make_pipeline(["footest|g|l|r"])
        self.rr_dir = self.tmp / ".specula-output" / "spec" / "repair-requests"
        self.rr_dir.mkdir(parents=True)


class TestRepairPredicates(RRDirCase):
    def test_no_dir_no_requests(self) -> None:
        p = make_pipeline(["other|g|l|r"])
        self.assertFalse(p.has_any_request())
        self.assertFalse(p.repair_work_remaining())
        self.assertEqual(p.repair_state_sig(), "")

    def test_terminal_statuses(self) -> None:
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

    def test_mixed_terminal_and_open(self) -> None:
        make_rr(self.rr_dir, "RR-1", "RESOLVED")
        make_rr(self.rr_dir, "RR-2", "OPEN")
        self.assertTrue(self.p.repair_work_remaining())

    def test_sig_tracks_status_and_round(self) -> None:
        f = make_rr(self.rr_dir, "RR-1", "OPEN", round_=1)
        make_rr(self.rr_dir, "RR-2", "RECHECK", round_=2)
        sig = self.p.repair_state_sig()
        self.assertEqual(sig, "RR-1.md:OPEN:1\nRR-2.md:RECHECK:2")
        pl.rr_set_status(f, "RECHECK", "n")
        self.assertNotEqual(self.p.repair_state_sig(), sig)

    def test_reset_stale_only_touches_in_repair(self) -> None:
        stale = make_rr(self.rr_dir, "RR-1", "IN_REPAIR")
        untouched = make_rr(self.rr_dir, "RR-2", "RECHECK")
        _, out = quiet(self.p.reset_stale_in_repair)
        self.assertEqual(pl.rr_status(stale), "OPEN")
        self.assertEqual(pl.rr_status(untouched), "RECHECK")
        self.assertIn("reset RR-1.md IN_REPAIR -> OPEN (crash recovery)", out)
        self.assertIn("- reset (orchestrator): repair phase did not complete; retrying", stale.read_text())

    def test_reset_stale_noop_in_dry_run(self) -> None:
        stale = make_rr(self.rr_dir, "RR-1", "IN_REPAIR")
        self.p.dry_run = True
        _, out = quiet(self.p.reset_stale_in_repair)
        self.assertEqual(pl.rr_status(stale), "IN_REPAIR")
        self.assertEqual(out, "")


class TestLedger(RRDirCase):
    def test_ledger_rows_and_pipe_escape(self) -> None:
        make_rr(self.rr_dir, "RR-1", "OPEN", bug_id="DA-1 | pipes", round_=1)
        make_rr(self.rr_dir, "RR-2", "RESOLVED", bug_id="DA-2", round_=3)
        self.p.regenerate_ledger()
        text = (self.tmp / ".specula-output" / "spec" / "repair-ledger.md").read_text()
        self.assertIn("# Repair Ledger — footest", text)
        self.assertIn("| RR-1 | DA-1 \\| pipes | base.tla | OPEN | 1 |", text)
        self.assertIn("| RR-2 | DA-2 | base.tla | RESOLVED | 3 |", text)

    def test_no_requests_no_ledger(self) -> None:
        self.p.regenerate_ledger()
        self.assertFalse((self.tmp / ".specula-output" / "spec" / "repair-ledger.md").exists())

    def test_dry_run_noop(self) -> None:
        make_rr(self.rr_dir, "RR-1", "OPEN")
        self.p.dry_run = True
        self.p.regenerate_ledger()
        self.assertFalse((self.tmp / ".specula-output" / "spec" / "repair-ledger.md").exists())

    def test_status_file_count_exact_token(self) -> None:
        # wart fix (step 7): the bash grep matched RESOLVED as a PREFIX, so a
        # botched RESOLVEDX counted as resolved; the count is exact now
        f1 = make_rr(self.rr_dir, "RR-1", "RESOLVEDX")
        f2 = make_rr(self.rr_dir, "RR-2", "RESOLVED")
        f3 = make_rr(self.rr_dir, "RR-3", "OPEN")
        self.assertEqual(pl.Pipeline._status_file_count([f1, f2, f3], "RESOLVED"), 1)

    def test_status_file_count_uses_state_machine_window(self) -> None:
        # wart fix (step 7): the bash summary grep scanned the whole file while
        # rr_status reads only the 25-line frontmatter window — the same RR
        # could count as resolved in the summary yet stay OPEN to the repair
        # loop; both reads now share rr_status
        pad = "".join(f"k{i}: v\n" for i in range(30))
        f = self.rr_dir / "RR-1.md"
        f.write_text(pad + "status: DEFERRED\n")
        self.assertEqual(pl.Pipeline._status_file_count([f], "DEFERRED"), 0)


class TestRepairLoop(RRDirCase):
    """run_repair_loop orchestration: round counting + the no-progress spin guard,
    with the phase bodies stubbed. Replaces the pipeline_repair_* goldens."""

    def drive(self, on_repair: Callable[[int], None]) -> tuple[list[int], str]:
        """Run the loop with the phase bodies + quota wait stubbed; return the
        rounds run_phase3_repair saw and the captured log."""
        rounds: list[int] = []

        def repair(round_: int) -> None:
            rounds.append(round_)
            on_repair(round_)

        self.p.run_phase3_repair = repair  # type: ignore[method-assign]
        self.p.run_phase4_recheck = lambda round_: None  # type: ignore[method-assign]

        def no_quota_wait(*, reactive: bool = False) -> None:
            pass

        self.p.wait_for_quota = no_quota_wait  # type: ignore[method-assign]
        _, out = quiet(self.p.run_repair_loop)
        return rounds, out

    def resolve(self, rr_id: str = "RR-1") -> Callable[[int], None]:
        return lambda r: pl.rr_set_status(self.rr_dir / f"{rr_id}.md", "RESOLVED", "done")

    def test_no_requests_is_noop(self) -> None:
        rounds, out = self.drive(lambda r: None)
        self.assertEqual(rounds, [])
        self.assertIn("repair loop is a no-op", out)

    def test_resolves_then_stops(self) -> None:
        make_rr(self.rr_dir, "RR-1", "OPEN")
        rounds, out = self.drive(self.resolve())
        self.assertEqual(rounds, [1])
        self.assertIn("ended after 1 round", out)

    def test_no_progress_guard_breaks_spin(self) -> None:
        make_rr(self.rr_dir, "RR-1", "OPEN")
        rounds, out = self.drive(lambda r: None)  # status never changes -> stop after 1
        self.assertEqual(rounds, [1])
        self.assertIn("made no progress in round 1", out)

    def test_stale_in_repair_recovered_before_loop(self) -> None:
        make_rr(self.rr_dir, "RR-1", "IN_REPAIR")  # crashed prior run -> reset to OPEN
        self.drive(self.resolve())
        self.assertEqual(pl.rr_status(self.rr_dir / "RR-1.md"), "RESOLVED")


# ──────────────────────────────────────────────────────────
# Exit-code and error-path parity (bash set -e / set -u / pipefail)
# ──────────────────────────────────────────────────────────
class TestRunLauncherExitCodes(TmpCwd):
    def _pipeline(self, body: str) -> pl.Pipeline:
        (self.tmp / "fake.sh").write_text(body)
        p = make_pipeline(["t|g|l|r"])
        self.addCleanup(setattr, pl, "LAUNCH_DIR", pl.LAUNCH_DIR)
        pl.LAUNCH_DIR = self.tmp
        return p

    def _launch(self, body: str) -> int | str | None:
        p = self._pipeline(body)
        with self.assertRaises(SystemExit) as ctx:
            p._run_launcher("fake.sh", [])
        return ctx.exception.code

    def test_signal_death_maps_to_128_plus_n(self) -> None:
        # bash set -e reported a SIGTERM'd launcher as 143, not the mod-256
        # wraparound 241 — schedulers classify kills by 128+N
        self.assertEqual(self._launch("kill -TERM $$\n"), 143)

    def test_plain_failure_passes_through(self) -> None:
        self.assertEqual(self._launch("exit 7\n"), 7)

    def test_rate_limit_is_not_retried_at_whole_phase_scope(self) -> None:
        runs = self.tmp / "runs"
        p = self._pipeline(f'printf x >> "{runs}"\nexit 75\n')
        with self.assertRaises(SystemExit) as ctx:
            p._run_launcher("fake.sh", [])
        self.assertEqual(ctx.exception.code, pl.RATE_LIMIT_RC)
        self.assertEqual(runs.read_text(), "x")

    def test_phase_receives_rate_limit_contract(self) -> None:
        captured = self.tmp / "env"
        p = self._pipeline(
            f'printf \'%s\\n\' "$SPECULA_RATE_LIMIT_REACTIVE" "$SPECULA_RATE_LIMIT_RETRIES" '
            f'"$SPECULA_QUOTA_5H" "$SPECULA_QUOTA_7D" "$SPECULA_QUOTA_MAX_WAITS" '
            f'"$SPECULA_CLAUDE_ALIAS" > "{captured}"\n'
        )
        p.quota_5h = "81"
        p.quota_7d = "91"
        p.quota_max_waits = "4"
        p.claude_alias = "work"
        p._run_launcher("fake.sh", [])
        self.assertEqual(captured.read_text().splitlines(), ["1", "2", "81", "91", "4", "work"])

    def test_sigterm_is_forwarded_to_active_phase(self) -> None:
        forwarded = self.tmp / "forwarded"
        p = self._pipeline(f"trap 'touch \"{forwarded}\"; exit 0' TERM\nwhile :; do sleep 0.05; done\n")
        stop = threading.Event()

        def terminate() -> None:
            if not stop.wait(0.1):
                os.kill(os.getpid(), signal.SIGTERM)

        previous = signal.getsignal(signal.SIGTERM)
        sender = threading.Thread(target=terminate)
        sender.start()
        try:
            with self.assertRaises(SystemExit) as ctx:
                p._run_launcher("fake.sh", [])
        finally:
            stop.set()
            sender.join()
        self.assertEqual(ctx.exception.code, 128 + signal.SIGTERM)
        self.assertTrue(forwarded.is_file())
        self.assertIs(signal.getsignal(signal.SIGTERM), previous)

    def test_sigterm_escalates_when_phase_ignores_it(self) -> None:
        pid_file = self.tmp / "pid"
        p = self._pipeline(f"printf '%s\\n' $$ > \"{pid_file}\"\ntrap '' TERM\nwhile :; do sleep 1; done\n")
        old_grace = pl.PHASE_TERMINATION_GRACE_SECONDS
        pl.PHASE_TERMINATION_GRACE_SECONDS = 0.1
        self.addCleanup(setattr, pl, "PHASE_TERMINATION_GRACE_SECONDS", old_grace)
        stop = threading.Event()

        def terminate() -> None:
            if not stop.wait(0.1):
                os.kill(os.getpid(), signal.SIGTERM)

        sender = threading.Thread(target=terminate)
        sender.start()
        started = time.monotonic()
        try:
            with self.assertRaises(SystemExit) as ctx:
                p._run_launcher("fake.sh", [])
        finally:
            stop.set()
            sender.join()
        self.assertEqual(ctx.exception.code, 128 + signal.SIGTERM)
        self.assertLess(time.monotonic() - started, 1.0)
        phase_pid = int(pid_file.read_text())
        with self.assertRaises(ProcessLookupError):
            os.kill(phase_pid, 0)


class TestSingleTargetGuards(TmpCwd):
    def test_empty_name_aborts_before_phases(self) -> None:
        # bash died at `names[0]: unbound variable` (set -u) before any phase;
        # the port must fail fast too, not run the pipeline with zero names
        p = make_pipeline(["|org/repo|Go|ref"])
        buf = io.StringIO()
        with self.assertRaises(SystemExit) as ctx, contextlib.redirect_stdout(buf):
            p.main()
        self.assertEqual(ctx.exception.code, 1)
        self.assertIn("ERROR: no target name parsed", buf.getvalue())
        self.assertNotIn("PHASE 1", buf.getvalue())

    def test_absolute_name_does_not_escape_case_studies(self) -> None:
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
    def setUp(self) -> None:
        super().setUp()
        old_pwd = os.environ.get("PWD")

        def restore() -> None:
            if old_pwd is None:
                os.environ.pop("PWD", None)
            else:
                os.environ["PWD"] = old_pwd

        self.addCleanup(restore)

    def test_symlink_component_preserved(self) -> None:
        # bash $PWD keeps the path you cd'd through; getcwd resolves symlinks
        real = self.tmp / "mysys"
        real.mkdir()
        link = self.tmp / "work"
        link.symlink_to(real)
        os.chdir(link)
        os.environ["PWD"] = str(link)
        self.assertEqual(_logical_cwd(), link)
        p = pl.Pipeline()
        self.assertIsNone(p.parse_args([]))
        self.assertEqual(p.targets, ["work"])  # bash `basename "$PWD"`

    def test_stale_pwd_falls_back_to_getcwd(self) -> None:
        os.environ["PWD"] = "/definitely/not/here"
        self.assertEqual(_logical_cwd(), Path.cwd())


class TestMainTeeTeardown(TmpCwd):
    """End-to-end pins for the `main 2>&1 | tee` teardown, driven as a
    subprocess because the entry dup2s the real fds 1/2."""

    def _run_entry(self, patch: str) -> subprocess.CompletedProcess[str]:
        d = self.tmp / "driver.py"
        d.write_text(
            "import sys\n"
            f"sys.path.insert(0, {str(SRC)!r})\n"
            "from specula import pipelinelib as pl\n"
            f"{patch}\n"
            "sys.exit(pl.main(['--no-isolate', 't|g|l|r']))\n"  # legacy: keep runs/ out of the real repo
        )
        return subprocess.run([sys.executable, str(d)], cwd=self.tmp, capture_output=True, text=True)

    def test_unexpected_exception_traceback_reaches_log(self) -> None:
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

    def test_failing_tee_fails_the_pipeline(self) -> None:
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

    def test_failing_tee_wins_over_failing_main(self) -> None:
        # bash pipefail returns the rightmost non-zero status: when main fails
        # (rc=2) AND tee fails, the pipeline exits with tee's code (1), not 2
        out = self.tmp / ".specula-output"
        out.mkdir()
        logf = out / "pipeline.log"
        logf.write_text("")
        logf.chmod(0o444)
        self.addCleanup(logf.chmod, 0o644)
        r = self._run_entry("pl.Pipeline.main = lambda self: 2")
        self.assertEqual(r.returncode, 1)


if __name__ == "__main__":
    unittest.main()
