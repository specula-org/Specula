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
import json
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
from unittest import mock

SRC = Path(__file__).resolve().parents[2] / "src"

from specula import pipelinelib as pl
from specula.phaselib import Workspace, _logical_cwd

RR_TEMPLATE = """\
---
id: {rr_id}
bug_id: {bug_id}
target: SPEC_REPAIR
status: {status}
round: {round}
counterexample: output/{rr_id}.out
scope:
  actions: [RepairAction]
  invariants: []
  hunt_cfgs: [MC_repair.cfg]
  fault_actions: []
---

# Repair Request {rr_id}

body

## Trigger
The counterexample requires an impossible transition.

## Evidence
The real guard is enforced at src/base.tla:1.

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
        f = self._write("status: OPEN\nstatus: CONSUMED\n")
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
        pl.rr_set_status(f, "CONSUMED", "done")
        self.assertEqual(f.read_text(), "status: CONSUMED\nlast line\n- done\n")

    def test_rewrites_only_first_status(self) -> None:
        f = self.tmp / "RR-1.md"
        f.write_text("status: OPEN\nstatus: CONSUMED\n")
        pl.rr_set_status(f, "IN_REPAIR", "n")
        self.assertEqual(f.read_text(), "status: IN_REPAIR\nstatus: CONSUMED\n- n\n")

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
    def test_keep_original_is_opt_in_and_requires_isolation(self) -> None:
        default = pl.Pipeline()
        self.assertIsNone(default.parse_args(["t|g|l|r"]))
        self.assertFalse(default.keep_original)

        private = pl.Pipeline()
        self.assertIsNone(private.parse_args(["--keep-original", "t|g|l|r"]))
        self.assertTrue(private.keep_original)

        for argv in (
            ["--keep-original", "--no-isolate", "t|g|l|r"],
            ["--no-isolate", "--keep-original", "t|g|l|r"],
        ):
            with self.subTest(argv=argv), contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(pl.Pipeline().parse_args(argv), 1)

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
                "--tlc-memory-limit=96G",
                "--tlc-worker-limit=24",
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
        self.assertEqual(p.tlc_memory_limit, "96G")
        self.assertEqual(p.tlc_worker_limit, "24")
        self.assertEqual(p.targets, ["t|g|l|r"])

    def test_invalid_tlc_resource_limits_are_rejected_at_parse(self) -> None:
        for flag in (
            "--tlc-memory-limit=lots",
            "--tlc-memory-limit=0G",
            "--tlc-worker-limit=auto",
            "--tlc-worker-limit=0",
        ):
            with self.subTest(flag=flag):
                err = io.StringIO()
                with contextlib.redirect_stderr(err):
                    rc = pl.Pipeline().parse_args([flag, "t|g|l|r"])
                self.assertEqual(rc, 1)
                self.assertIn("ERROR:", err.getvalue())

    def test_tlc_resource_limit_environment_is_validated(self) -> None:
        os.environ["SPECULA_TLC_MEMORY_LIMIT"] = "bad"
        self.addCleanup(os.environ.pop, "SPECULA_TLC_MEMORY_LIMIT", None)
        err = io.StringIO()
        with contextlib.redirect_stderr(err):
            rc = pl.Pipeline().parse_args(["t|g|l|r"])
        self.assertEqual(rc, 1)
        self.assertIn("invalid memory size", err.getvalue())

    def test_legacy_confirmation_rejects_debate_in_either_order(self) -> None:
        for args in (
            ["--legacy-confirm", "--confirm-debate", "t|g|l|r"],
            ["--confirm-debate", "--legacy-confirm", "t|g|l|r"],
        ):
            with self.subTest(args=args):
                err = io.StringIO()
                with contextlib.redirect_stderr(err):
                    rc = pl.Pipeline().parse_args(args)
                self.assertEqual(rc, 1)
                self.assertIn("--legacy-confirm conflicts with --confirm-debate", err.getvalue())

    def test_artifact_omitted_preserves_auto_discovery(self) -> None:
        p = pl.Pipeline()
        self.assertIsNone(p.parse_args(["t|g|l|r"]))
        self.assertFalse(p._artifact_given)
        self.assertFalse(any(arg.startswith("--artifact=") for arg in p._phase_args(["t"])))

    def test_valid_artifact_directory_is_forwarded(self) -> None:
        repo = self.tmp / "repo"
        repo.mkdir()
        p = pl.Pipeline()

        self.assertIsNone(p.parse_args([f"--artifact={repo}", "t|g|l|r"]))

        self.assertTrue(p._artifact_given)
        self.assertEqual(p.artifact, str(repo))
        self.assertIn(f"--artifact={repo}", p._phase_args(["t"]))
        self.assertNotIn(f"--artifact={repo}", p._phase_args(["t"], with_artifact=False))

    def test_relative_artifact_is_stable_after_working_directory_changes(self) -> None:
        repo = self.tmp / "repo"
        repo.mkdir()
        p = pl.Pipeline()
        self.assertIsNone(p.parse_args(["--artifact=repo", "t|g|l|r"]))

        later_cwd = self.tmp / "case-studies" / "t"
        later_cwd.mkdir(parents=True)
        os.chdir(later_cwd)

        self.assertEqual(p.artifact, str(repo))
        self.assertEqual(p.argv, ["--artifact=repo", "t|g|l|r"])
        self.assertIn(f"--artifact={repo}", p._phase_args(["t"]))

    def test_home_relative_artifact_is_expanded_and_forwarded(self) -> None:
        home = self.tmp / "home"
        repo = home / "cass-operator"
        repo.mkdir(parents=True)
        p = pl.Pipeline()

        with mock.patch.dict(os.environ, {"HOME": str(home)}):
            self.assertIsNone(p.parse_args(["--artifact=~/cass-operator", "t|g|l|r"]))

        self.assertEqual(p.artifact, str(repo))
        self.assertEqual(p.argv, ["--artifact=~/cass-operator", "t|g|l|r"])
        self.assertIn(f"--artifact={repo}", p._phase_args(["t"]))

    def test_artifact_expansion_failure_uses_existing_error_contract(self) -> None:
        p = pl.Pipeline()
        err = io.StringIO()
        with (
            mock.patch.object(Path, "expanduser", side_effect=RuntimeError("home unavailable")),
            contextlib.redirect_stderr(err),
        ):
            rc = p.parse_args(["--artifact=~/repo", "t|g|l|r"])

        self.assertEqual(rc, 1)
        self.assertEqual(err.getvalue(), "ERROR: --artifact must be an existing directory: ~/repo\n")

    def test_invalid_artifact_path_is_rejected(self) -> None:
        file_path = self.tmp / "artifact.txt"
        file_path.write_text("not a directory\n")
        for value in ("", str(self.tmp / "missing"), str(file_path)):
            with self.subTest(value=value):
                p = pl.Pipeline()
                err = io.StringIO()
                with contextlib.redirect_stderr(err):
                    rc = p.parse_args([f"--artifact={value}", "t|g|l|r"])
                self.assertEqual(rc, 1)
                self.assertIn("--artifact must be an existing directory", err.getvalue())

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
        self.assertEqual(p._max_parallel_summary(), "1")

    def test_policy_retry_default_and_explicit_value_are_forwarded(self) -> None:
        default = pl.Pipeline()
        self.assertIsNone(default.parse_args(["t|g|l|r"]))
        self.assertEqual(default.policy_retries, 20)
        self.assertIn("--policy-retries=20", default._phase_args(["t"]))

        explicit = pl.Pipeline()
        self.assertIsNone(explicit.parse_args(["--policy-retries=100", "t|g|l|r"]))
        self.assertEqual(explicit.policy_retries, 100)
        self.assertIn("--policy-retries=100", explicit._phase_args(["t"]))

        disabled = pl.Pipeline()
        self.assertIsNone(disabled.parse_args(["--policy-retries=0", "t|g|l|r"]))
        self.assertEqual(disabled.policy_retries, 0)
        self.assertIn("--policy-retries=0", disabled._phase_args(["t"]))

    def test_invalid_policy_retry_budget_is_rejected_at_parse(self) -> None:
        for value in ("", "-1", "1.5", "bad", "+1"):
            with self.subTest(value=value):
                p = pl.Pipeline()
                err = io.StringIO()
                with contextlib.redirect_stderr(err):
                    rc = p.parse_args([f"--policy-retries={value}", "t|g|l|r"])
                self.assertEqual(rc, 1)
                self.assertIn("--policy-retries must be a non-negative integer", err.getvalue())

    def test_transient_resume_default_and_explicit_value_are_forwarded(self) -> None:
        default = pl.Pipeline()
        self.assertIsNone(default.parse_args(["t|g|l|r"]))
        self.assertEqual(default.transient_resumes, 20)
        self.assertIn("--transient-resumes=20", default._phase_args(["t"]))

        explicit = pl.Pipeline()
        self.assertIsNone(explicit.parse_args(["--transient-resumes=100", "t|g|l|r"]))
        self.assertEqual(explicit.transient_resumes, 100)
        self.assertIn("--transient-resumes=100", explicit._phase_args(["t"]))

        disabled = pl.Pipeline()
        self.assertIsNone(disabled.parse_args(["--transient-resumes=0", "t|g|l|r"]))
        self.assertEqual(disabled.transient_resumes, 0)
        self.assertIn("--transient-resumes=0", disabled._phase_args(["t"]))

    def test_invalid_transient_resume_budget_is_rejected_at_parse(self) -> None:
        for value in ("", "-1", "1.5", "bad", "+1"):
            with self.subTest(value=value):
                p = pl.Pipeline()
                err = io.StringIO()
                with contextlib.redirect_stderr(err):
                    rc = p.parse_args([f"--transient-resumes={value}", "t|g|l|r"])
                self.assertEqual(rc, 1)
                self.assertIn("--transient-resumes must be a non-negative integer", err.getvalue())

    def test_max_parallel_summary_reports_per_finding_default(self) -> None:
        p = pl.Pipeline()
        self.assertIsNone(p.parse_args(["t|g|l|r"]))
        self.assertEqual(
            p._max_parallel_summary(),
            "phase defaults (ordinary phases 1 at a time; per-finding confirmation 4 at a time)",
        )

    def test_max_parallel_summary_reports_legacy_confirmation_default(self) -> None:
        p = pl.Pipeline()
        self.assertIsNone(p.parse_args(["--legacy-confirm", "t|g|l|r"]))
        self.assertEqual(
            p._max_parallel_summary(),
            "phase defaults (ordinary phases 1 at a time; legacy confirmation 1 at a time)",
        )

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

    def test_invalid_repair_round_cap_rejected_at_parse(self) -> None:
        for value in ("", "bad", "1.5", "-1", "+1"):
            with self.subTest(value=value):
                p = pl.Pipeline()
                err = io.StringIO()
                with contextlib.redirect_stderr(err):
                    rc = p.parse_args([f"--max-repair-rounds={value}", "t|g|l|r"])
                self.assertEqual(rc, 1)
                self.assertIn("must be a non-negative integer", err.getvalue())

    def test_invalid_repair_round_cap_env_rejected_at_parse(self) -> None:
        os.environ["MAX_REPAIR_ROUNDS"] = "-2"
        self.addCleanup(os.environ.pop, "MAX_REPAIR_ROUNDS", None)
        err = io.StringIO()
        with contextlib.redirect_stderr(err):
            rc = pl.Pipeline().parse_args(["t|g|l|r"])
        self.assertEqual(rc, 1)
        self.assertIn("must be a non-negative integer", err.getvalue())

    def test_zero_repair_round_cap_is_valid_unlimited_value(self) -> None:
        p = pl.Pipeline()
        self.assertIsNone(p.parse_args(["--max-repair-rounds=0", "t|g|l|r"]))
        self.assertEqual(p.max_repair_rounds, "0")

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
        self.assertIn("--policy-retries=N", out)
        self.assertIn("--transient-resumes=N", out)
        self.assertIn("default: 20", out)

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


class TestPhaseParallelArgs(TmpCwd):
    def capture_main(self, p: pl.Pipeline) -> dict[str, list[str]]:
        calls: dict[str, list[str]] = {}
        p.skip_repair_loop = True
        p.validate_agent_adapter = lambda: None  # type: ignore[method-assign]
        p.wait_for_quota = lambda **kwargs: None  # type: ignore[method-assign]
        p.generate_summary = lambda: None  # type: ignore[method-assign]
        p._phase = lambda banner, script, args: calls.__setitem__(script, args)  # type: ignore[method-assign]
        quiet(p.main)
        return calls

    def test_full_pipeline_default_preserves_each_phase_default(self) -> None:
        p = pl.Pipeline()
        self.assertIsNone(p.parse_args(["--max-turns=9", "--model=gpt-5.5", "--effort=high", "a|g|l|r", "b|g|l|r"]))
        calls = self.capture_main(p)
        confirmation = calls["launch_bug_confirmation.sh"]
        self.assertFalse(any(arg.startswith("--max-parallel=") for arg in confirmation))
        self.assertIn("--max-turns=9", confirmation)
        self.assertIn("--model=gpt-5.5", confirmation)
        self.assertIn("--effort=high", confirmation)
        for script, args in calls.items():
            self.assertFalse(any(arg.startswith("--max-parallel=") for arg in args), script)

    def test_explicit_one_reaches_confirmation_and_stays_serial(self) -> None:
        p = pl.Pipeline()
        self.assertIsNone(p.parse_args(["--max-parallel=1", "a|g|l|r", "b|g|l|r"]))
        calls = self.capture_main(p)
        self.assertIn("--max-parallel=1", calls["launch_bug_confirmation.sh"])

    def test_explicit_nondefault_reaches_confirmation(self) -> None:
        p = pl.Pipeline()
        self.assertIsNone(p.parse_args(["--max-parallel=7", "a|g|l|r", "b|g|l|r"]))
        calls = self.capture_main(p)
        self.assertIn("--max-parallel=7", calls["launch_bug_confirmation.sh"])


class TestSourceSnapshots(TmpCwd):
    def setUp(self) -> None:
        super().setUp()
        for name in ("SPECULA_RUN_DIR", "SPECULA_SOURCE_SNAPSHOT", "SPECULA_SANDBOX_EXTRA_WRITE"):
            previous = os.environ.pop(name, None)

            def restore(key: str = name, value: str | None = previous) -> None:
                if value is None:
                    os.environ.pop(key, None)
                else:
                    os.environ[key] = value

            self.addCleanup(restore)

    def test_prepare_routes_phases_and_extends_sandbox_write_paths(self) -> None:
        original = self.tmp / "original"
        original.mkdir()
        (original / "source.txt").write_text("original\n")
        run = self.tmp / "run"
        run.mkdir()
        p = make_pipeline(["demo|g|l|r"], keep_original=True)
        p.run_dir = run
        p._snapshot_sources = {"demo": original}
        os.environ["SPECULA_RUN_DIR"] = str(run)
        os.environ["SPECULA_SANDBOX_EXTRA_WRITE"] = "/cache"

        p.prepare_source_snapshots(["demo"])

        source = run / "demo" / "source"
        self.assertEqual(Workspace(p.targets, artifact=str(original)).find_repo_dir("demo"), str(source))
        self.assertEqual(os.environ["SPECULA_SANDBOX_EXTRA_WRITE"].split(os.pathsep), ["/cache", str(source)])
        self.assertFalse(any(arg.startswith("--artifact=") for arg in p._phase_args(p.targets)))


class TestRunReview(TmpCwd):
    """run_review must emit `<phase>` as the FIRST positional. launch_review.sh /
    ReviewPhase.run read the phase from argv[0] and treat every other non-flag
    arg as a target, so the phase has to lead. The pre-migration bash put the
    flags first, which made a real (non-dry-run) --enable-reviews run parse phase
    as "--agent=..." and abort with "Unknown phase"; --dry-run only logs the
    command, so the sequencing golden never caught it. Pin the arg order here."""

    def _capture(
        self,
        phase: str,
        *,
        model: str | None = None,
        effort: str | None = None,
        policy_retries: int = 20,
        transient_resumes: int = 20,
    ) -> list[str]:
        p = make_pipeline(
            ["footest|foo/bar|Go|ref"],
            skip_reviews=False,
            model=model,
            effort=effort,
            policy_retries=policy_retries,
            transient_resumes=transient_resumes,
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
        self.assertIn("--policy-retries=20", args)
        self.assertIn("--transient-resumes=20", args)
        self.assertEqual(args[-1], "footest")

    def test_explicit_policy_retry_budget_reaches_review(self) -> None:
        args = self._capture("analysis", policy_retries=100)
        self.assertIn("--policy-retries=100", args)

    def test_explicit_transient_resume_budget_reaches_review(self) -> None:
        args = self._capture("analysis", transient_resumes=100)
        self.assertIn("--transient-resumes=100", args)

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
    def test_executable_accepts_dispatcher_lifecycle_only(self) -> None:
        text = "---\nid: RR-1\nstatus: OPEN\nround: 1\n---\n\nagent prose\n"
        self.assertTrue(self.p._repair_request_is_executable(text, "RR-1"))

    def test_executable_rejects_invalid_dispatcher_lifecycle(self) -> None:
        cases = {
            "wrong id": "---\nid: RR-2\nstatus: OPEN\nround: 1\n---\n",
            "invalid status": "---\nid: RR-1\nstatus: PENDING\nround: 1\n---\n",
            "non-digit round": "---\nid: RR-1\nstatus: OPEN\nround: one\n---\n",
        }
        for label, text in cases.items():
            with self.subTest(label):
                self.assertFalse(self.p._repair_request_is_executable(text, "RR-1"))

    def test_no_dir_no_requests(self) -> None:
        p = make_pipeline(["other|g|l|r"])
        self.assertFalse(p.has_any_request())
        self.assertFalse(p.has_open_repair_requests())
        self.assertEqual(p.repair_state_sig(), "")

    def test_terminal_statuses(self) -> None:
        # New state machine: OPEN | IN_REPAIR | CONSUMED. Only CONSUMED is terminal.
        for status, remaining in [
            ("OPEN", True),
            ("IN_REPAIR", True),
            ("CONSUMED", False),
        ]:
            for f in self.rr_dir.glob("RR-*.md"):
                f.unlink()
            make_rr(self.rr_dir, "RR-1", status)
            self.assertTrue(self.p.has_any_request())
            self.assertEqual(self.p.has_open_repair_requests(), remaining, status)

    def test_mixed_terminal_and_open(self) -> None:
        make_rr(self.rr_dir, "RR-1", "CONSUMED")
        make_rr(self.rr_dir, "RR-2", "OPEN")
        self.assertTrue(self.p.has_open_repair_requests())

    def test_sig_tracks_status_and_round(self) -> None:
        f = make_rr(self.rr_dir, "RR-1", "OPEN", round_=1)
        make_rr(self.rr_dir, "RR-2", "IN_REPAIR", round_=2)
        sig = self.p.repair_state_sig()
        self.assertEqual(sig, "RR-1.md:OPEN:1\nRR-2.md:IN_REPAIR:2")
        pl.rr_set_status(f, "CONSUMED", "n")
        self.assertNotEqual(self.p.repair_state_sig(), sig)

    def test_reset_stale_only_touches_in_repair(self) -> None:
        stale = make_rr(self.rr_dir, "RR-1", "IN_REPAIR")
        untouched = make_rr(self.rr_dir, "RR-2", "CONSUMED")
        _, out = quiet(self.p.reset_stale_in_repair)
        self.assertEqual(pl.rr_status(stale), "OPEN")
        self.assertEqual(pl.rr_status(untouched), "CONSUMED")
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
        make_rr(self.rr_dir, "RR-2", "CONSUMED", bug_id="DA-2", round_=3)
        self.p.regenerate_ledger()
        text = (self.tmp / ".specula-output" / "spec" / "repair-ledger.md").read_text()
        self.assertIn("# Repair Ledger — footest", text)
        self.assertIn("| RR-1 | DA-1 \\| pipes | SPEC_REPAIR | OPEN | 1 |", text)
        self.assertIn("| RR-2 | DA-2 | SPEC_REPAIR | CONSUMED | 3 |", text)

    def test_no_requests_no_ledger(self) -> None:
        self.p.regenerate_ledger()
        self.assertFalse((self.tmp / ".specula-output" / "spec" / "repair-ledger.md").exists())

    def test_deferred_requests_remain_in_ledger(self) -> None:
        deferred = self.rr_dir / "deferred"
        deferred.mkdir()
        make_rr(deferred, "RR-1", "OPEN", bug_id="legacy", round_=2)
        self.p.regenerate_ledger()
        text = (self.tmp / ".specula-output" / "spec" / "repair-ledger.md").read_text()
        self.assertIn("| RR-1 | legacy | SPEC_REPAIR | DEFERRED | 2 |", text)

    def test_empty_state_removes_stale_ledger(self) -> None:
        ledger = self.tmp / ".specula-output" / "spec" / "repair-ledger.md"
        ledger.write_text("stale\n")
        self.p.regenerate_ledger()
        self.assertFalse(ledger.exists())

    def test_dry_run_noop(self) -> None:
        make_rr(self.rr_dir, "RR-1", "OPEN")
        self.p.dry_run = True
        self.p.regenerate_ledger()
        self.assertFalse((self.tmp / ".specula-output" / "spec" / "repair-ledger.md").exists())

    def test_status_file_count_exact_token(self) -> None:
        # wart fix (step 7): the bash grep matched CONSUMED as a PREFIX, so a
        # botched CONSUMEDX counted as consumed; the count is exact now
        f1 = make_rr(self.rr_dir, "RR-1", "CONSUMEDX")
        f2 = make_rr(self.rr_dir, "RR-2", "CONSUMED")
        f3 = make_rr(self.rr_dir, "RR-3", "OPEN")
        self.assertEqual(pl.Pipeline._status_file_count([f1, f2, f3], "CONSUMED"), 1)

    def test_status_file_count_uses_state_machine_window(self) -> None:
        # wart fix (step 7): the bash summary grep scanned the whole file while
        # rr_status reads only the 25-line frontmatter window — the same RR
        # could count as consumed in the summary yet stay OPEN to the repair
        # loop; both reads now share rr_status
        pad = "".join(f"k{i}: v\n" for i in range(30))
        f = self.rr_dir / "RR-1.md"
        f.write_text(pad + "status: CONSUMED\n")
        self.assertEqual(pl.Pipeline._status_file_count([f], "CONSUMED"), 0)


class TestRepairLoop(RRDirCase):
    """run_repair_loop orchestration: round counting + the no-progress spin guard,
    with the phase bodies stubbed. Replaces the pipeline_repair_* goldens."""

    def configure(self, on_repair: Callable[[int], None]) -> list[int]:
        """Stub the phase bodies + quota wait and return observed rounds."""
        rounds: list[int] = []

        def repair(round_: int, names: list[str] | None = None) -> None:
            self.assertEqual(names, ["footest"])
            rounds.append(round_)
            on_repair(round_)

        self.p.run_phase3_repair = repair  # type: ignore[method-assign]
        self.p.run_phase4_confirmation = lambda: None  # type: ignore[method-assign]

        def no_quota_wait(*, reactive: bool = False) -> None:
            pass

        self.p.wait_for_quota = no_quota_wait  # type: ignore[method-assign]
        return rounds

    def drive(self, on_repair: Callable[[int], None]) -> tuple[list[int], str]:
        """Run the configured loop and return observed rounds and its log."""
        rounds = self.configure(on_repair)
        _, out = quiet(self.p.run_repair_loop)
        return rounds, out

    def resolve(self, rr_id: str = "RR-1") -> Callable[[int], None]:
        return lambda r: pl.rr_set_status(self.rr_dir / f"{rr_id}.md", "CONSUMED", "done")

    def test_no_requests_is_noop(self) -> None:
        rounds, out = self.drive(lambda r: None)
        self.assertEqual(rounds, [])
        self.assertIn("repair loop is a no-op", out)

    def test_resolves_then_stops(self) -> None:
        request = make_rr(self.rr_dir, "RR-1", "OPEN")

        def resolve_with_durable_snapshot(round_: int) -> None:
            marker = self.p.repair_phase3_snapshot_path("footest")
            self.assertTrue(marker.is_file())
            self.assertIn('"RR-1.md"', marker.read_text())
            pl.rr_set_status(request, "CONSUMED", "done")

        rounds, out = self.drive(resolve_with_durable_snapshot)
        self.assertEqual(rounds, [1])
        self.assertIn("resolved all requests after 1 round", out)
        self.assertFalse(self.p.repair_phase3_snapshot_path("footest").exists())

    def test_success_without_consuming_is_failure_and_keeps_request_open(self) -> None:
        make_rr(self.rr_dir, "RR-1", "OPEN")
        rounds = self.configure(lambda r: None)
        out = io.StringIO()
        with self.assertRaisesRegex(RuntimeError, "without consuming"), contextlib.redirect_stdout(out):
            self.p.run_repair_loop()
        self.assertEqual(rounds, [1])
        self.assertIn("only that target was reset OPEN", out.getvalue())
        self.assertEqual(pl.rr_status(self.rr_dir / "RR-1.md"), "OPEN")
        self.assertFalse((self.rr_dir / "deferred" / "RR-1.md").exists())

    def test_stale_in_repair_recovered_before_loop(self) -> None:
        make_rr(self.rr_dir, "RR-1", "IN_REPAIR")  # crashed prior run -> reset to OPEN
        self.drive(self.resolve())
        self.assertEqual(pl.rr_status(self.rr_dir / "RR-1.md"), "CONSUMED")

    def test_restart_restores_truncated_in_repair_from_durable_snapshot(self) -> None:
        request = make_rr(self.rr_dir, "RR-1", "OPEN")
        snapshot = self.p.snapshot_open_repair_requests("footest")
        self.p.persist_open_repair_snapshot("footest", snapshot, 2)
        request.write_text("---\nid: RR-1\nstatus: IN_REPAIR\n")

        restarted = make_pipeline(["footest|g|l|r"])
        _, out = quiet(restarted.prepare_repair_state)

        restored = request.read_text()
        self.assertEqual(pl.rr_status(request), "OPEN")
        self.assertIn("target: SPEC_REPAIR", restored)
        self.assertIn("## Evidence", restored)
        self.assertIn("partial spec/output changes were retained", restored)
        self.assertFalse(restarted.repair_phase3_snapshot_path("footest").exists())
        self.assertIn("recovered durable Phase 3 snapshot", out)

    def test_restart_after_durable_phase3_commit_keeps_consumed(self) -> None:
        request = make_rr(self.rr_dir, "RR-1", "OPEN")
        snapshot = self.p.snapshot_open_repair_requests("footest")
        self.p.persist_open_repair_snapshot("footest", snapshot, 2)
        snapshot_doc = json.loads(self.p.repair_phase3_snapshot_path("footest").read_text())

        # The launcher returned success: CONSUMED is complete, then the
        # generation marker commits this exact attempt. Simulate SIGKILL before
        # the obsolete durable snapshot can be unlinked.
        pl.rr_set_status(request, "CONSUMED", "repair completed")
        self.p.advance_confirmation_generation(2, ["footest"])
        generation = json.loads((self.rr_dir.parent / "confirmation-generation.json").read_text())
        self.assertEqual(generation["repair_phase3_commit"], snapshot_doc["commit_token"])

        restarted = make_pipeline(["footest|g|l|r"])
        recovered, out = quiet(restarted.prepare_repair_state)

        self.assertEqual(recovered, {"footest"})
        self.assertEqual(pl.rr_status(request), "CONSUMED")
        self.assertNotIn("retrying OPEN", request.read_text())
        self.assertFalse(restarted.repair_phase3_snapshot_path("footest").exists())
        self.assertIn("finalized committed repair Phase 3", out)

    def test_main_committed_recovery_goes_directly_to_fresh_phase4(self) -> None:
        request = make_rr(self.rr_dir, "RR-1", "OPEN")
        snapshot = self.p.snapshot_open_repair_requests("footest")
        self.p.persist_open_repair_snapshot("footest", snapshot, 2)
        pl.rr_set_status(request, "CONSUMED", "repair completed")
        self.p.advance_confirmation_generation(2, ["footest"])
        events: list[str] = []

        self.p.skip_analysis = True
        self.p.skip_specgen = True
        self.p.skip_harness = True
        self.p.skip_classification = True
        self.p.validate_agent_adapter = lambda: None  # type: ignore[method-assign]
        self.p.generate_summary = lambda: None  # type: ignore[method-assign]
        self.p.wait_for_quota = lambda **kwargs: None  # type: ignore[method-assign]
        self.p.run_phase3_validation = lambda: self.fail("committed repair was rerun as ordinary Phase 3")  # type: ignore[method-assign]
        self.p.run_phase3_repair = lambda *_args: self.fail("committed repair was reopened")  # type: ignore[method-assign]
        self.p.run_phase4_confirmation = lambda: events.append("fresh-phase4")  # type: ignore[method-assign]

        rc, out = quiet(self.p.main)

        self.assertEqual(rc, 0)
        self.assertEqual(events, ["fresh-phase4"])
        self.assertEqual(pl.rr_status(request), "CONSUMED")
        self.assertIn("Ordinary Phase 3 covered for every target by the recovered committed repairs", out)
        self.assertIn("repair loop is a no-op", out)

    def test_default_upstream_rerun_forces_fresh_ordinary_phase3_after_commit_recovery(self) -> None:
        request = make_rr(self.rr_dir, "RR-1", "OPEN")
        snapshot = self.p.snapshot_open_repair_requests("footest")
        self.p.persist_open_repair_snapshot("footest", snapshot, 2)
        pl.rr_set_status(request, "CONSUMED", "repair completed")
        self.p.advance_confirmation_generation(2, ["footest"])
        snapshot_path = self.p.repair_phase3_snapshot_path("footest")
        events: list[str] = []

        def phase1() -> None:
            # Recovery must precede the first default upstream mutation.
            self.assertFalse(snapshot_path.exists())
            self.assertEqual(pl.rr_status(request), "CONSUMED")
            events.append("phase1")

        self.p.validate_agent_adapter = lambda: None  # type: ignore[method-assign]
        self.p.generate_summary = lambda: None  # type: ignore[method-assign]
        self.p.wait_for_quota = lambda **kwargs: None  # type: ignore[method-assign]
        self.p.run_phase1_analysis = phase1  # type: ignore[method-assign]
        self.p.run_phase2_specgen = lambda: events.append("phase2")  # type: ignore[method-assign]
        self.p.run_phase2_5_harness = lambda: events.append("phase2.5")  # type: ignore[method-assign]
        self.p.run_phase3_validation = lambda: events.append("ordinary-phase3")  # type: ignore[method-assign]
        self.p.run_phase3_repair = lambda *_args: self.fail("committed RR was reopened as scoped repair")  # type: ignore[method-assign]
        self.p.run_phase4_confirmation = lambda: events.append("phase4")  # type: ignore[method-assign]
        self.p.run_phase4b_classification = lambda: events.append("phase4b")  # type: ignore[method-assign]

        rc, _out = quiet(self.p.main)

        self.assertEqual(rc, 0)
        self.assertEqual(events, ["phase1", "phase2", "phase2.5", "ordinary-phase3", "phase4", "phase4b"])
        self.assertEqual(pl.rr_status(request), "CONSUMED")

    def test_partial_multitarget_commit_never_covers_new_target_phase3(self) -> None:
        p = make_pipeline(["old|g|l|r", "new|g|l|r"])
        old_rr_dir = self.tmp / "old" / ".specula-output" / "spec" / "repair-requests"
        new_rr_dir = self.tmp / "new" / ".specula-output" / "spec" / "repair-requests"
        old_rr_dir.mkdir(parents=True)
        new_rr_dir.mkdir(parents=True)
        old_request = make_rr(old_rr_dir, "RR-1", "OPEN", bug_id="OLD-1")
        snapshot = p.snapshot_open_repair_requests("old")
        p.persist_open_repair_snapshot("old", snapshot, 3)
        pl.rr_set_status(old_request, "CONSUMED", "old target repair completed")
        p.advance_confirmation_generation(3, ["old"])
        events: list[str] = []

        p.skip_analysis = True
        p.skip_specgen = True
        p.skip_harness = True
        p.skip_classification = True
        p.validate_agent_adapter = lambda: None  # type: ignore[method-assign]
        p.generate_summary = lambda: None  # type: ignore[method-assign]
        p.wait_for_quota = lambda **kwargs: None  # type: ignore[method-assign]
        p.run_phase3_validation = lambda: events.append("all-target-ordinary-phase3")  # type: ignore[method-assign]
        p.run_phase3_repair = lambda *_args: self.fail("old committed target was reopened")  # type: ignore[method-assign]
        p.run_phase4_confirmation = lambda: events.append("phase4")  # type: ignore[method-assign]

        rc, out = quiet(p.main)

        self.assertEqual(rc, 0)
        self.assertEqual(events, ["all-target-ordinary-phase3", "phase4"])
        self.assertEqual(pl.rr_status(old_request), "CONSUMED")
        self.assertNotIn("covered for every target", out)

    def test_direct_repair_loop_consumes_committed_recovery_with_fresh_phase4(self) -> None:
        request = make_rr(self.rr_dir, "RR-1", "OPEN")
        snapshot = self.p.snapshot_open_repair_requests("footest")
        self.p.persist_open_repair_snapshot("footest", snapshot, 2)
        pl.rr_set_status(request, "CONSUMED", "repair completed")
        self.p.advance_confirmation_generation(2, ["footest"])
        events: list[str] = []
        self.p.wait_for_quota = lambda **kwargs: None  # type: ignore[method-assign]
        self.p.run_phase3_repair = lambda *_args: self.fail("committed repair was reopened")  # type: ignore[method-assign]
        self.p.run_phase4_confirmation = lambda: events.append("fresh-phase4")  # type: ignore[method-assign]

        covered, out = quiet(self.p.run_repair_loop)

        self.assertEqual(covered, {"footest"})
        self.assertEqual(events, ["fresh-phase4"])
        self.assertEqual(pl.rr_status(request), "CONSUMED")
        self.assertFalse(self.p.repair_phase3_snapshot_path("footest").exists())
        self.assertIn("completed its pending fresh Phase 4", out)

    def test_direct_committed_recovery_repairs_requests_opened_by_fresh_phase4(self) -> None:
        request = make_rr(self.rr_dir, "RR-1", "OPEN")
        snapshot = self.p.snapshot_open_repair_requests("footest")
        self.p.persist_open_repair_snapshot("footest", snapshot, 2)
        pl.rr_set_status(request, "CONSUMED", "repair completed")
        self.p.advance_confirmation_generation(2, ["footest"])
        confirmations: list[int] = []
        repairs: list[int] = []

        def confirm() -> None:
            confirmations.append(len(confirmations) + 1)
            if len(confirmations) == 1:
                make_rr(self.rr_dir, "RR-2", "OPEN", bug_id="B-2")

        def repair(round_: int, names: list[str] | None = None) -> None:
            self.assertEqual(names, ["footest"])
            repairs.append(round_)
            pl.rr_set_status(self.rr_dir / "RR-2.md", "CONSUMED", "follow-up repaired")

        self.p.wait_for_quota = lambda **kwargs: None  # type: ignore[method-assign]
        self.p.run_phase3_repair = repair  # type: ignore[method-assign]
        self.p.run_phase4_confirmation = confirm  # type: ignore[method-assign]

        covered, out = quiet(self.p.run_repair_loop)

        self.assertEqual(covered, {"footest"})
        self.assertEqual(confirmations, [1, 2])
        self.assertEqual(repairs, [1])
        self.assertEqual(pl.rr_status(self.rr_dir / "RR-2.md"), "CONSUMED")
        self.assertIn("Fresh Phase 4 opened repair requests", out)

    def test_restart_before_phase3_commit_reopens_early_consumed_write(self) -> None:
        request = make_rr(self.rr_dir, "RR-1", "OPEN")
        snapshot = self.p.snapshot_open_repair_requests("footest")
        self.p.persist_open_repair_snapshot("footest", snapshot, 2)

        # CONSUMED written by the child is not a commit: the child may still
        # fail or be killed before returning zero to the orchestrator.
        pl.rr_set_status(request, "CONSUMED", "agent wrote status before exit")
        restarted = make_pipeline(["footest|g|l|r"])
        _, out = quiet(restarted.prepare_repair_state)

        self.assertEqual(pl.rr_status(request), "OPEN")
        self.assertIn("agent wrote status before exit", request.read_text())
        self.assertIn("recovered durable Phase 3 snapshot", out)

    def test_same_round_generation_without_attempt_token_is_not_commit(self) -> None:
        request = make_rr(self.rr_dir, "RR-1", "OPEN")
        # A prior run can have the same repair-round number. Its generation
        # marker must not prove success for this new snapshot.
        self.p.advance_confirmation_generation(2, ["footest"])
        snapshot = self.p.snapshot_open_repair_requests("footest")
        self.p.persist_open_repair_snapshot("footest", snapshot, 2)
        pl.rr_set_status(request, "CONSUMED", "uncommitted attempt")

        restarted = make_pipeline(["footest|g|l|r"])
        quiet(restarted.prepare_repair_state)

        self.assertEqual(pl.rr_status(request), "OPEN")

    def test_malformed_legacy_in_repair_without_snapshot_fails_closed(self) -> None:
        request = self.rr_dir / "RR-1.md"
        request.write_text("---\nid: RR-1\nstatus: IN_REPAIR\n---\n")
        original = request.read_bytes()

        with self.assertRaises(SystemExit) as ctx:
            quiet(self.p.prepare_repair_state)

        self.assertEqual(ctx.exception.code, 1)
        self.assertEqual(request.read_bytes(), original)
        self.assertEqual(pl.rr_status(request), "IN_REPAIR")

    def test_quota_failure_before_phase3_leaves_request_bytes_unchanged(self) -> None:
        request = make_rr(self.rr_dir, "RR-1", "OPEN")
        original = request.read_bytes()
        self.p.wait_for_quota = mock.Mock(side_effect=SystemExit(9))  # type: ignore[method-assign]
        phase3 = mock.Mock()
        self.p.run_phase3_repair = phase3  # type: ignore[method-assign]
        out = io.StringIO()

        with self.assertRaises(SystemExit) as ctx, contextlib.redirect_stdout(out):
            self.p.run_repair_loop()

        self.assertEqual(ctx.exception.code, 9)
        self.assertEqual(request.read_bytes(), original)
        phase3.assert_not_called()
        self.assertIn("before Phase 3", out.getvalue())
        self.assertIn("repair requests were left unchanged", out.getvalue())

    def test_phase_failure_is_not_exhaustion(self) -> None:
        request = make_rr(self.rr_dir, "RR-1", "OPEN")

        def fail(round_: int, names: list[str] | None = None) -> None:
            self.assertEqual(names, ["footest"])
            pl.rr_set_status(request, "IN_REPAIR", "started")
            raise SystemExit(7)

        self.p.run_phase3_repair = fail  # type: ignore[method-assign]
        self.p.wait_for_quota = lambda **kwargs: None  # type: ignore[method-assign]
        out = io.StringIO()
        with self.assertRaises(SystemExit) as ctx, contextlib.redirect_stdout(out):
            self.p.run_repair_loop()
        self.assertEqual(ctx.exception.code, 7)
        self.assertEqual(pl.rr_status(request), "OPEN")
        self.assertFalse((self.rr_dir / "deferred" / request.name).exists())
        self.assertFalse((self.rr_dir.parent / "confirmation-generation.json").exists())
        self.assertIn("failed in round 1 for footest during Phase 3", out.getvalue())
        ledger = self.rr_dir.parent / "repair-ledger.md"
        self.assertIn("| RR-1 | B-1 | SPEC_REPAIR | OPEN | 1 |", ledger.read_text())

    def test_phase3_consumes_then_raises_restores_original_open_set(self) -> None:
        first = make_rr(self.rr_dir, "RR-1", "OPEN")
        second = make_rr(self.rr_dir, "RR-2", "OPEN", bug_id="B-2")
        already_done = make_rr(self.rr_dir, "RR-3", "CONSUMED", bug_id="B-3")

        def fail_after_partial_commit(round_: int, names: list[str] | None = None) -> None:
            self.assertEqual(round_, 1)
            self.assertEqual(names, ["footest"])
            pl.rr_set_status(first, "CONSUMED", "agent committed too early")
            pl.rr_set_status(second, "CONSUMED", "agent committed too early")
            raise RuntimeError("repair process failed after writes")

        self.p.run_phase3_repair = fail_after_partial_commit  # type: ignore[method-assign]
        self.p.wait_for_quota = lambda **kwargs: None  # type: ignore[method-assign]
        with self.assertRaisesRegex(RuntimeError, "failed after writes"):
            quiet(self.p.run_repair_loop)

        self.assertEqual(pl.rr_status(first), "OPEN")
        self.assertEqual(pl.rr_status(second), "OPEN")
        self.assertEqual(pl.rr_status(already_done), "CONSUMED")
        for request in (first, second):
            text = request.read_text()
            self.assertIn("agent committed too early", text)
            self.assertIn("partial spec/output changes were retained", text)

    def test_snapshot_cleanup_failure_never_rolls_back_committed_phase3(self) -> None:
        request = make_rr(self.rr_dir, "RR-1", "OPEN")

        def successful_repair(_banner: str, _script: str, _args: list[str]) -> None:
            pl.rr_set_status(request, "CONSUMED", "repair process returned success")

        self.p._phase = successful_repair  # type: ignore[assignment]
        self.p.wait_for_quota = lambda **kwargs: None  # type: ignore[method-assign]
        self.p.clear_open_repair_snapshot = mock.Mock(side_effect=OSError("injected unlink failure"))  # type: ignore[method-assign]

        out = io.StringIO()
        with self.assertRaisesRegex(OSError, "injected unlink failure"), contextlib.redirect_stdout(out):
            self.p.run_repair_loop()

        snapshot_path = self.p.repair_phase3_snapshot_path("footest")
        snapshot_doc = json.loads(snapshot_path.read_text())
        generation = json.loads((self.rr_dir.parent / "confirmation-generation.json").read_text())
        self.assertEqual(generation["repair_phase3_commit"], snapshot_doc["commit_token"])
        self.assertEqual(pl.rr_status(request), "CONSUMED")
        self.assertNotIn("partial spec/output changes were retained", request.read_text())
        self.assertIn("CONSUMED state was retained for startup recovery", out.getvalue())

        restarted = make_pipeline(["footest|g|l|r"])
        _, recovery_out = quiet(restarted.prepare_repair_state)
        self.assertEqual(pl.rr_status(request), "CONSUMED")
        self.assertFalse(snapshot_path.exists())
        self.assertIn("finalized committed repair Phase 3", recovery_out)

    def test_phase3_truncation_restores_complete_snapshot_semantics(self) -> None:
        request = make_rr(self.rr_dir, "RR-1", "OPEN")

        def truncate_then_fail(round_: int, names: list[str] | None = None) -> None:
            self.assertEqual((round_, names), (1, ["footest"]))
            request.write_text("---\nid: RR-1\nstatus: CONSUMED\n")
            raise RuntimeError("truncated request")

        self.p.run_phase3_repair = truncate_then_fail  # type: ignore[method-assign]
        self.p.wait_for_quota = lambda **kwargs: None  # type: ignore[method-assign]

        with self.assertRaisesRegex(RuntimeError, "truncated request"):
            quiet(self.p.run_repair_loop)

        restored = request.read_text()
        self.assertEqual(pl.rr_status(request), "OPEN")
        self.assertIn("target: SPEC_REPAIR", restored)
        self.assertIn("# Repair Request RR-1", restored)
        self.assertIn("## History\n- created", restored)
        self.assertIn("partial spec/output changes were retained", restored)

    def test_failure_in_later_target_keeps_earlier_target_consumed(self) -> None:
        p = make_pipeline(["alpha|g|l|r", "beta|g|l|r"])
        alpha_dir = self.tmp / "alpha" / ".specula-output" / "spec" / "repair-requests"
        beta_dir = self.tmp / "beta" / ".specula-output" / "spec" / "repair-requests"
        alpha_dir.mkdir(parents=True)
        beta_dir.mkdir(parents=True)
        alpha = make_rr(alpha_dir, "RR-1", "OPEN", bug_id="A-1")
        beta = make_rr(beta_dir, "RR-1", "OPEN", bug_id="B-1")
        calls: list[str] = []

        def repair(round_: int, names: list[str] | None = None) -> None:
            self.assertEqual(round_, 1)
            assert names is not None
            name = names[0]
            calls.append(name)
            request = alpha if name == "alpha" else beta
            pl.rr_set_status(request, "CONSUMED", f"{name} wrote partial state")
            if name == "beta":
                raise RuntimeError("beta failed")

        p.run_phase3_repair = repair  # type: ignore[method-assign]
        p.run_phase4_confirmation = lambda: self.fail("Phase 4 must not run")  # type: ignore[method-assign]
        p.wait_for_quota = lambda **kwargs: None  # type: ignore[method-assign]

        with self.assertRaisesRegex(RuntimeError, "beta failed"):
            quiet(p.run_repair_loop)

        self.assertEqual(calls, ["alpha", "beta"])
        self.assertEqual(pl.rr_status(alpha), "CONSUMED")
        self.assertEqual(pl.rr_status(beta), "OPEN")
        self.assertNotIn("partial spec/output changes were retained", alpha.read_text())
        self.assertIn("beta wrote partial state", beta.read_text())
        self.assertIn("partial spec/output changes were retained", beta.read_text())

    def test_main_resumes_in_repair_before_ordinary_phase3(self) -> None:
        request = make_rr(self.rr_dir, "RR-1", "IN_REPAIR")
        events: list[str] = []

        def repair(round_: int, names: list[str] | None = None) -> None:
            self.assertEqual(round_, 1)
            self.assertEqual(names, ["footest"])
            events.append(f"repair:{pl.rr_status(request)}")
            pl.rr_set_status(request, "CONSUMED", "retry completed")

        self.p.skip_analysis = True
        self.p.skip_specgen = True
        self.p.skip_harness = True
        self.p.skip_validation = False
        self.p.skip_classification = True
        self.p.validate_agent_adapter = lambda: None  # type: ignore[method-assign]
        self.p.generate_summary = lambda: None  # type: ignore[method-assign]
        self.p.wait_for_quota = lambda **kwargs: None  # type: ignore[method-assign]
        self.p.run_phase3_repair = repair  # type: ignore[method-assign]
        self.p.run_phase3_validation = lambda: self.fail("ordinary Phase 3 ran before recovery")  # type: ignore[method-assign]
        self.p.run_phase4_confirmation = lambda: events.append("confirm")  # type: ignore[method-assign]

        rc, out = quiet(self.p.main)

        self.assertEqual(rc, 0)
        self.assertEqual(events, ["repair:OPEN", "confirm"])
        self.assertIn("Resuming pending repair requests before the ordinary Phase 3 pass", out)
        self.assertIn("Ordinary Phase 3 covered for every target by the resumed repair loop", out)
        self.assertIn("Initial Phase 4 completed by the resumed repair loop", out)

    def _assert_skip_flag_still_recovers_before_phase3(self, *, skip_confirmation: bool, skip_repair: bool) -> None:
        request = make_rr(self.rr_dir, "RR-1", "OPEN")
        snapshot = self.p.snapshot_open_repair_requests("footest")
        self.p.persist_open_repair_snapshot("footest", snapshot, 2)
        request.write_text("---\nid: RR-1\nstatus: IN_REPAIR\n")
        observed: list[str] = []

        def ordinary_phase3() -> None:
            text = request.read_text()
            self.assertEqual(pl.rr_status(request), "OPEN")
            self.assertIn("target: SPEC_REPAIR", text)
            self.assertIn("## Evidence", text)
            observed.append("ordinary-phase3-after-recovery")

        self.p.skip_analysis = True
        self.p.skip_specgen = True
        self.p.skip_harness = True
        self.p.skip_confirmation = skip_confirmation
        self.p.skip_repair_loop = skip_repair
        self.p.skip_classification = True
        self.p.validate_agent_adapter = lambda: None  # type: ignore[method-assign]
        self.p.generate_summary = lambda: None  # type: ignore[method-assign]
        self.p.wait_for_quota = lambda **kwargs: None  # type: ignore[method-assign]
        self.p.run_phase3_validation = ordinary_phase3  # type: ignore[method-assign]
        self.p.run_phase3_repair = lambda *_args: self.fail("skip flag did not prevent repair resume")  # type: ignore[method-assign]
        self.p.run_phase4_confirmation = lambda: observed.append("phase4")  # type: ignore[method-assign]

        rc, _out = quiet(self.p.main)

        self.assertEqual(rc, 0)
        expected = ["ordinary-phase3-after-recovery"] + ([] if skip_confirmation else ["phase4"])
        self.assertEqual(observed, expected)
        self.assertFalse(self.p.repair_phase3_snapshot_path("footest").exists())

    def test_skip_confirmation_still_recovers_before_ordinary_phase3(self) -> None:
        self._assert_skip_flag_still_recovers_before_phase3(skip_confirmation=True, skip_repair=False)

    def test_skip_repair_loop_still_recovers_before_ordinary_phase3(self) -> None:
        self._assert_skip_flag_still_recovers_before_phase3(skip_confirmation=False, skip_repair=True)

    def test_phase4_failure_keeps_consumed_and_full_rerun_retries_phase4(self) -> None:
        request = make_rr(self.rr_dir, "RR-1", "OPEN")
        phase4_calls: list[int] = []

        def successful_repair(_banner: str, _script: str, _args: list[str]) -> None:
            pl.rr_set_status(request, "CONSUMED", "Phase 3 completed")

        def confirmation() -> None:
            phase4_calls.append(len(phase4_calls) + 1)
            if len(phase4_calls) == 1:
                raise SystemExit(8)

        self.p._phase = successful_repair  # type: ignore[assignment]
        self.p.run_phase4_confirmation = confirmation  # type: ignore[method-assign]
        self.p.wait_for_quota = lambda **kwargs: None  # type: ignore[method-assign]
        out = io.StringIO()
        with self.assertRaises(SystemExit) as ctx, contextlib.redirect_stdout(out):
            self.p.run_repair_loop()
        self.assertEqual(ctx.exception.code, 8)
        self.assertEqual(pl.rr_status(request), "CONSUMED")
        self.assertEqual(json.loads((self.rr_dir.parent / "confirmation-generation.json").read_text())["generation"], 1)
        self.assertIn("successful Phase 3 request states were retained", out.getvalue())

        # A full pipeline retry invokes normal Phase 4 before entering the
        # repair loop. With no OPEN request the loop then safely becomes a no-op.
        self.p.skip_analysis = True
        self.p.skip_specgen = True
        self.p.skip_harness = True
        self.p.skip_validation = True
        self.p.skip_classification = True
        self.p.validate_agent_adapter = lambda: None  # type: ignore[method-assign]
        self.p.generate_summary = lambda: None  # type: ignore[method-assign]
        rc, retry_out = quiet(self.p.main)
        self.assertEqual(rc, 0)
        self.assertEqual(phase4_calls, [1, 2])
        self.assertIn("No OPEN repair requests", retry_out)
        self.assertEqual(pl.rr_status(request), "CONSUMED")

    def test_only_progress_followed_by_cap_defers(self) -> None:
        first = make_rr(self.rr_dir, "RR-1", "OPEN")
        report = self.rr_dir.parent.parent / "confirmed-bugs.md"
        report.write_text("Status: PENDING REPAIR (RR-2)\n")
        self.p.max_repair_rounds = "1"

        def replace_request(round_: int) -> None:
            pl.rr_set_status(first, "CONSUMED", "fixed")
            make_rr(self.rr_dir, "RR-2", "OPEN", bug_id="B-2", round_=round_)

        rounds, out = self.drive(replace_request)
        self.assertEqual(rounds, [1])
        self.assertIn("reached its 1-round cap", out)
        self.assertEqual(pl.rr_status(first), "CONSUMED")
        deferred = self.rr_dir / "deferred" / "RR-2.md"
        self.assertEqual(pl.rr_status(deferred), "DEFERRED")
        self.assertFalse((self.rr_dir / "RR-2.md").exists())
        self.assertIn("DEFERRED (repair loop exhausted; RR-2 in deferred/)", report.read_text())
        ledger = self.rr_dir.parent / "repair-ledger.md"
        ledger_text = ledger.read_text()
        self.assertIn("| RR-1 | B-1 | SPEC_REPAIR | CONSUMED | 1 |", ledger_text)
        self.assertIn("| RR-2 | B-2 | SPEC_REPAIR | DEFERRED | 1 |", ledger_text)

    def test_no_progress_at_cap_still_fails_instead_of_deferring(self) -> None:
        request = make_rr(self.rr_dir, "RR-1", "OPEN")
        self.p.max_repair_rounds = "1"
        self.configure(lambda round_: None)
        with self.assertRaisesRegex(RuntimeError, "without consuming"):
            quiet(self.p.run_repair_loop)
        self.assertTrue(request.exists())
        self.assertEqual(pl.rr_status(request), "OPEN")
        self.assertFalse((self.rr_dir / "deferred" / request.name).exists())

    def test_direct_invalid_cap_fails_before_mutation(self) -> None:
        request = make_rr(self.rr_dir, "RR-1", "OPEN")
        self.p.max_repair_rounds = "-1"
        with self.assertRaises(SystemExit) as ctx:
            quiet(self.p.run_repair_loop)
        self.assertEqual(ctx.exception.code, 1)
        self.assertTrue(request.exists())


class TestConfirmationGeneration(RRDirCase):
    def marker(self) -> Path:
        return self.rr_dir.parent / "confirmation-generation.json"

    def test_generation_increments_atomically(self) -> None:
        self.p.advance_confirmation_generation(1)
        first = json.loads(self.marker().read_text())
        self.assertEqual(first["generation"], 1)
        self.assertEqual(first["repair_round"], 1)
        self.p.advance_confirmation_generation(2)
        second = json.loads(self.marker().read_text())
        self.assertEqual(second["generation"], 2)
        self.assertEqual(second["repair_round"], 2)
        self.assertEqual(list(self.marker().parent.glob(".confirmation-generation.json.*.tmp")), [])

    def test_invalid_legacy_marker_is_replaced(self) -> None:
        self.marker().write_text("not json\n")
        _, out = quiet(self.p.advance_confirmation_generation, 3)
        doc = json.loads(self.marker().read_text())
        self.assertEqual(doc["generation"], 1)
        self.assertEqual(doc["repair_round"], 3)
        self.assertIn("replacing invalid confirmation generation marker", out)

    def test_normal_phase3_success_and_resume_each_advance_generation(self) -> None:
        self.p._phase = lambda _banner, _script, _args: None  # type: ignore[assignment]

        self.p.run_phase3_validation()
        first = json.loads(self.marker().read_text())
        self.assertEqual((first["generation"], first["repair_round"]), (1, 0))

        self.p.run_phase3_validation()
        second = json.loads(self.marker().read_text())
        self.assertEqual((second["generation"], second["repair_round"]), (2, 0))

    def test_failed_normal_phase3_does_not_advance_generation(self) -> None:
        self.p.advance_confirmation_generation(0)
        before = self.marker().read_text()

        def fail(_banner: str, _script: str, _args: list[str]) -> None:
            raise SystemExit(7)

        self.p._phase = fail  # type: ignore[assignment]
        with self.assertRaises(SystemExit) as ctx:
            self.p.run_phase3_validation()
        self.assertEqual(ctx.exception.code, 7)
        self.assertEqual(self.marker().read_text(), before)

    def test_marker_exists_before_fresh_phase4(self) -> None:
        request = make_rr(self.rr_dir, "RR-1", "OPEN")
        seen: list[dict[str, Any]] = []

        def repair(_banner: str, _script: str, _args: list[str]) -> None:
            pl.rr_set_status(request, "CONSUMED", "fixed")

        self.p._phase = repair  # type: ignore[assignment]
        self.p.run_phase4_confirmation = lambda: seen.append(json.loads(self.marker().read_text()))  # type: ignore[method-assign]
        self.p.wait_for_quota = lambda **kwargs: None  # type: ignore[method-assign]
        quiet(self.p.run_repair_loop)
        self.assertEqual([(d["generation"], d["repair_round"]) for d in seen], [(1, 1)])
        self.assertEqual(json.loads(self.marker().read_text())["generation"], 1)

    def test_dry_run_does_not_write_marker(self) -> None:
        self.p.dry_run = True
        quiet(self.p.run_phase3_validation)
        self.assertFalse(self.marker().exists())


class TestDeferredMoves(RRDirCase):
    def test_reconcile_disposition_counts_supports_current_aggregate_format(self) -> None:
        report = (
            "Dispositions: 3 total = 0 reproduced + 0 env-limited + 0 masked + 0 false-positive "
            "+ 0 needs-more-info + 0 dropped + 2 pending-repair + 1 incomplete + 0 deferred\n\n"
            "| Entry | Finding | Status | Counts as final bug? |\n"
            "|---|---|---|---|\n"
            "| 1 | MC-1 | DEFERRED (repair loop exhausted; RR-1 in deferred/) | no |\n"
            "| 2 | MC-2 | PENDING REPAIR (RR-2) | no |\n"
            "| 3 | MC-3 | INCOMPLETE | no |\n"
        )

        reconciled = self.p._reconcile_disposition_counts(report)

        self.assertIn("+ 1 pending-repair + 1 incomplete + 1 deferred", reconciled)

    def test_only_open_moves_consumed_stays_active(self) -> None:
        consumed = make_rr(self.rr_dir, "RR-1", "CONSUMED")
        opened = make_rr(self.rr_dir, "RR-2", "OPEN")
        moved, _ = quiet(self.p.move_open_requests_to_deferred)
        self.assertEqual(moved, 1)
        self.assertTrue(consumed.exists())
        self.assertFalse(opened.exists())
        self.assertEqual(pl.rr_status(self.rr_dir / "deferred" / "RR-2.md"), "DEFERRED")

    def test_unknown_or_in_repair_state_is_rejected(self) -> None:
        for status in ("IN_REPAIR", "BROKEN"):
            with self.subTest(status=status):
                for f in self.rr_dir.glob("RR-*.md"):
                    f.unlink()
                request = make_rr(self.rr_dir, "RR-1", status)
                with self.assertRaises(SystemExit) as ctx:
                    quiet(self.p.move_open_requests_to_deferred)
                self.assertEqual(ctx.exception.code, 1)
                self.assertTrue(request.exists())

    def test_existing_deferred_request_is_never_overwritten(self) -> None:
        source = make_rr(self.rr_dir, "RR-1", "OPEN", bug_id="new")
        deferred_dir = self.rr_dir / "deferred"
        deferred_dir.mkdir()
        existing = make_rr(deferred_dir, "RR-1", "OPEN", bug_id="old")
        old_text = existing.read_text()
        with self.assertRaises(SystemExit) as ctx:
            quiet(self.p.move_open_requests_to_deferred)
        self.assertEqual(ctx.exception.code, 1)
        self.assertTrue(source.exists())
        self.assertEqual(existing.read_text(), old_text)

    def test_startup_finishes_exact_publish_then_unlink_crash_copy(self) -> None:
        source = make_rr(self.rr_dir, "RR-1", "OPEN")
        destination = self.rr_dir / "deferred" / source.name
        destination.parent.mkdir()
        destination.write_text(
            self.p._repair_request_text_with_status(
                source.read_text(),
                "DEFERRED",
                "deferred (orchestrator): repair loop round cap reached",
            )
        )

        _, out = quiet(self.p.run_repair_loop)

        self.assertFalse(source.exists())
        self.assertEqual(pl.rr_status(destination), "DEFERRED")
        self.assertIn("completed interrupted defer move", out)
        self.assertIn("repair loop is a no-op", out)

    def test_startup_rejects_divergent_active_and_deferred_copy(self) -> None:
        source = make_rr(self.rr_dir, "RR-1", "OPEN", bug_id="active")
        deferred_dir = self.rr_dir / "deferred"
        deferred_dir.mkdir()
        destination = make_rr(deferred_dir, "RR-1", "DEFERRED", bug_id="different")

        with self.assertRaises(SystemExit) as ctx:
            quiet(self.p.run_repair_loop)

        self.assertEqual(ctx.exception.code, 1)
        self.assertTrue(source.exists())
        self.assertTrue(destination.exists())

    def test_source_unlink_failure_is_completed_from_durable_intent(self) -> None:
        source = make_rr(self.rr_dir, "RR-1", "OPEN")
        original = source.read_text()
        destination = self.rr_dir / "deferred" / source.name
        real_unlink = Path.unlink

        def fail_source_unlink(path: Path, *args: Any, **kwargs: Any) -> None:
            if path == source:
                raise OSError("injected source unlink failure")
            real_unlink(path, *args, **kwargs)

        with (
            mock.patch.object(Path, "unlink", fail_source_unlink),
            self.assertRaisesRegex(OSError, "injected source unlink failure"),
        ):
            quiet(self.p.move_open_requests_to_deferred)

        self.assertEqual(source.read_text(), original)
        self.assertEqual(pl.rr_status(destination), "DEFERRED")
        self.assertTrue(self.p.repair_defer_intent_path().is_file())
        self.assertEqual(list(destination.parent.glob(".*.tmp")), [])

        quiet(self.p.reconcile_deferred_state)
        self.assertFalse(source.exists())
        self.assertEqual(pl.rr_status(destination), "DEFERRED")
        self.assertFalse(self.p.repair_defer_intent_path().exists())

    def test_startup_completes_every_request_in_partially_applied_cap_batch(self) -> None:
        first = make_rr(self.rr_dir, "RR-1", "OPEN")
        second = make_rr(self.rr_dir, "RR-2", "OPEN", bug_id="B-2")
        real_publish = self.p._publish_deferred_no_replace

        def fail_second_publish(path: Path, text: str) -> None:
            if path.name == "RR-2.md":
                raise OSError("injected second publish failure")
            real_publish(path, text)

        with (
            mock.patch.object(self.p, "_publish_deferred_no_replace", side_effect=fail_second_publish),
            self.assertRaisesRegex(OSError, "injected second publish failure"),
        ):
            quiet(self.p.move_open_requests_to_deferred)

        self.assertFalse(first.exists())
        self.assertTrue(second.exists())
        self.assertEqual(pl.rr_status(self.rr_dir / "deferred" / "RR-1.md"), "DEFERRED")
        self.assertTrue(self.p.repair_defer_intent_path().is_file())

        quiet(self.p.reconcile_deferred_state)
        self.assertFalse(first.exists())
        self.assertFalse(second.exists())
        self.assertEqual(pl.rr_status(self.rr_dir / "deferred" / "RR-1.md"), "DEFERRED")
        self.assertEqual(pl.rr_status(self.rr_dir / "deferred" / "RR-2.md"), "DEFERRED")
        self.assertFalse(self.p.repair_defer_intent_path().exists())

    def test_startup_reconciles_legacy_deferred_status_and_report(self) -> None:
        deferred_dir = self.rr_dir / "deferred"
        deferred_dir.mkdir()
        request = make_rr(deferred_dir, "RR-1", "OPEN")
        report = self.rr_dir.parent.parent / "confirmed-bugs.md"
        report.write_text(
            "# Confirmed Bugs\n\n"
            "Dispositions: 2 total = 0 reproduced + 0 env-limited + 0 masked + 0 false-positive "
            "+ 0 needs-more-info + 0 dropped + 2 pending-repair\n\n"
            "| Bug | Finding | Status |\n"
            "|---|---|---|\n"
            "| 1 | MC-1 | PENDING REPAIR (RR-1) |\n"
            "| 2 | MC-2 | PENDING REPAIR (RR-2) |\n\n"
            "- **Status**: PENDING REPAIR (RR-1)\n"
        )

        quiet(self.p.run_repair_loop)
        self.assertEqual(pl.rr_status(request), "DEFERRED")
        self.assertIn("deferred directory is authoritative", request.read_text())
        self.assertIn("DEFERRED (repair loop exhausted; RR-1 in deferred/)", report.read_text())
        self.assertIn("+ 1 pending-repair + 1 deferred", report.read_text())

        request_after = request.read_text()
        report_after = report.read_text()
        quiet(self.p.run_repair_loop)
        self.assertEqual(request.read_text(), request_after)
        self.assertEqual(report.read_text(), report_after)

    def test_report_write_failure_is_recovered_on_next_startup(self) -> None:
        source = make_rr(self.rr_dir, "RR-1", "OPEN")
        destination = self.rr_dir / "deferred" / source.name
        report = self.rr_dir.parent.parent / "confirmed-bugs.md"
        report.write_text(
            "Dispositions: 1 total = 0 reproduced + 0 env-limited + 0 masked + 0 false-positive "
            "+ 0 needs-more-info + 0 dropped + 1 pending-repair\n\n"
            "| Bug | Finding | Status |\n"
            "|---|---|---|\n"
            "| 1 | MC-1 | PENDING REPAIR (RR-1) |\n"
        )
        real_replace = self.p._atomic_replace_text
        failed = False

        def fail_first_report_write(path: Path, text: str) -> None:
            nonlocal failed
            if path == report and not failed:
                failed = True
                raise OSError("injected report write failure")
            real_replace(path, text)

        self.p._atomic_replace_text = fail_first_report_write  # type: ignore[method-assign]
        with self.assertRaisesRegex(OSError, "injected report write failure"):
            quiet(self.p.move_open_requests_to_deferred)
        self.assertFalse(source.exists())
        self.assertEqual(pl.rr_status(destination), "DEFERRED")
        self.assertIn("PENDING REPAIR (RR-1)", report.read_text())

        self.p._atomic_replace_text = real_replace  # type: ignore[method-assign]
        quiet(self.p.run_repair_loop)
        self.assertIn("DEFERRED (repair loop exhausted; RR-1 in deferred/)", report.read_text())
        self.assertIn("+ 0 pending-repair + 1 deferred", report.read_text())
        self.assertEqual(pl.rr_status(destination), "DEFERRED")


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

    def test_phase_receives_explicit_tlc_resource_limits(self) -> None:
        captured = self.tmp / "resources"
        p = self._pipeline(
            f'printf \'%s\\n\' "$SPECULA_TLC_MEMORY_LIMIT" "$SPECULA_TLC_WORKER_LIMIT" '
            f'"$SPECULA_TLC_SCOPE" > "{captured}"\n'
        )
        p.tlc_memory_limit = "80G"
        p.tlc_worker_limit = "12"
        p.tlc_scope = "/tmp/specula-run-scope"
        p._run_launcher("fake.sh", [])
        self.assertEqual(captured.read_text().splitlines(), ["80G", "12", "/tmp/specula-run-scope"])

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

    def test_final_source_capture_runs_after_pipeline_failure(self) -> None:
        marker = self.tmp / "captured"
        r = self._run_entry(
            "def boom(self):\n    raise SystemExit(7)\n"
            f"def capture(self):\n    open({str(marker)!r}, 'w').write('done')\n"
            "pl.Pipeline.main = boom\npl.Pipeline.finalize_source_snapshots = capture"
        )
        self.assertEqual(r.returncode, 7)
        self.assertEqual(marker.read_text(), "done")

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
