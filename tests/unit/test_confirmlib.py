"""Unit tests for parallel per-finding bug confirmation (src/specula/confirmlib.py).

Run in-process: agent turns are monkeypatched (no adapter spawn, no network), so
these pin the dispatcher's control flow that the phase/pipeline tests don't reach
— verdict parsing, the debate gate, the RR lifecycle merge, candidate validation,
partial-delivery return codes, and idempotent retry.

    uv run python -m unittest tests.unit.test_confirmlib -v
"""

from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import tempfile
import unittest
from collections.abc import Callable
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from typing import Any
from unittest import mock

from specula import confirmlib as C
from specula import prompts as P
from specula.phaselib import Workspace

EVIDENCE = "The investigation inspected the real call path and captured concrete observed behavior."


def _response(status: str, extra: str = "") -> str:
    return f"{EVIDENCE}\n{extra}\nVERDICT: {status}".strip()


def _fake_turn(text: str, rc: int = 0) -> Callable[..., tuple[int, str]]:
    """A run_agent_blocking replacement that returns a fixed (rc, text)."""

    def _f(*_args: object, **_kwargs: object) -> tuple[int, str]:
        return (rc, text)

    return _f


def _fake_turn_with_repro(ws: Workspace, name: str, fid: str, text: str) -> Callable[..., tuple[int, str]]:
    def _f(*_args: object, **_kwargs: object) -> tuple[int, str]:
        repro = ws.work_dir(name) / "repro" / f"test_bug{fid}_case.py"
        repro.parent.mkdir(parents=True, exist_ok=True)
        repro.write_text("assert True\n")
        return (0, text)

    return _f


def _boom(*_args: object, **_kwargs: object) -> tuple[int, str]:
    raise AssertionError("run_agent_blocking must not be called (cached finding)")


class ConfirmCase(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.mkdtemp()
        self._old = os.environ.get("SPECULA_RUN_DIR")
        os.environ["SPECULA_RUN_DIR"] = self.tmp
        self.addCleanup(self._restore)

    def _restore(self) -> None:
        if self._old is None:
            os.environ.pop("SPECULA_RUN_DIR", None)
        else:
            os.environ["SPECULA_RUN_DIR"] = self._old
        shutil.rmtree(self.tmp, ignore_errors=True)

    def seed(self, name: str, findings: list[dict[str, Any]]) -> Workspace:
        ws = Workspace([name])
        spec = ws.work_dir(name) / "spec"
        spec.mkdir(parents=True, exist_ok=True)
        (spec / "candidates.json").write_text(json.dumps({"findings": findings}))
        return ws

    def cfg(self, ws: Workspace, name: str, **kw: Any) -> C.ConfirmConfig:
        return C.ConfirmConfig(name=name, ws=ws, adapter=Path("/x"), worktree=False, repo_dir="", **kw)

    def finding(self, ws: Workspace, name: str, fid: str = "MC-1") -> C.Finding:
        fdir = ws.work_dir(name) / "confirmation" / fid
        return C.Finding({"id": fid, "title": "t", "summary": "s"}, fdir)


class TestVerdict(ConfirmCase):
    def test_parse_verdict(self) -> None:
        self.assertEqual(C.parse_verdict("noise\nVERDICT: REPRODUCED"), "REPRODUCED")
        self.assertEqual(C.parse_verdict("VERDICT: PENDING REPAIR (RR-001)"), "PENDING REPAIR")
        self.assertIsNone(C.parse_verdict("no verdict line"))
        self.assertIsNone(C.parse_verdict("VERDICT: not-a-status"))
        # last VERDICT line wins
        self.assertEqual(C.parse_verdict("VERDICT: DROPPED\nVERDICT: FALSE POSITIVE"), "FALSE POSITIVE")


class TestConfirmConfigCompatibility(ConfirmCase):
    def test_legacy_positional_arguments_keep_their_meaning(self) -> None:
        ws = Workspace(["T"])
        cfg = C.ConfirmConfig("T", ws, Path("/adapter"), "/repo", 7, "alias", False, True, "EXTRA")
        self.assertFalse(cfg.worktree)
        self.assertTrue(cfg.dry_run)
        self.assertEqual(cfg.prompt_extra, "EXTRA")
        self.assertIsNone(cfg.model)
        self.assertIsNone(cfg.effort)

    def test_turn_threads_explicit_empty_tuning(self) -> None:
        ws = Workspace(["T"])
        cfg = C.ConfirmConfig("T", ws, Path("/adapter"), worktree=False, model="", effort="")
        finding = C.Finding({"id": "MC-1"}, ws.work_dir("T") / "confirmation" / "MC-1")
        with mock.patch.object(C, "run_agent_blocking", return_value=(0, "VERDICT: FALSE POSITIVE")) as run:
            verdict, _ = C.run_turn(cfg, finding, "A", 1, "prompt")
        self.assertEqual(verdict, "FALSE POSITIVE")
        self.assertEqual(run.call_args.kwargs["model"], "")
        self.assertEqual(run.call_args.kwargs["effort"], "")


class TestMergeRR(ConfirmCase):
    AGENT_BODY = (
        "---\n"
        "target: SPEC_REPAIR\n"
        "counterexample: spec/output/x.out\n"
        "scope:\n"
        "  actions: [Foo]\n"
        "  invariants: [Inv]\n"
        "  hunt_cfgs: [MC_hunt.cfg]\n"
        "  fault_actions: []\n"
        "---\n\nThe counterexample disagrees with src/node.py:42 and the captured trace demonstrates the mismatch.\n"
    )

    def test_agent_scope_preserved_lifecycle_stamped(self) -> None:
        out = C._merge_rr("RR-001", "MC-1", "fallback.out", self.AGENT_BODY)
        self.assertIn("id: RR-001", out)
        self.assertIn("status: OPEN", out)
        self.assertIn("round: 0", out)
        self.assertIn("actions: [Foo]", out)  # agent scope verbatim
        self.assertIn("hunt_cfgs: [MC_hunt.cfg]", out)

    def test_agent_lifecycle_fields_are_stripped(self) -> None:
        # A stray dispatcher-owned key in the agent body is stripped, never fatal —
        # _merge_rr always stamps the authoritative lifecycle over it.
        sneaky = self.AGENT_BODY.replace("target: SPEC_REPAIR", "id: RR-999\nstatus: CONSUMED\ntarget: SPEC_REPAIR")
        out = C._merge_rr("RR-002", "MC-1", "fb", sneaky)
        self.assertIn("id: RR-002", out)  # stamped id wins
        self.assertNotIn("RR-999", out)  # agent's stray id stripped
        self.assertNotIn("CONSUMED", out)  # agent's stray status stripped
        self.assertIn("status: OPEN", out)

    def test_missing_frontmatter_tolerated(self) -> None:
        # A body without YAML frontmatter is best-effort: the prose becomes evidence
        # and _merge_rr still emits a well-formed request (never rejects the verdict).
        out = C._merge_rr("RR-003", "MC-1", "spec/output/x.out", "prose only")
        self.assertIn("id: RR-003", out)
        self.assertIn("---\nprose only", out)
        self.assertNotIn("---prose only", out)


class TestValidateCandidates(ConfirmCase):
    def test_valid(self) -> None:
        p = Path(self.tmp) / "c.json"
        p.write_text(
            json.dumps({"findings": [{"id": "MC-1", "source": "model-checking", "title": "t", "summary": "s"}]})
        )
        self.assertEqual(C._validate_candidates(p), [])

    def test_invalid_reports_problems(self) -> None:
        p = Path(self.tmp) / "c.json"
        p.write_text(json.dumps({"findings": [{"id": "bad id!", "source": "guess", "title": "", "summary": ""}]}))
        errs = C._validate_candidates(p)
        self.assertTrue(any("filesystem-safe" in e for e in errs))
        self.assertTrue(any("source not in" in e for e in errs))


class TestDriver(ConfirmCase):
    def test_dry_run_no_candidates_returns_zero(self) -> None:
        ws = Workspace(["T"])  # no candidates.json seeded
        rc = C.run_parallel_confirmation(self.cfg(ws, "T", dry_run=True))
        self.assertEqual(rc, 0)

    def test_dry_run_with_candidates_does_not_touch_existing_artifacts(self) -> None:
        ws = self.seed("T", [{"id": "MC-1", "source": "model-checking", "title": "t", "summary": "s"}])
        fdir = ws.work_dir("T") / "confirmation" / "MC-1"
        repro = ws.work_dir("T") / "repro" / "test_bugMC-1_old.py"
        artifacts = {
            fdir / "repair-request.body.md": b"old repair body\n",
            fdir / "debate.md": b"old debate\n",
            fdir / "verdict.json": b"old verdict\n",
            repro: b"old repro\n",
        }
        for path, content in artifacts.items():
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(content)
        with mock.patch.object(C, "run_agent_blocking", _boom):
            self.assertEqual(C.run_parallel_confirmation(self.cfg(ws, "T", dry_run=True)), 0)
        self.assertEqual({path: path.read_bytes() for path in artifacts}, artifacts)

    def test_success_writes_confirmed_bugs(self) -> None:
        ws = self.seed("T", [{"id": "MC-1", "source": "model-checking", "title": "t", "summary": "s"}])
        with mock.patch.object(C, "run_agent_blocking", _fake_turn(_response("FALSE POSITIVE"))):
            rc = C.run_parallel_confirmation(self.cfg(ws, "T"))
        self.assertEqual(rc, 0)
        cb = ws.work_dir("T") / "spec" / "confirmed-bugs.md"
        self.assertTrue(cb.is_file() and cb.stat().st_size > 0)

    def test_configured_max_parallel_reaches_executor(self) -> None:
        ws = self.seed("T", [{"id": "MC-1", "source": "model-checking", "title": "t", "summary": "s"}])
        real_executor = ThreadPoolExecutor
        worker_counts: list[int] = []

        def executor(*args: Any, **kwargs: Any) -> ThreadPoolExecutor:
            worker_counts.append(kwargs["max_workers"])
            return real_executor(*args, **kwargs)

        with (
            mock.patch.object(C, "ThreadPoolExecutor", side_effect=executor),
            mock.patch.object(C, "run_agent_blocking", _fake_turn("VERDICT: FALSE POSITIVE")),
        ):
            rc = C.run_parallel_confirmation(self.cfg(ws, "T", max_parallel=1))

        self.assertEqual(rc, 0)
        self.assertEqual(worker_counts, [1])

    def test_rate_limit_finding_is_incomplete_delivers(self) -> None:
        # A rate-limited finding no longer withholds the whole target: it becomes an
        # INCOMPLETE row, the report is still delivered, and its verdict is NOT cached
        # so a retry re-attempts it.
        ws = self.seed("T", [{"id": "MC-1", "source": "model-checking", "title": "t", "summary": "s"}])
        with mock.patch.object(C, "run_agent_blocking", _fake_turn("", rc=75)):
            rc = C.run_parallel_confirmation(self.cfg(ws, "T"))
        self.assertEqual(rc, 75)
        cb = ws.work_dir("T") / "spec" / "confirmed-bugs.md"
        self.assertTrue(cb.is_file())  # delivered, not withheld
        self.assertIn("INCOMPLETE", cb.read_text())
        self.assertFalse((ws.work_dir("T") / "confirmation" / "MC-1" / "verdict.json").is_file())  # not cached

    def test_idempotent_skip_on_retry(self) -> None:
        ws = self.seed("T", [{"id": "MC-1", "source": "model-checking", "title": "t", "summary": "s"}])
        with mock.patch.object(C, "run_agent_blocking", _fake_turn(_response("FALSE POSITIVE"))):
            C.run_parallel_confirmation(self.cfg(ws, "T"))
        # Second run: a cached terminal verdict must short-circuit — no agent call.
        with mock.patch.object(C, "run_agent_blocking", _boom):
            rc = C.run_parallel_confirmation(self.cfg(ws, "T"))
        self.assertEqual(rc, 0)

    def test_rate_limit_overwrites_stale_report(self) -> None:
        # A prior run's confirmed-bugs.md is overwritten by the fresh (partial) report
        # rather than left stale: the rate-limited finding shows up as INCOMPLETE.
        ws = self.seed("T", [{"id": "MC-1", "source": "model-checking", "title": "t", "summary": "s"}])
        stale = ws.work_dir("T") / "spec" / "confirmed-bugs.md"
        stale.write_text("# STALE REPORT from a prior run\n")
        with mock.patch.object(C, "run_agent_blocking", _fake_turn("", rc=75)):
            rc = C.run_parallel_confirmation(self.cfg(ws, "T"))
        self.assertEqual(rc, 75)
        text = stale.read_text()
        self.assertNotIn("STALE REPORT", text)  # overwritten, not left stale
        self.assertIn("INCOMPLETE", text)

    def test_consolidate_prompt_invokes_installed_skill_without_path(self) -> None:
        ws = Workspace(["T"])
        spec = ws.work_dir("T") / "spec"
        spec.mkdir(parents=True)
        prompts: list[str] = []

        def run(_adapter: Path, prompt: str, *_args: object, **_kwargs: object) -> tuple[int, str]:
            prompts.append(prompt)
            (spec / "candidates.json").write_text('{"generated_by":"consolidate","findings":[]}')
            return (0, "")

        with mock.patch.object(C, "run_agent_blocking", run):
            C.consolidate(self.cfg(ws, "T"))

        self.assertEqual(len(prompts), 1)
        self.assertIn("installed Specula skill **validation-workflow**", prompts[0])
        self.assertIn("<!-- specula-skill:", prompts[0])
        self.assertIn(":validation-workflow -->", prompts[0])
        self.assertNotIn("$validation-workflow", prompts[0])
        self.assertNotIn("/skills/", prompts[0])
        self.assertNotIn(".claude/skills", prompts[0])

    def test_consolidate_failure_withholds_not_raises(self) -> None:
        # No candidates.json → consolidate runs the agent. A non-75 failure that
        # yields no valid candidates.json must withhold and return failure.
        ws = Workspace(["T"])
        (ws.work_dir("T") / "spec").mkdir(parents=True, exist_ok=True)
        (ws.work_dir("T") / "spec" / "confirmed-bugs.md").write_text("# stale\n")
        with mock.patch.object(C, "run_agent_blocking", _fake_turn("", rc=1)):
            rc = C.run_parallel_confirmation(self.cfg(ws, "T"))
        self.assertEqual(rc, 1)
        self.assertFalse((ws.work_dir("T") / "spec" / "confirmed-bugs.md").is_file())  # stale removed too

    def test_mixed_failures_all_deliver_as_incomplete(self) -> None:
        # A permanent failure + a simultaneous rate limit no longer withhold; both
        # findings become INCOMPLETE and the target still delivers a report.
        findings = [{"id": fid, "source": "model-checking", "title": fid, "summary": "s"} for fid in ("MC-1", "MC-2")]
        ws = self.seed("T", findings)

        def agent(*args: object, **_kwargs: object) -> tuple[int, str]:
            fid = Path(str(args[2])).parent.name
            return (9, "") if fid == "MC-1" else (75, "")

        with mock.patch.object(C, "run_agent_blocking", agent):
            rc = C.run_parallel_confirmation(self.cfg(ws, "T"))
        self.assertEqual(rc, 1)  # permanent failure wins over the simultaneous rate limit
        cb = ws.work_dir("T") / "spec" / "confirmed-bugs.md"
        self.assertTrue(cb.is_file())
        self.assertIn("2 incomplete", cb.read_text())  # both marked in the disposition summary

    def test_cache_write_failure_is_incomplete_delivers(self) -> None:
        # A _save_verdict failure (disk full) makes the finding INCOMPLETE and still
        # delivers the report — never discards it.
        ws = self.seed("T", [{"id": "MC-1", "source": "model-checking", "title": "t", "summary": "s"}])
        report = ws.work_dir("T") / "spec" / "confirmed-bugs.md"
        report.write_text("stale\n")
        with (
            mock.patch.object(C, "run_agent_blocking", _fake_turn(_response("FALSE POSITIVE"))),
            mock.patch.object(C, "_save_verdict", side_effect=OSError("disk full")),
        ):
            rc = C.run_parallel_confirmation(self.cfg(ws, "T"))
        self.assertEqual(rc, 1)
        self.assertTrue(report.is_file())
        self.assertIn("INCOMPLETE", report.read_text())

    def test_pending_repair_without_body_is_allocated_best_effort(self) -> None:
        data = {"id": "MC-1", "source": "model-checking", "title": "t", "summary": "s"}
        ws = self.seed("T", [data])
        fdir = ws.work_dir("T") / "confirmation" / "MC-1"

        with mock.patch.object(C, "run_agent_blocking", _fake_turn(_response("PENDING REPAIR"))):
            rc = C.run_parallel_confirmation(self.cfg(ws, "T"))

        self.assertEqual(rc, 0)
        self.assertFalse((fdir / "repair-request.body.md").exists())
        rr = ws.work_dir("T") / "spec" / "repair-requests" / "RR-001.md"
        self.assertTrue(rr.is_file())
        self.assertIn("status: OPEN", rr.read_text())
        self.assertIn("PENDING REPAIR (RR-001)", (ws.work_dir("T") / "spec" / "confirmed-bugs.md").read_text())
        self.assertTrue((fdir / "verdict.json").is_file())

    def test_log_tee_failure_does_not_block_stale_deliverable_cleanup(self) -> None:
        ws = self.seed("T", [{"id": "MC-1", "source": "model-checking", "title": "t", "summary": "s"}])
        report = ws.work_dir("T") / "spec" / "confirmed-bugs.md"
        report.write_text("stale\n")
        with mock.patch.object(C, "_log", side_effect=OSError("log disk full")):
            self.assertEqual(C.run_parallel_confirmation(self.cfg(ws, "T")), 1)
        self.assertFalse(report.exists())

    def test_retry_reuses_rr_if_cache_update_failed_after_allocation(self) -> None:
        data = {
            "id": "MC-1",
            "source": "model-checking",
            "title": "t",
            "summary": "s",
            "counterexample": "spec/output/x.out",
        }
        ws = self.seed("T", [data])
        spec = ws.work_dir("T") / "spec"
        (spec / "output").mkdir()
        (spec / "output" / "x.out").write_text("trace\n")
        fdir = ws.work_dir("T") / "confirmation" / "MC-1"

        def pending(*_args: object, **_kwargs: object) -> tuple[int, str]:
            fdir.mkdir(parents=True, exist_ok=True)
            (fdir / "repair-request.body.md").write_text(TestMergeRR.AGENT_BODY)
            return (0, _response("PENDING REPAIR"))

        original_save = C._save_verdict
        saves = {"count": 0}

        def fail_second(outcome: C.Outcome, cfg: C.ConfirmConfig) -> None:
            saves["count"] += 1
            if saves["count"] == 2:
                raise OSError("crash after RR allocation")
            original_save(outcome, cfg)

        with (
            mock.patch.object(C, "run_agent_blocking", pending),
            mock.patch.object(C, "_save_verdict", fail_second),
        ):
            self.assertEqual(C.run_parallel_confirmation(self.cfg(ws, "T")), 1)
        rr_dir = spec / "repair-requests"
        self.assertEqual([p.name for p in rr_dir.glob("RR-*.md")], ["RR-001.md"])

        with mock.patch.object(C, "run_agent_blocking", _boom):
            self.assertEqual(C.run_parallel_confirmation(self.cfg(ws, "T")), 0)
        self.assertEqual([p.name for p in rr_dir.glob("RR-*.md")], ["RR-001.md"])
        self.assertIn("PENDING REPAIR (RR-001)", (spec / "confirmed-bugs.md").read_text())


class TestDebateGate(ConfirmCase):
    def test_debate_off_is_a_solo(self) -> None:
        ws = self.seed("T", [])
        cfg = self.cfg(ws, "T", debate=False)
        with mock.patch.object(
            C, "run_agent_blocking", _fake_turn_with_repro(ws, "T", "MC-1", _response("REPRODUCED"))
        ):
            o = C.run_finding(cfg, self.finding(ws, "T"))
        self.assertEqual(o.status, "REPRODUCED")
        self.assertEqual(o.rounds, 0)  # no debate opened

    def test_debate_on_reaches_consensus(self) -> None:
        ws = self.seed("T", [])
        cfg = self.cfg(ws, "T", debate=True, rounds=5)
        with mock.patch.object(
            C, "run_agent_blocking", _fake_turn_with_repro(ws, "T", "MC-2", _response("REPRODUCED"))
        ):
            o = C.run_finding(cfg, self.finding(ws, "T", "MC-2"))
        self.assertEqual(o.status, "REPRODUCED")
        self.assertEqual(o.rounds, 1)  # B then A agree in round 1
        self.assertTrue(o.consensus)

    def test_dismissal_never_opens_debate(self) -> None:
        ws = self.seed("T", [])
        cfg = self.cfg(ws, "T", debate=True, rounds=5)
        with mock.patch.object(C, "run_agent_blocking", _fake_turn(_response("FALSE POSITIVE"))):
            o = C.run_finding(cfg, self.finding(ws, "T", "CR-9"))
        self.assertEqual(o.status, "FALSE POSITIVE")
        self.assertEqual(o.rounds, 0)  # debate exists to challenge confirmations, not dismissals

    def test_b_agrees_skips_a_defense(self) -> None:
        # A confirms, B agrees on its first turn → consensus WITHOUT pulling A into
        # a defense (A never hears about the debate — turn-1 stays debate-blind).
        ws = self.seed("T", [])
        cfg = self.cfg(ws, "T", debate=True, rounds=5)
        calls = {"n": 0}

        def counting(*_a: object, **_k: object) -> tuple[int, str]:
            calls["n"] += 1
            repro = ws.work_dir("T") / "repro" / "test_bugMC-3_case.py"
            repro.parent.mkdir(parents=True, exist_ok=True)
            repro.write_text("assert True\n")
            return (0, _response("REPRODUCED"))

        with mock.patch.object(C, "run_agent_blocking", counting):
            o = C.run_finding(cfg, self.finding(ws, "T", "MC-3"))
        self.assertEqual(o.status, "REPRODUCED")
        self.assertEqual(o.rounds, 1)
        self.assertEqual(calls["n"], 2)  # A reproduce + B challenge; NO A defense turn
        transcript = (ws.work_dir("T") / "confirmation" / "MC-3" / "debate.md").read_text()
        self.assertIn("## B (round 1)", transcript)
        self.assertNotIn("## A (round 1)", transcript)


class TestAggregate(ConfirmCase):
    def _confirmed_bugs(self, body: str, name: str = "T") -> str:
        ws = self.seed(name, [{"id": "MC-1", "source": "model-checking", "title": "the bug", "summary": "s"}])
        text = f"{EVIDENCE}\n{body}"
        runner = (
            _fake_turn_with_repro(ws, name, "MC-1", text) if C.parse_verdict(text) == "REPRODUCED" else _fake_turn(text)
        )
        with mock.patch.object(C, "run_agent_blocking", runner):
            C.run_parallel_confirmation(self.cfg(ws, name))
        return (ws.work_dir(name) / "spec" / "confirmed-bugs.md").read_text()

    def test_heading_is_bug_n_not_finding_id(self) -> None:
        cb = self._confirmed_bugs("- **Novelty**: NEW\nVERDICT: REPRODUCED")
        self.assertIn("## Bug 1: the bug", cb)  # Phase 4b parses integer "## Bug N:"
        self.assertNotIn("## MC-1:", cb)
        self.assertIn("- **Finding ID**: MC-1", cb)  # id carried as a body field
        self.assertIn("| 1 | MC-1 |", cb)  # and a table column

    def test_novelty_split_counts_known_unfixed(self) -> None:
        cb = self._confirmed_bugs("- **Novelty**: KNOWN (cite: http://x; fix-status: unfixed)\nVERDICT: REPRODUCED")
        self.assertIn("Reproduced: 1 = 0 NEW + 1 KNOWN-unfixed + 0 KNOWN-fixed + 0 UNKNOWN", cb)

    def test_novelty_known_fixed_flagged_separately(self) -> None:
        cb = self._confirmed_bugs("- **Novelty**: KNOWN (cite: http://x; fix-status: fixed)\nVERDICT: REPRODUCED")
        self.assertIn("0 NEW + 0 KNOWN-unfixed", cb)
        self.assertIn("+ 1 KNOWN-fixed + 0 UNKNOWN", cb)

    def test_missing_novelty_stays_unknown(self) -> None:
        cb = self._confirmed_bugs("VERDICT: REPRODUCED")
        self.assertIn("Reproduced: 1 = 0 NEW + 0 KNOWN-unfixed + 0 KNOWN-fixed + 1 UNKNOWN", cb)

    def test_masked_is_a_finding_not_a_reproduced_bug(self) -> None:
        cb = self._confirmed_bugs("VERDICT: MASKED")
        self.assertIn("Reproduced: 0 = 0 NEW + 0 KNOWN-unfixed", cb)  # masked is NOT a bug
        self.assertIn("Findings: 1 = 0 env-limited + 1 masked", cb)  # it is a finding
        self.assertIn("| 1 | MC-1 | MASKED |", cb)

    def test_env_limited_counted_as_finding(self) -> None:
        cb = self._confirmed_bugs("VERDICT: ENV_LIMITED")
        self.assertIn("Findings: 1 = 1 env-limited + 0 masked", cb)

    def test_disposition_summary_is_exhaustive(self) -> None:
        ws = self.seed("T", [])
        outcomes: list[C.Outcome] = []
        for index, status in enumerate(C.CANON, 1):
            fid = f"MC-{index}"
            finding = C.Finding(
                {"id": fid, "source": "model-checking", "title": fid, "summary": "s"},
                ws.work_dir("T") / "confirmation" / fid,
            )
            outcomes.append(C.Outcome(finding, status, True, 0, EVIDENCE, bug_no=index))
        C.aggregate(self.cfg(ws, "T"), outcomes)
        report = (ws.work_dir("T") / "spec" / "confirmed-bugs.md").read_text()
        self.assertIn(
            "Dispositions: 7 total = 1 reproduced + 1 env-limited + 1 masked + 1 false-positive "
            "+ 1 needs-more-info + 1 dropped + 1 pending-repair + 0 incomplete + 0 deferred",
            report,
        )


class TestPromptExtraAndLog(ConfirmCase):
    def test_confirmation_prompts_keep_source_specific_outcomes(self) -> None:
        expected = "| MC | `MASKED`, `ENV_LIMITED`, `PENDING REPAIR`, `NEEDS MORE INFO` | `FALSE POSITIVE`, `DROPPED` |"
        for template in ("reproduce", "orchestrate"):
            text = (P.PROMPTS_DIR / "confirmation" / f"{template}.md").read_text()
            self.assertIn(expected, text)
            self.assertIn(
                "| Code Review | `MASKED`, `ENV_LIMITED`, `FALSE POSITIVE`, `DROPPED`, `NEEDS MORE INFO` "
                "| `PENDING REPAIR` |",
                text,
            )

    def test_prompt_extra_appended_to_reproduce(self) -> None:
        ws = self.seed("T", [])
        cfg = self.cfg(ws, "T", prompt_extra="\n## Target-Specific Instructions\n\nCHECK THE FOO RACE")
        f = C.Finding({"id": "MC-1", "title": "t", "summary": "s"}, ws.work_dir("T") / "confirmation" / "MC-1")
        self.assertIn("CHECK THE FOO RACE", C.prompt_reproduce(cfg, f, "/repo"))

    def test_reproduce_prompt_invokes_installed_skill_without_path(self) -> None:
        ws = self.seed("T", [])
        cfg = self.cfg(ws, "T")
        f = C.Finding({"id": "MC-1", "title": "t", "summary": "s"}, ws.work_dir("T") / "confirmation" / "MC-1")

        prompt = C.prompt_reproduce(cfg, f, "/repo")

        self.assertIn("installed Specula skill **bug-confirmation**", prompt)
        self.assertIn("<!-- specula-skill:", prompt)
        self.assertIn(":bug-confirmation -->", prompt)
        self.assertNotIn("$bug-confirmation", prompt)
        self.assertNotIn("/skills/", prompt)
        self.assertNotIn(".claude/skills", prompt)

    def test_bug_confirmation_log_written_and_global_reset(self) -> None:
        ws = self.seed("T", [{"id": "MC-1", "source": "model-checking", "title": "t", "summary": "s"}])
        with mock.patch.object(C, "run_agent_blocking", _fake_turn(_response("FALSE POSITIVE"))):
            C.run_parallel_confirmation(self.cfg(ws, "T"))
        log = ws.work_dir("T") / "bug-confirmation.log"
        self.assertTrue(log.is_file() and log.stat().st_size > 0)  # summary link + tail -f resolve
        self.assertIsNone(C._log_file)  # global reset — does not leak to the next call

    def test_rr_bug_id_is_bug_n(self) -> None:
        ws = self.seed("T", [])
        f = C.Finding(
            {"id": "MC-1", "title": "t", "summary": "s", "counterexample": "x.out"},
            ws.work_dir("T") / "confirmation" / "MC-1",
        )
        f.fdir.mkdir(parents=True, exist_ok=True)
        (f.fdir / "repair-request.body.md").write_text(
            "---\n"
            "target: SPEC_REPAIR\n"
            "counterexample: x.out\n"
            "scope:\n"
            "  actions: [ApplyEntry]\n"
            "  invariants: []\n"
            "  hunt_cfgs: [MC_hunt.cfg]\n"
            "  fault_actions: []\n"
            "---\n\nThe trace step conflicts with the real guard at src/node.py:42 and needs a scoped repair.\n"
        )
        o = C.Outcome(f, "PENDING REPAIR", True, 0, "body", bug_no=3)
        rid = C.allocate_rr(self.cfg(ws, "T"), o)
        rr = (ws.work_dir("T") / "spec" / "repair-requests" / f"{rid}.md").read_text()
        self.assertIn("bug_id: Bug 3", rr)  # points at the "## Bug 3:" heading, not MC-1


class TestCacheContracts(ConfirmCase):
    def test_candidate_reorder_invalidates_bug_number_and_rr_link_cache(self) -> None:
        first = {"id": "MC-1", "source": "model-checking", "title": "one", "summary": "s"}
        second = {"id": "MC-2", "source": "model-checking", "title": "two", "summary": "s"}
        ws = self.seed("T", [first, second])
        cfg = self.cfg(ws, "T")
        finding = C.Finding(first, ws.work_dir("T") / "confirmation" / "MC-1")
        C._save_verdict(C.Outcome(finding, "FALSE POSITIVE", True, 0, EVIDENCE), cfg)
        self.assertIsNotNone(C._load_verdict(finding, cfg))

        candidates = ws.work_dir("T") / "spec" / "candidates.json"
        candidates.write_text(json.dumps({"findings": [second, first]}))
        self.assertIsNone(C._load_verdict(finding, cfg))

    def test_generation_invalidates_candidate_and_verdict_caches(self) -> None:
        finding_data = {
            "id": "MC-1",
            "source": "model-checking",
            "title": "t",
            "summary": "s",
            "invariant": "Inv",
            "config": "MC.cfg",
            "counterexample": "spec/output/MC-1.out",
        }
        ws = self.seed("T", [finding_data])
        spec = ws.work_dir("T") / "spec"
        (spec / "output").mkdir()
        (spec / "output" / "MC-1.out").write_text("counterexample\n")
        (spec / "findings.json").write_text(json.dumps({"findings": [finding_data]}))
        cfg = self.cfg(ws, "T")
        candidates = spec / "candidates.json"
        C._write_candidate_cache(cfg, candidates)
        self.assertTrue(C._candidate_cache_valid(cfg, candidates, {"MC-1"}))

        f = C.Finding(finding_data, ws.work_dir("T") / "confirmation" / "MC-1")
        C._save_verdict(C.Outcome(f, "FALSE POSITIVE", True, 0, EVIDENCE), cfg)
        self.assertIsNotNone(C._load_verdict(f, cfg))

        (spec / "confirmation-generation.json").write_text('{"generation": 1}\n')
        self.assertFalse(C._candidate_cache_valid(cfg, candidates, {"MC-1"}))
        self.assertIsNone(C._load_verdict(f, cfg))

    def test_fresh_generation_reconsolidates_fresh_findings(self) -> None:
        ws = Workspace(["T"])
        spec = ws.work_dir("T") / "spec"
        spec.mkdir(parents=True)
        cfg = self.cfg(ws, "T")
        calls: list[str] = []

        def finding(fid: str) -> dict[str, str]:
            output = spec / "output" / f"{fid}.out"
            output.parent.mkdir(exist_ok=True)
            output.write_text(f"counterexample for {fid}\n")
            return {
                "id": fid,
                "source": "model-checking",
                "title": fid,
                "summary": "summary",
                "invariant": "Inv",
                "config": "MC.cfg",
                "counterexample": f"spec/output/{fid}.out",
            }

        (spec / "findings.json").write_text(json.dumps({"findings": [finding("MC-1")]}))

        def agent(*args: object, **_kwargs: object) -> tuple[int, str]:
            prompt_file = Path(str(args[2]))
            if prompt_file.name == ".consolidate.prompt.md":
                source = json.loads((spec / "findings.json").read_text())
                (spec / "candidates.json").write_text(json.dumps(source))
                calls.append("consolidate")
                return (0, "")
            calls.append(prompt_file.parent.name)
            return (0, _response("FALSE POSITIVE"))

        with mock.patch.object(C, "run_agent_blocking", agent):
            self.assertEqual(C.run_parallel_confirmation(cfg), 0)
            (spec / "findings.json").write_text(json.dumps({"findings": [finding("MC-2")]}))
            (spec / "confirmation-generation.json").write_text('{"generation": 1}\n')
            self.assertEqual(C.run_parallel_confirmation(cfg), 0)

        report = (spec / "confirmed-bugs.md").read_text()
        self.assertIn("MC-2", report)
        self.assertNotIn("MC-1", report)
        self.assertEqual(calls, ["consolidate", "MC-1", "consolidate", "MC-2"])

    def test_same_generation_rate_limit_retry_reuses_completed_verdict(self) -> None:
        findings = [{"id": fid, "source": "model-checking", "title": fid, "summary": "s"} for fid in ("MC-1", "MC-2")]
        ws = self.seed("T", findings)
        first_calls: list[str] = []

        def first(*args: object, **_kwargs: object) -> tuple[int, str]:
            fid = Path(str(args[2])).parent.name
            first_calls.append(fid)
            return (75, "") if fid == "MC-2" else (0, _response("FALSE POSITIVE"))

        with mock.patch.object(C, "run_agent_blocking", first):
            # MC-2 rate-limited -> INCOMPLETE (delivers, rc 75); its verdict is NOT
            # cached, so the retry re-runs only MC-2 and reuses MC-1's completed one.
            self.assertEqual(C.run_parallel_confirmation(self.cfg(ws, "T")), 75)

        retry_calls: list[str] = []

        def retry(*args: object, **_kwargs: object) -> tuple[int, str]:
            retry_calls.append(Path(str(args[2])).parent.name)
            return (0, _response("FALSE POSITIVE"))

        with mock.patch.object(C, "run_agent_blocking", retry):
            self.assertEqual(C.run_parallel_confirmation(self.cfg(ws, "T")), 0)
        self.assertEqual(sorted(first_calls), ["MC-1", "MC-2"])
        self.assertEqual(retry_calls, ["MC-2"])

    def test_cache_binds_adapter_agent_flags_and_confirmation_skill(self) -> None:
        finding_data = {"id": "MC-1", "source": "model-checking", "title": "t", "summary": "s"}
        ws = self.seed("T", [finding_data])
        adapter = Path(self.tmp) / "adapter.sh"
        adapter.write_text("#!/bin/sh\nexit 0\n")
        cfg = C.ConfirmConfig(name="T", ws=ws, adapter=adapter, worktree=False, claude_alias="agent-a", max_turns="3")
        candidates = ws.work_dir("T") / "spec" / "candidates.json"
        f = C.Finding(finding_data, ws.work_dir("T") / "confirmation" / "MC-1")
        with mock.patch.object(C, "_skill_identity", return_value={"guide": "v1"}):
            C._write_candidate_cache(cfg, candidates)
            C._save_verdict(C.Outcome(f, "FALSE POSITIVE", True, 0, EVIDENCE), cfg)
            self.assertTrue(C._candidate_cache_valid(cfg, candidates, None))
            self.assertIsNotNone(C._load_verdict(f, cfg))

        adapter.write_text("#!/bin/sh\nexit 9\n")
        with mock.patch.object(C, "_skill_identity", return_value={"guide": "v1"}):
            self.assertFalse(C._candidate_cache_valid(cfg, candidates, None))
            self.assertIsNone(C._load_verdict(f, cfg))

        adapter.write_text("#!/bin/sh\nexit 0\n")
        with mock.patch.object(C, "_skill_identity", return_value={"guide": "v1"}):
            C._write_candidate_cache(cfg, candidates)
            C._save_verdict(C.Outcome(f, "FALSE POSITIVE", True, 0, EVIDENCE), cfg)
        cfg.claude_alias = "agent-b"
        self.assertFalse(C._candidate_cache_valid(cfg, candidates, None))
        self.assertIsNone(C._load_verdict(f, cfg))

        cfg.claude_alias = "agent-a"
        cfg.max_turns = "4"
        self.assertFalse(C._candidate_cache_valid(cfg, candidates, None))
        self.assertIsNone(C._load_verdict(f, cfg))
        cfg.max_turns = "3"
        with mock.patch.object(C, "_skill_identity", return_value={"guide": "v2"}):
            self.assertIsNone(C._load_verdict(f, cfg))

    def test_cache_binds_model_and_effort(self) -> None:
        finding_data = {"id": "MC-1", "source": "model-checking", "title": "t", "summary": "s"}
        ws = self.seed("T", [finding_data])
        adapter = Path(self.tmp) / "adapter.sh"
        adapter.write_text("#!/bin/sh\nexit 0\n")
        cfg = C.ConfirmConfig(name="T", ws=ws, adapter=adapter, worktree=False)
        candidates = ws.work_dir("T") / "spec" / "candidates.json"
        finding = C.Finding(finding_data, ws.work_dir("T") / "confirmation" / "MC-1")
        with mock.patch.object(C, "_skill_identity", return_value={"guide": "v1"}):
            C._write_candidate_cache(cfg, candidates)
            C._save_verdict(C.Outcome(finding, "FALSE POSITIVE", True, 0, EVIDENCE), cfg)
            for field, value in (("model", "gpt-5.5"), ("model", ""), ("effort", "high"), ("effort", "")):
                with self.subTest(field=field, value=value):
                    setattr(cfg, field, value)
                    self.assertFalse(C._candidate_cache_valid(cfg, candidates, None))
                    self.assertIsNone(C._load_verdict(finding, cfg))
                    setattr(cfg, field, None)
                    self.assertTrue(C._candidate_cache_valid(cfg, candidates, None))
                    self.assertIsNotNone(C._load_verdict(finding, cfg))

    def test_cache_binds_adapter_environment_tuning(self) -> None:
        finding_data = {"id": "MC-1", "source": "model-checking", "title": "t", "summary": "s"}
        ws = self.seed("T", [finding_data])
        adapter = Path(self.tmp) / "codex.sh"
        adapter.write_text("#!/bin/sh\nexit 0\n")
        cfg = C.ConfirmConfig(name="T", ws=ws, adapter=adapter, worktree=False)
        candidates = ws.work_dir("T") / "spec" / "candidates.json"
        finding = C.Finding(finding_data, ws.work_dir("T") / "confirmation" / "MC-1")
        with (
            mock.patch.dict(os.environ, {"CODEX_MODEL": "model-a", "CODEX_EFFORT": "low"}),
            mock.patch.object(C, "_skill_identity", return_value={"guide": "v1"}),
        ):
            C._write_candidate_cache(cfg, candidates)
            C._save_verdict(C.Outcome(finding, "FALSE POSITIVE", True, 0, EVIDENCE), cfg)
            for name, value in (("CODEX_MODEL", "model-b"), ("CODEX_EFFORT", "high")):
                with self.subTest(name=name):
                    original = os.environ[name]
                    os.environ[name] = value
                    self.assertFalse(C._candidate_cache_valid(cfg, candidates, None))
                    self.assertIsNone(C._load_verdict(finding, cfg))
                    os.environ[name] = original
                    self.assertTrue(C._candidate_cache_valid(cfg, candidates, None))
                    self.assertIsNotNone(C._load_verdict(finding, cfg))

    def test_cached_verdict_revalidates_repro_and_repair_request_artifacts(self) -> None:
        data = {"id": "MC-1", "source": "model-checking", "title": "t", "summary": "s"}
        ws = self.seed("T", [data])
        cfg = self.cfg(ws, "T")
        f = C.Finding(data, ws.work_dir("T") / "confirmation" / "MC-1")
        repro = ws.work_dir("T") / "repro" / "test_bugMC-1_case.py"
        repro.parent.mkdir(parents=True)
        repro.write_text("assert True\n")
        reproduced = C.Outcome(f, "REPRODUCED", True, 0, EVIDENCE)
        C._save_verdict(reproduced, cfg)
        self.assertIsNotNone(C._load_verdict(f, cfg))
        repro.unlink()
        self.assertIsNone(C._load_verdict(f, cfg))

        output = ws.work_dir("T") / "spec" / "output" / "x.out"
        output.parent.mkdir(parents=True)
        output.write_text("trace\n")
        f.fdir.mkdir(parents=True, exist_ok=True)
        (f.fdir / "repair-request.body.md").write_text(TestMergeRR.AGENT_BODY)
        pending = C.Outcome(f, "PENDING REPAIR", True, 0, EVIDENCE, bug_no=1)
        pending.rr = C.allocate_rr(cfg, pending)
        C._save_verdict(pending, cfg)
        self.assertIsNotNone(C._load_verdict(f, cfg))
        rr = ws.work_dir("T") / "spec" / "repair-requests" / f"{pending.rr}.md"
        rr.unlink()
        self.assertIsNone(C._load_verdict(f, cfg))

    def test_standalone_spec_or_counterexample_change_invalidates_verdict(self) -> None:
        data = {
            "id": "MC-1",
            "source": "model-checking",
            "title": "t",
            "summary": "s",
            "counterexample": "spec/output/ce.out",
        }
        ws = self.seed("T", [data])
        spec = ws.work_dir("T") / "spec"
        (spec / "output").mkdir()
        ce = spec / "output" / "ce.out"
        ce.write_text("trace one\n")
        model = spec / "base.tla"
        model.write_text("---- MODULE base ----\n")
        cfg = self.cfg(ws, "T")
        f = C.Finding(data, ws.work_dir("T") / "confirmation" / "MC-1")
        outcome = C.Outcome(f, "FALSE POSITIVE", True, 0, EVIDENCE)
        C._save_verdict(outcome, cfg)
        self.assertIsNotNone(C._load_verdict(f, cfg))
        model.write_text("---- MODULE base ----\nVARIABLE changed\n")
        self.assertIsNone(C._load_verdict(f, cfg))

        model.write_text("---- MODULE base ----\n")
        C._save_verdict(outcome, cfg)
        ce.write_text("trace two\n")
        self.assertIsNone(C._load_verdict(f, cfg))

        target = ce.parent / "real.out"
        target.write_text("symlink target one\n")
        ce.unlink()
        ce.symlink_to(target.name)
        C._save_verdict(outcome, cfg)
        target.write_text("symlink target two\n")
        self.assertIsNone(C._load_verdict(f, cfg))


class TestValidationContracts(ConfirmCase):
    def test_structural_hygiene_still_enforced(self) -> None:
        # Kept (would break the per-finding fan-out): id filesystem-safe + unique,
        # source routable. Everything else was intentionally relaxed.
        p = Path(self.tmp) / "candidates.json"
        p.write_text(json.dumps({"findings": [{"id": "..", "source": "model-checking", "title": "t", "summary": "s"}]}))
        self.assertTrue(any("filesystem-safe" in e for e in C._validate_candidates(p)))
        p.write_text(json.dumps({"findings": [{"id": "F1", "source": "guess", "title": "t", "summary": "s"}]}))
        self.assertTrue(any("source not in" in e for e in C._validate_candidates(p)))
        p.write_text(
            json.dumps(
                {
                    "findings": [
                        {"id": "MC-1", "source": "model-checking", "title": "t", "summary": "s"},
                        {"id": "MC-1", "source": "model-checking", "title": "t", "summary": "s"},
                    ]
                }
            )
        )
        self.assertTrue(any("duplicate id" in e for e in C._validate_candidates(p)))

    def test_completeness_and_cosmetics_relaxed(self) -> None:
        # Relaxed: MC-completeness, one-line title, and MC-/CR- prefixes no longer
        # fail — they only fail-closed a runnable batch without improving a verdict.
        p = Path(self.tmp) / "candidates.json"
        p.write_text(json.dumps({"findings": []}))
        self.assertEqual(C._validate_candidates(p, {"MC-1"}), [])  # missing MC-1: not an error now
        p.write_text(
            json.dumps(
                {"findings": [{"id": "MC-1", "source": "model-checking", "title": "x\ninjected", "summary": "s"}]}
            )
        )
        self.assertEqual(C._validate_candidates(p), [])  # multi-line title accepted

    def test_family_partial_dedup_is_accepted(self) -> None:
        # The exact pattern that failed the 3-model run: a family absorbed into an
        # MC candidate (dedup_note) AND emitted as a distinct-site CR residual is a
        # legitimate consolidation and must NOT be rejected as a contradiction.
        p = Path(self.tmp) / "candidates.json"
        p.write_text(
            json.dumps(
                {
                    "findings": [
                        {
                            "id": "MC-1",
                            "source": "model-checking",
                            "title": "t",
                            "summary": "s",
                            "dedup_note": "also covers Family 2",
                        },
                        {"id": "CR-2", "source": "code-review", "family": "Family 2", "title": "t2", "summary": "s2"},
                    ]
                }
            )
        )
        self.assertEqual(C._validate_candidates(p, {"MC-1"}, {"Family 1", "Family 2"}), [])

    def test_mc_immutability_no_longer_enforced(self) -> None:
        # Relaxed: a changed source field / a missing counterexample no longer fails.
        spec = Path(self.tmp) / "spec"
        spec.mkdir(parents=True)
        source: dict[str, Any] = {
            "id": "MC-1",
            "source": "model-checking",
            "title": "t",
            "summary": "s",
            "counterexample": "spec/output/ce.out",
        }
        candidate = dict(source)
        candidate["counterexample"] = None
        candidate["title"] = "changed"
        path = spec / "candidates.json"
        path.write_text(json.dumps({"findings": [candidate]}))
        self.assertEqual(C._validate_candidates(path, {"MC-1": source}), [])

    def test_nonzero_and_hollow_reproduced_are_incomplete_not_cached(self) -> None:
        # A nonzero adapter exit or a hollow REPRODUCED (no repro artifact) is never
        # persisted as a business verdict: the finding becomes INCOMPLETE (not cached,
        # so a retry re-attempts it) and the target still delivers.
        data = {"id": "MC-1", "source": "model-checking", "title": "t", "summary": "s"}
        for response, rc in (("", 2), ("VERDICT: REPRODUCED", 0)):
            ws = self.seed(f"T{rc}", [data])
            with mock.patch.object(C, "run_agent_blocking", _fake_turn(response, rc=rc)):
                self.assertEqual(C.run_parallel_confirmation(self.cfg(ws, f"T{rc}")), 1)
            verdict = ws.work_dir(f"T{rc}") / "confirmation" / "MC-1" / "verdict.json"
            self.assertFalse(verdict.exists())  # not cached

    def test_rr_id_scans_deferred_and_never_overwrites(self) -> None:
        ws = self.seed("T", [])
        rr_dir = ws.work_dir("T") / "spec" / "repair-requests"
        deferred = rr_dir / "deferred"
        deferred.mkdir(parents=True)
        old = deferred / "RR-007.md"
        old.write_text("old history\n")
        f = self.finding(ws, "T")
        f.fdir.mkdir(parents=True)
        (f.fdir / "repair-request.body.md").write_text(TestMergeRR.AGENT_BODY)
        rid = C.allocate_rr(self.cfg(ws, "T"), C.Outcome(f, "PENDING REPAIR", True, 0, EVIDENCE, bug_no=1))
        self.assertEqual(rid, "RR-008")
        self.assertEqual(old.read_text(), "old history\n")

    def test_changed_repair_body_gets_a_new_allocation(self) -> None:
        ws = self.seed("T", [])
        f = self.finding(ws, "T")
        f.fdir.mkdir(parents=True)
        body_file = f.fdir / "repair-request.body.md"
        body_file.write_text(TestMergeRR.AGENT_BODY)
        cfg = self.cfg(ws, "T")
        outcome = C.Outcome(f, "PENDING REPAIR", True, 0, EVIDENCE, bug_no=1)
        self.assertEqual(C.allocate_rr(cfg, outcome), "RR-001")
        body_file.write_text(TestMergeRR.AGENT_BODY + "\nAdditional corrected evidence changes the request.\n")
        self.assertEqual(C.allocate_rr(cfg, outcome), "RR-002")


class TestEvidenceAndRendering(ConfirmCase):
    def test_debate_preserves_initial_evidence_and_validates_each_turn(self) -> None:
        ws = self.seed("T", [])
        cfg = self.cfg(ws, "T", debate=True, rounds=2)
        texts = iter(
            [
                _response("REPRODUCED", "INITIAL EVIDENCE\n- **Novelty**: KNOWN (fix-status: unfixed)"),
                _response("FALSE POSITIVE", "CHALLENGE EVIDENCE"),
                _response("FALSE POSITIVE", "DEFENSE CONCESSION"),
            ]
        )

        def agent(*_args: object, **_kwargs: object) -> tuple[int, str]:
            repro = ws.work_dir("T") / "repro" / "test_bugMC-1_case.py"
            repro.parent.mkdir(parents=True, exist_ok=True)
            repro.write_text("assert True\n")
            return (0, next(texts))

        with mock.patch.object(C, "run_agent_blocking", agent):
            outcome = C.run_finding(cfg, self.finding(ws, "T"))
        self.assertEqual(outcome.status, "FALSE POSITIVE")
        self.assertIn("INITIAL EVIDENCE", outcome.body)
        self.assertIn("DEFENSE CONCESSION", outcome.body)
        self.assertNotIn("VERDICT:", outcome.body)

    def test_hollow_challenger_cannot_create_consensus(self) -> None:
        ws = self.seed("T", [])
        cfg = self.cfg(ws, "T", debate=True)
        texts = iter([_response("REPRODUCED"), "VERDICT: REPRODUCED"])

        def agent(*_args: object, **_kwargs: object) -> tuple[int, str]:
            repro = ws.work_dir("T") / "repro" / "test_bugMC-1_case.py"
            repro.parent.mkdir(parents=True, exist_ok=True)
            repro.write_text("assert True\n")
            return (0, next(texts))

        with mock.patch.object(C, "run_agent_blocking", agent), self.assertRaises(C.InvalidAgentOutput):
            C.run_finding(cfg, self.finding(ws, "T"))

    def test_final_reproduced_cannot_bypass_repro_validation(self) -> None:
        ws = self.seed("T", [])
        cfg = self.cfg(ws, "T", debate=True)
        texts = iter(
            [
                _response("ENV_LIMITED", "Initial environment limitation."),
                _response("REPRODUCED", "The challenger claims it reproduced."),
                _response("REPRODUCED", "The defender changes the final status."),
            ]
        )
        with (
            mock.patch.object(C, "run_agent_blocking", lambda *_a, **_k: (0, next(texts))),
            self.assertRaises(C.InvalidAgentOutput),
        ):
            C.run_finding(cfg, self.finding(ws, "T"))

    def test_novelty_uses_last_complete_claim(self) -> None:
        body = (
            "- **Novelty**: NEW\ninitial evidence\n"
            "## Debate addendum\n- **Novelty**: KNOWN (cite: issue-1; fix-status: fixed)"
        )
        self.assertEqual(C._novelty(body), "KNOWN-fixed")

    def test_report_strips_nested_verdict_and_escapes_bug_heading(self) -> None:
        ws = self.seed("T", [])
        f = self.finding(ws, "T")
        C.aggregate(
            self.cfg(ws, "T"),
            [C.Outcome(f, "NEEDS MORE INFO", False, 0, "## Bug 99: injected\nVERDICT: REPRODUCED\nevidence")],
        )
        report = (ws.work_dir("T") / "spec" / "confirmed-bugs.md").read_text()
        self.assertEqual(len(re.findall(r"^## Bug \d+:", report, re.MULTILINE)), 1)
        self.assertNotIn("VERDICT:", report)
        self.assertIn("- **Debate**: not run", report)

    def test_renderer_does_not_expand_placeholders_inside_values(self) -> None:
        root = Path(self.tmp) / "prompts"
        root.mkdir()
        (root / "test.md").write_text("A={{a}}; B={{b}}")
        with mock.patch.object(P, "PROMPTS_DIR", root):
            self.assertEqual(P.render("test", a="{{b}}", b="expanded"), "A={{b}}; B=expanded")


class TestRepoIsolation(ConfirmCase):
    def _repo(self) -> Path:
        repo = Path(self.tmp) / "repo"
        repo.mkdir()
        subprocess.run(["git", "init", "-q", str(repo)], check=True)
        (repo / "tracked.txt").write_text("base\n")
        (repo / "delete-me.txt").write_text("delete me\n")
        subprocess.run(["git", "-C", str(repo), "add", "tracked.txt", "delete-me.txt"], check=True)
        subprocess.run(
            [
                "git",
                "-C",
                str(repo),
                "-c",
                "user.name=Test",
                "-c",
                "user.email=test@example.com",
                "commit",
                "-qm",
                "initial",
            ],
            check=True,
        )
        return repo

    def _repo_cfg(self, repo: Path, *, worktree: bool) -> tuple[C.ConfirmConfig, mock.Mock]:
        ws = mock.Mock()
        ws.work_dir.return_value = repo / ".specula-output"
        cfg = C.ConfirmConfig(name="T", ws=ws, adapter=Path("/x"), repo_dir=str(repo), worktree=worktree)
        return cfg, ws

    def test_dispatcher_output_does_not_make_clean_repo_dirty(self) -> None:
        repo = self._repo()
        cfg, ws = self._repo_cfg(repo, worktree=True)
        fdir = ws.work_dir("T") / "confirmation" / "MC-1"
        fdir.mkdir(parents=True)
        (ws.work_dir("T") / "own-output.log").write_text("dispatcher output\n")
        f = C.Finding({"id": "MC-1", "source": "model-checking"}, fdir)
        path, cleanup = C.setup_repo(cfg, f)
        try:
            self.assertTrue((Path(path) / "tracked.txt").is_file())
        finally:
            cleanup()

    def test_local_cache_ignores_own_output_but_hashes_untracked_contents(self) -> None:
        repo = self._repo()
        cfg, ws = self._repo_cfg(repo, worktree=False)
        output = ws.work_dir("T")
        output.mkdir()
        (output / "log").write_text("one")
        first = C._repo_cache_identity(cfg)
        (output / "log").write_text("two")
        self.assertEqual(first, C._repo_cache_identity(cfg))

        untracked = repo / "scratch.txt"
        untracked.write_text("alpha")
        alpha = C._repo_cache_identity(cfg)
        untracked.write_text("beta")
        self.assertNotEqual(alpha, C._repo_cache_identity(cfg))

    def test_pipeline_instrumentation_is_copied_into_isolated_worktree(self) -> None:
        repo = self._repo()
        cfg, ws = self._repo_cfg(repo, worktree=True)
        (repo / "tracked.txt").write_text("instrumented tracked bytes\n")
        (repo / "harness.py").write_text("instrumented untracked bytes\n")
        (repo / "delete-me.txt").unlink()
        f = C.Finding({"id": "MC-1", "source": "model-checking"}, ws.work_dir("T") / "confirmation" / "MC-1")
        path, cleanup = C.setup_repo(cfg, f)
        try:
            self.assertEqual((Path(path) / "tracked.txt").read_text(), "instrumented tracked bytes\n")
            self.assertEqual((Path(path) / "harness.py").read_text(), "instrumented untracked bytes\n")
            self.assertFalse((Path(path) / "delete-me.txt").exists())
            (Path(path) / "tracked.txt").write_text("finding one mutation\n")

            f2 = C.Finding({"id": "MC-2", "source": "model-checking"}, ws.work_dir("T") / "confirmation" / "MC-2")
            path2, cleanup2 = C.setup_repo(cfg, f2)
            try:
                self.assertEqual((Path(path2) / "tracked.txt").read_text(), "instrumented tracked bytes\n")
                self.assertEqual((repo / "tracked.txt").read_text(), "instrumented tracked bytes\n")
            finally:
                cleanup2()
        finally:
            cleanup()

    def test_worktree_cache_misses_after_tracked_or_untracked_change(self) -> None:
        repo = self._repo()
        cfg, ws = self._repo_cfg(repo, worktree=True)
        f = C.Finding({"id": "MC-1", "source": "model-checking"}, ws.work_dir("T") / "confirmation" / "MC-1")
        C._save_verdict(C.Outcome(f, "FALSE POSITIVE", True, 0, EVIDENCE), cfg)
        self.assertIsNotNone(C._load_verdict(f, cfg))

        (repo / "tracked.txt").write_text("changed\n")
        self.assertIsNone(C._load_verdict(f, cfg))
        (repo / "tracked.txt").write_text("base\n")
        (repo / "untracked.txt").write_text("new\n")
        self.assertIsNone(C._load_verdict(f, cfg))

    def test_repo_change_prevents_reusing_open_repair_allocation(self) -> None:
        repo = self._repo()
        cfg, ws = self._repo_cfg(repo, worktree=False)
        f = C.Finding({"id": "MC-1", "source": "model-checking"}, ws.work_dir("T") / "confirmation" / "MC-1")
        f.fdir.mkdir(parents=True)
        (f.fdir / "repair-request.body.md").write_text(TestMergeRR.AGENT_BODY)
        outcome = C.Outcome(f, "PENDING REPAIR", True, 0, EVIDENCE, bug_no=1)
        self.assertEqual(C.allocate_rr(cfg, outcome), "RR-001")
        (repo / "tracked.txt").write_text("new source bytes\n")
        self.assertEqual(C.allocate_rr(cfg, outcome), "RR-002")

    def test_cleanup_failure_does_not_replace_active_rate_limit(self) -> None:
        repo = self._repo()
        cfg, ws = self._repo_cfg(repo, worktree=True)
        f = C.Finding({"id": "MC-1", "source": "model-checking"}, ws.work_dir("T") / "confirmation" / "MC-1")
        _path, cleanup = C.setup_repo(cfg, f)
        try:
            with self.assertRaises(C.RateLimited):
                try:
                    raise C.RateLimited("quota")
                finally:
                    failed_remove = mock.Mock(returncode=1, stderr="remove failed")
                    with mock.patch("specula.confirmlib.subprocess.run", return_value=failed_remove):
                        cleanup()
        finally:
            subprocess.run(["git", "-C", str(repo), "worktree", "remove", "--force", str(f.fdir / "worktree")])

    def test_stale_registered_worktree_is_recovered(self) -> None:
        repo = self._repo()
        cfg, ws = self._repo_cfg(repo, worktree=True)
        f = C.Finding({"id": "MC-1", "source": "model-checking"}, ws.work_dir("T") / "confirmation" / "MC-1")
        first_path, _abandoned_cleanup = C.setup_repo(cfg, f)
        self.assertTrue(Path(first_path).is_dir())
        shutil.rmtree(first_path)  # simulate SIGKILL plus a partially cleaned directory
        second_path, cleanup = C.setup_repo(cfg, f)
        try:
            self.assertEqual(second_path, first_path)
            self.assertTrue((Path(second_path) / "tracked.txt").is_file())
        finally:
            cleanup()


if __name__ == "__main__":
    unittest.main()
