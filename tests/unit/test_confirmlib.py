"""Unit tests for parallel per-finding bug confirmation (src/specula/confirmlib.py).

Run in-process: agent turns are monkeypatched (no adapter spawn, no network), so
these pin the dispatcher's control flow that the phase/pipeline tests don't reach
— verdict parsing, the debate gate, the RR lifecycle merge, candidate validation,
the rate-limit withhold, and idempotent retry.

    uv run python -m unittest tests.unit.test_confirmlib -v
"""

from __future__ import annotations

import json
import os
import shutil
import tempfile
import unittest
from collections.abc import Callable
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from typing import Any
from unittest import mock

from specula import confirmlib as C
from specula.phaselib import Workspace
from specula.skill_refs import CODEX_PLUGIN_NAME


def _fake_turn(text: str, rc: int = 0) -> Callable[..., tuple[int, str]]:
    """A run_agent_blocking replacement that returns a fixed (rc, text)."""

    def _f(*_args: object, **_kwargs: object) -> tuple[int, str]:
        return (rc, text)

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
        "---\n\n## Trigger\nx\n"
    )

    def test_agent_scope_preserved_lifecycle_stamped(self) -> None:
        out = C._merge_rr("RR-001", "MC-1", "fallback.out", self.AGENT_BODY)
        self.assertIn("id: RR-001", out)
        self.assertIn("status: OPEN", out)
        self.assertIn("round: 0", out)
        self.assertIn("actions: [Foo]", out)  # agent scope verbatim
        self.assertIn("hunt_cfgs: [MC_hunt.cfg]", out)

    def test_agent_lifecycle_fields_overridden(self) -> None:
        sneaky = self.AGENT_BODY.replace("target: SPEC_REPAIR", "id: RR-999\nstatus: RESOLVED\ntarget: SPEC_REPAIR")
        out = C._merge_rr("RR-002", "MC-1", "fb", sneaky)
        self.assertIn("id: RR-002", out)
        self.assertNotIn("RR-999", out)
        self.assertNotIn("RESOLVED", out)

    def test_fallback_when_no_frontmatter(self) -> None:
        out = C._merge_rr("RR-003", "MC-1", "spec/output/x.out", "## Trigger\nprose only\n")
        self.assertIn("id: RR-003", out)
        self.assertIn("counterexample: spec/output/x.out", out)  # injected from fallback
        self.assertIn("scope:", out)  # honest empty stub
        self.assertIn("prose only", out)


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

    def test_success_writes_confirmed_bugs(self) -> None:
        ws = self.seed("T", [{"id": "MC-1", "source": "model-checking", "title": "t", "summary": "s"}])
        with mock.patch.object(C, "run_agent_blocking", _fake_turn("VERDICT: FALSE POSITIVE")):
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

    def test_rate_limit_withholds_deliverable(self) -> None:
        ws = self.seed("T", [{"id": "MC-1", "source": "model-checking", "title": "t", "summary": "s"}])
        with mock.patch.object(C, "run_agent_blocking", _fake_turn("", rc=75)):
            rc = C.run_parallel_confirmation(self.cfg(ws, "T"))
        self.assertEqual(rc, 0)  # batch-phase consistent: no special exit code
        self.assertFalse((ws.work_dir("T") / "spec" / "confirmed-bugs.md").is_file())  # deliverable withheld
        self.assertFalse((ws.work_dir("T") / "confirmation" / "MC-1" / "verdict.json").is_file())  # not cached

    def test_idempotent_skip_on_retry(self) -> None:
        ws = self.seed("T", [{"id": "MC-1", "source": "model-checking", "title": "t", "summary": "s"}])
        with mock.patch.object(C, "run_agent_blocking", _fake_turn("VERDICT: FALSE POSITIVE")):
            C.run_parallel_confirmation(self.cfg(ws, "T"))
        # Second run: a cached terminal verdict must short-circuit — no agent call.
        with mock.patch.object(C, "run_agent_blocking", _boom):
            rc = C.run_parallel_confirmation(self.cfg(ws, "T"))
        self.assertEqual(rc, 0)

    def test_rate_limit_removes_stale_report(self) -> None:
        # A prior run's confirmed-bugs.md must NOT survive a rate limit — else the
        # 4b gate would pass on the stale report. Withhold = remove it.
        ws = self.seed("T", [{"id": "MC-1", "source": "model-checking", "title": "t", "summary": "s"}])
        stale = ws.work_dir("T") / "spec" / "confirmed-bugs.md"
        stale.write_text("# STALE REPORT from a prior run\n")
        with mock.patch.object(C, "run_agent_blocking", _fake_turn("", rc=75)):
            rc = C.run_parallel_confirmation(self.cfg(ws, "T"))
        self.assertEqual(rc, 0)
        self.assertFalse(stale.is_file())  # removed → 4b gate sees MISSING and retries

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
        self.assertIn("$validation-workflow", prompts[0])
        self.assertIn(f"${CODEX_PLUGIN_NAME}:validation-workflow", prompts[0])
        self.assertIn("explicitly invoke exactly one ID listed in your Skills", prompts[0])
        self.assertNotIn("/skills/", prompts[0])
        self.assertNotIn(".claude/skills", prompts[0])

    def test_consolidate_failure_withholds_not_raises(self) -> None:
        # No candidates.json → consolidate runs the agent. A non-75 failure that
        # yields no valid candidates.json must withhold + return 0 (batch-phase
        # consistent), NOT raise (which the scheduler's log-probe cannot retry).
        ws = Workspace(["T"])
        (ws.work_dir("T") / "spec").mkdir(parents=True, exist_ok=True)
        (ws.work_dir("T") / "spec" / "confirmed-bugs.md").write_text("# stale\n")
        with mock.patch.object(C, "run_agent_blocking", _fake_turn("", rc=1)):
            rc = C.run_parallel_confirmation(self.cfg(ws, "T"))
        self.assertEqual(rc, 0)
        self.assertFalse((ws.work_dir("T") / "spec" / "confirmed-bugs.md").is_file())  # stale removed too


class TestAggregate(ConfirmCase):
    def _confirmed_bugs(self, body: str, name: str = "T") -> str:
        ws = self.seed(name, [{"id": "MC-1", "source": "model-checking", "title": "the bug", "summary": "s"}])
        with mock.patch.object(C, "run_agent_blocking", _fake_turn(body)):
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
        self.assertIn("Reproduced: 1 = 0 NEW + 1 KNOWN-unfixed", cb)

    def test_novelty_known_fixed_flagged_separately(self) -> None:
        cb = self._confirmed_bugs("- **Novelty**: KNOWN (cite: http://x; fix-status: fixed)\nVERDICT: REPRODUCED")
        self.assertIn("0 NEW + 0 KNOWN-unfixed", cb)
        self.assertIn("KNOWN-fixed: 1", cb)

    def test_missing_novelty_defaults_new(self) -> None:
        cb = self._confirmed_bugs("VERDICT: REPRODUCED")
        self.assertIn("Reproduced: 1 = 1 NEW + 0 KNOWN-unfixed", cb)


class TestPromptExtraAndLog(ConfirmCase):
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
        self.assertIn("$bug-confirmation", prompt)
        self.assertIn(f"${CODEX_PLUGIN_NAME}:bug-confirmation", prompt)
        self.assertIn("explicitly invoke exactly one ID listed in your Skills", prompt)
        self.assertNotIn("/skills/", prompt)
        self.assertNotIn(".claude/skills", prompt)

    def test_bug_confirmation_log_written_and_global_reset(self) -> None:
        ws = self.seed("T", [{"id": "MC-1", "source": "model-checking", "title": "t", "summary": "s"}])
        with mock.patch.object(C, "run_agent_blocking", _fake_turn("VERDICT: FALSE POSITIVE")):
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
        (f.fdir / "repair-request.body.md").write_text("---\ntarget: SPEC_REPAIR\n---\n\n## Trigger\nx\n")
        o = C.Outcome(f, "PENDING REPAIR", True, 0, "body", bug_no=3)
        rid = C.allocate_rr(self.cfg(ws, "T"), o)
        rr = (ws.work_dir("T") / "spec" / "repair-requests" / f"{rid}.md").read_text()
        self.assertIn("bug_id: Bug 3", rr)  # points at the "## Bug 3:" heading, not MC-1


if __name__ == "__main__":
    unittest.main()
