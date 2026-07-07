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
from pathlib import Path
from typing import Any
from unittest import mock

from specula import confirmlib as C
from specula.phaselib import Workspace


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


if __name__ == "__main__":
    unittest.main()
