"""Bug verdicts survive real CLI/event plumbing; adapters supply fixture evidence."""

from __future__ import annotations

import json
import os
import shlex
import unittest
from pathlib import Path
from unittest import mock

import test_github_ci as fixtures
import test_incremental_ci as incremental_fixtures

from specula.ci_store import CIStore


class InitializationVerdict(unittest.TestCase):
    def test_initialization_with_confirmed_bugs_publishes_baseline_and_exits_red(self) -> None:
        fixture = incremental_fixtures.IncrementalCLI()
        fixture.setUp()
        self.addCleanup(fixture.doCleanups)
        # Supply a final confirmation report and its matching summary through
        # the fixture adapter. This tests finalization, not bug discovery.
        report = (
            "# Fixture confirmation\n\n"
            "| Entry | Finding | Status | Counts as final bug? |\n|---|---|---|---|\n"
            "| 1 | MC-1 | ENV_LIMITED | no |\n\n"
            "## Entry 1: Fixture\n\n- **Finding ID**: MC-1\n- **Status**: ENV_LIMITED\n"
        )
        summary = (
            "One fixture finding.\n\n## Findings\n\n"
            "- **MC-1: Fixture** — Status: ENV_LIMITED. Fixture evidence only.\n\n"
            "## Validation limits\n\nNo real verification performed.\n"
        )
        helper = fixture.adapter.with_suffix(".init-verdict.py")
        helper.write_text(
            "import sys\nfrom pathlib import Path\nwork=Path(sys.argv[1])\n"
            f"(work/'confirmed-bugs.md').write_text({report!r})\n"
            f"(work/'.summary-findings.md').write_text({summary!r})\n"
        )
        script = fixture.adapter.read_text().replace(
            "esac\n",
            "esac\n"
            'if [ "$SPECULA_PHASE" = bug_classification ]; then\n'
            f'  python3 {shlex.quote(str(helper))} "$SPECULA_WORK_DIR"\n'
            "fi\n",
        )
        fixture.adapter.write_text(script)
        result = fixture.run_ci("--ci-init", "--agent=fake", f"--artifact={fixture.source}", "footest")
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        self.assertEqual(CIStore(fixture.ci).current()["verdict"], "FAIL")
        self.assertTrue((fixture.ci / "current/model/spec/base.tla").is_file())
        self.assertTrue(json.loads((fixture.latest() / "ci-result.json").read_text())["complete"])


class BugVerdictEvents(unittest.TestCase):
    def setUp(self) -> None:
        self.events = fixtures.GitHubEvents()
        self.events.setUp()
        self.addCleanup(self.events.doCleanups)
        self.fixture = self.events.fixture
        self.ci = self.fixture.ci

    def test_red_push_and_repeated_events_preserve_failure_and_published_model(self) -> None:
        before = (self.ci / "current").resolve()
        self.fixture.change_source("bug fixture\n")
        self.fixture.finding_status("REPRODUCED")
        result, reports = self.events.push()
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        baseline = (self.ci / "current").resolve()
        self.assertNotEqual(before, baseline)
        self.assertEqual(CIStore(self.ci).current()["verdict"], "FAIL")
        self.assertIn("| FAIL |", (reports / "summary.md").read_text())
        self.assertTrue(list(reports.glob("*/ci-verdict.json")))
        for kind in ("schedule", "workflow_dispatch"):
            result, reports = self.events.event(kind, {})
            self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
            self.assertIn("| FAIL |", (reports / "summary.md").read_text())
        result, _ = self.events.push()
        self.assertEqual(result.returncode, 2)
        self.assertEqual(self.events.calls(), 1)
        self.assertEqual((self.ci / "current").resolve(), baseline)

        # A new source version reruns confirmation. Its fix can turn CI green.
        self.fixture.change_source("fixed fixture\n")
        self.fixture.finding_status("FIXED")
        result, reports = self.events.push()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(self.events.calls(), 2)
        self.assertIn("| PASS |", (reports / "summary.md").read_text())
        self.assertIn("-bug fixture\n+fixed fixture", (self.fixture.latest() / "source.diff").read_text())

    def test_red_candidate_survives_duplicate_queue_and_squash_inheritance(self) -> None:
        self.events.prepare_pr()
        self.fixture.finding_status("ENV_LIMITED")
        baseline = (self.ci / "current").resolve()
        for _ in range(2):
            result, reports = self.events.open_pr()
            self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
            self.assertIn("| FAIL |", (reports / "summary.md").read_text())
        self.assertEqual(self.events.calls(), 1)
        self.assertEqual((self.ci / "current").resolve(), baseline)
        base = self.fixture.git("rev-parse", "trunk")
        head = self.fixture.git("rev-parse", "feature")
        group = self.fixture.git("commit-tree", f"{head}^{{tree}}", "-p", base, "-p", head, "-m", "merge group")
        self.fixture.git("update-ref", "refs/heads/queue", group)
        result, reports = self.events.event(
            "merge_group",
            {"action": "checks_requested", "merge_group": {"base_ref": "refs/heads/trunk", "head_sha": group}},
        )
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        self.assertIn("reused candidate result", (reports / "summary.md").read_text())
        merged = self.events.squash()
        result, reports = self.events.push()
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        self.assertEqual(self.events.calls(), 1)
        self.assertEqual(CIStore(self.ci).current()["source_commit"], merged)
        self.assertEqual(CIStore(self.ci).current()["verdict"], "FAIL")
        self.assertIn("inherited PR result", (reports / "summary.md").read_text())

    def test_masked_findings_are_visible_nonblocking_warnings(self) -> None:
        self.fixture.change_source("masked fixture\n")
        self.fixture.finding_status("MASKED")
        with mock.patch.dict(os.environ, {"GITHUB_ACTIONS": "true"}):
            for _ in range(2):
                result, reports = self.events.push()
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertIn("::warning::", result.stdout)
                self.assertIn("| WARNING |", (reports / "summary.md").read_text())
        self.assertEqual(self.events.calls(), 1)

    def test_resuming_an_interrupted_check_can_finish_red_and_be_reused_red(self) -> None:
        self.fixture.change_source("bug fixture\n")
        fail = Path(f"{self.fixture.adapter}.fail")
        fail.touch()
        result, _ = self.events.push()
        self.assertNotEqual(result.returncode, 0)
        run = self.fixture.latest()
        fail.unlink()
        self.fixture.finding_status("REPRODUCED")
        result = self.fixture.run_ci(f"--run-id={run.name}")
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        receipt = json.loads((run / "ci-result.json").read_text())
        self.assertTrue(receipt["complete"])
        result, reports = self.events.push()
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        self.assertEqual(self.events.calls(), 2)
        self.assertIn("reused current result", (reports / "summary.md").read_text())

    def test_legacy_completion_without_a_verdict_requires_a_fresh_check(self) -> None:
        self.fixture.change_source("fixture update\n")
        result, _ = self.events.push()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        state_path = self.ci / "current/state.json"
        state = json.loads(state_path.read_text())
        del state["verdict"]
        state_path.write_text(json.dumps(state))
        for path in (self.ci / ".github-ci/attempts").glob("*.json"):
            attempt = json.loads(path.read_text())
            del attempt["verdict"]
            path.write_text(json.dumps(attempt))
        self.fixture.finding_status("REPRODUCED")
        result, reports = self.events.push()
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        self.assertEqual(self.events.calls(), 2)
        self.assertIn("| FAIL |", (reports / "summary.md").read_text())

    def test_delayed_event_does_not_turn_a_red_cumulative_check_green(self) -> None:
        self.fixture.change_source("earlier fixture\n")
        earlier = self.fixture.git("rev-parse", "HEAD")
        self.fixture.change_source("later fixture\n")
        self.fixture.finding_status("REPRODUCED")
        result, _ = self.events.push()
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        result, reports = self.events.push(earlier)
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        self.assertIn("no separate check", (reports / "summary.md").read_text())
        self.assertIn("| FAIL |", (reports / "summary.md").read_text())
        self.assertEqual(self.events.calls(), 1)
