"""Real event-to-CLI wiring with fixture Agent calls; no LLM or TLC execution."""

from __future__ import annotations

import json
import os
import secrets
import subprocess
import sys
import unittest
from pathlib import Path
from typing import Any

import test_cli_pipeline as base_fixtures
import test_incremental_ci as incremental_fixtures

from specula.ci_store import CIStore


class GitHubEvents(unittest.TestCase):
    def setUp(self) -> None:
        self.fixture = incremental_fixtures.IncrementalCLI()
        self.fixture.setUp()
        self.addCleanup(self.fixture.helper.doCleanups)
        self.root = self.fixture.root
        self.ci = self.fixture.ci
        self.source = self.fixture.source
        self.fixture.git("branch", "-M", "trunk")
        self.fixture.initialize()
        self.bin = self.fixture.work / "bin"
        self.bin.mkdir()
        self.gh = self.bin / "gh"
        self.gh.write_text('#!/bin/sh\ncat "$0.response"\n')
        self.gh.chmod(0o755)
        Path(str(self.gh) + ".response").write_text("")

    def calls(self) -> int:
        return Path(str(self.fixture.adapter) + ".phases").read_text().splitlines().count("incremental")

    def event(
        self, name: str, payload: dict[str, Any], *options: str, model: str = "fixture-model"
    ) -> tuple[subprocess.CompletedProcess[str], Path]:
        request = self.fixture.work / f"event-{secrets.token_hex(4)}.json"
        request.write_text(json.dumps({"repository": {"full_name": "example/project"}, **payload}))
        reports = self.fixture.work / f"reports-{secrets.token_hex(4)}"
        environment = {
            key: value
            for key, value in os.environ.items()
            if key not in base_fixtures._VOLATILE
            and key
            not in {"SPECULA_CI_RECEIPT", "SPECULA_CI_BORROW_LEASE", "SPECULA_CI_EVENT_LOCK_FD", "SPECULA_CI_LOCK_FD"}
        }
        environment.update(
            {
                "GITHUB_REPOSITORY": "example/project",
                "GITHUB_EVENT_NAME": name,
                "GITHUB_EVENT_PATH": str(request),
                "GITHUB_REF": "refs/heads/trunk",
                "GITHUB_SHA": self.fixture.git("rev-parse", "HEAD"),
                "HOME": str(self.fixture.work),
            }
        )
        environment["PATH"] = str(self.bin) + os.pathsep + environment.get("PATH", "")
        result = subprocess.run(
            [
                sys.executable,
                str(self.root / "src/specula/cli.py"),
                "ci",
                f"--ci-dir={self.ci}",
                f"--artifact={self.source}",
                f"--reports-dir={reports}",
                "--agent=fake",
                f"--model={model}",
                "--effort=high",
                *options,
            ],
            env=environment,
            cwd=self.fixture.work,
            capture_output=True,
            text=True,
            timeout=90,
        )
        return result, reports

    def push(self, target: str | None = None, **kwargs: Any) -> tuple[subprocess.CompletedProcess[str], Path]:
        return self.event(
            "push", {"ref": "refs/heads/trunk", "after": target or self.fixture.git("rev-parse", "HEAD")}, **kwargs
        )

    def open_pr(self, **kwargs: Any) -> tuple[subprocess.CompletedProcess[str], Path]:
        head = self.fixture.git("rev-parse", "feature")
        return self.event(
            "pull_request_target",
            {
                "number": 7,
                "action": "synchronize",
                "pull_request": {
                    "head": {"sha": head, "repo": {"full_name": "example/project"}},
                    "base": {"ref": "trunk", "sha": self.fixture.git("rev-parse", "trunk")},
                },
            },
            **kwargs,
        )

    def prepare_pr(self) -> None:
        self.fixture.git("checkout", "-qb", "feature")
        self.fixture.change_source("PR change\n")
        self.fixture.git("checkout", "-q", "trunk")

    def squash(self) -> str:
        self.fixture.git("merge", "--squash", "feature")
        self.fixture.git("commit", "-qm", "Squashed feature")
        return self.fixture.git("rev-parse", "HEAD")

    def test_pr_result_is_inherited_after_squash_without_another_agent(self) -> None:
        self.prepare_pr()
        previous = (self.ci / "current").resolve()
        checked, _ = self.open_pr()
        self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
        self.assertEqual(self.calls(), 1)
        self.assertEqual((self.ci / "current").resolve(), previous)
        merged = self.squash()
        pushed, reports = self.push()
        self.assertEqual(pushed.returncode, 0, pushed.stdout + pushed.stderr)
        self.assertEqual(self.calls(), 1)
        self.assertEqual(CIStore(self.ci).current()["source_commit"], merged)
        self.assertIn("inherited PR result", (reports / "summary.md").read_text())
        self.assertTrue(list(reports.glob("*/summary.md")))
        self.assertFalse(list(reports.rglob("*.resume.json")))

    def test_changed_merge_content_requires_new_checks(self) -> None:
        self.prepare_pr()
        checked, _ = self.open_pr()
        self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
        (self.source / "another-module.txt").write_text("new context\n")
        self.fixture.commit("other mainline update")
        self.squash()
        pushed, reports = self.push()
        self.assertEqual(pushed.returncode, 0, pushed.stdout + pushed.stderr)
        self.assertEqual(self.calls(), 3)
        self.assertNotIn("inherited PR result", (reports / "summary.md").read_text())

    def test_changed_configuration_does_not_reuse_pr_result(self) -> None:
        self.prepare_pr()
        checked, _ = self.open_pr()
        self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
        self.squash()
        pushed, _ = self.push(model="different-model")
        self.assertEqual(pushed.returncode, 0, pushed.stdout + pushed.stderr)
        self.assertEqual(self.calls(), 2)

    def test_multi_commit_rebase_merge_inherits_the_final_pr_model(self) -> None:
        base = self.fixture.git("rev-parse", "trunk")
        self.fixture.git("checkout", "-qb", "feature")
        self.fixture.change_source("first PR commit\n")
        first = self.fixture.git("rev-parse", "HEAD")
        self.fixture.change_source("second PR commit\n")
        second = self.fixture.git("rev-parse", "HEAD")
        self.fixture.git("checkout", "-q", "trunk")
        result, _ = self.open_pr()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        rebased_first = self.fixture.git("commit-tree", f"{first}^{{tree}}", "-p", base, "-m", "rebased first")
        rebased_second = self.fixture.git(
            "commit-tree", f"{second}^{{tree}}", "-p", rebased_first, "-m", "rebased second"
        )
        self.fixture.git("update-ref", "refs/heads/trunk", rebased_second)
        self.fixture.git("checkout", "-q", "--detach", rebased_second)
        Path(str(self.gh) + ".response").write_text(
            json.dumps({"merged_at": "2026-09-06", "merge_commit_sha": rebased_second, "branch": "trunk"}) + "\n"
        )
        result, reports = self.event("push", {"ref": "refs/heads/trunk", "before": base, "after": rebased_second})
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(self.calls(), 1)
        self.assertEqual(CIStore(self.ci).current()["source_commit"], rebased_second)
        self.assertIn("intermediate commits were not separately checked", (reports / "summary.md").read_text())

    def test_duplicate_pr_event_reuses_the_same_checked_tree(self) -> None:
        self.prepare_pr()
        for _ in range(2):
            result, _ = self.open_pr()
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(self.calls(), 1)

    def test_merge_queue_reuses_a_matching_pr_candidate(self) -> None:
        self.prepare_pr()
        result, _ = self.open_pr()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        base = self.fixture.git("rev-parse", "trunk")
        head = self.fixture.git("rev-parse", "feature")
        group = self.fixture.git("commit-tree", f"{head}^{{tree}}", "-p", base, "-p", head, "-m", "merge group")
        self.fixture.git("update-ref", "refs/heads/queue", group)
        result, reports = self.event(
            "merge_group",
            {"action": "checks_requested", "merge_group": {"base_ref": "refs/heads/trunk", "head_sha": group}},
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(self.calls(), 1)
        self.assertIn("reused candidate result", (reports / "summary.md").read_text())

    def test_pr_check_restores_the_canonical_branch_checkout(self) -> None:
        self.prepare_pr()
        result, _ = self.open_pr()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        source = self.ci / ".github-ci/source"
        actual = subprocess.run(
            ["git", "-C", str(source), "rev-parse", "HEAD"], check=True, capture_output=True, text=True
        ).stdout.strip()
        self.assertEqual(actual, self.fixture.git("rev-parse", "trunk"))

    def test_push_covers_all_new_mainline_commits_and_old_events_do_not_regress(self) -> None:
        self.fixture.change_source("B\n")
        earlier = self.fixture.git("rev-parse", "HEAD")
        self.fixture.change_source("C\n")
        latest = self.fixture.git("rev-parse", "HEAD")
        result, _ = self.push()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(self.calls(), 2)
        for target in (latest, earlier):
            result, _ = self.push(target)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(self.calls(), 2)
        self.assertEqual(CIStore(self.ci).current()["source_commit"], latest)

    def test_failure_is_not_retried_by_schedule_but_manual_force_can_rerun(self) -> None:
        self.fixture.change_source("B\n")
        previous = (self.ci / "current").resolve()
        fail = Path(str(self.fixture.adapter) + ".fail")
        fail.touch()
        result, _ = self.push()
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual((self.ci / "current").resolve(), previous)
        fail.unlink()
        for name, payload in (
            ("push", {"ref": "refs/heads/trunk", "after": self.fixture.git("rev-parse", "HEAD")}),
            ("schedule", {}),
        ):
            result, _ = self.event(name, payload)
            self.assertNotEqual(result.returncode, 0)
        self.assertEqual(self.calls(), 1)
        result, _ = self.event("workflow_dispatch", {}, "--force")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(self.calls(), 2)

    def test_external_fork_is_skipped_without_running_or_changing_ci_state(self) -> None:
        before = set(self.ci.iterdir())
        result, reports = self.event(
            "pull_request_target",
            {
                "number": 9,
                "action": "opened",
                "pull_request": {
                    "head": {"sha": "a" * 40, "repo": {"full_name": "external/project"}},
                    "base": {"ref": "trunk"},
                },
            },
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(self.calls(), 0)
        self.assertEqual(set(self.ci.iterdir()), before)
        self.assertTrue((reports / "summary.md").is_file())

    def test_schedule_and_manual_dispatch_reuse_completed_current_result(self) -> None:
        self.fixture.change_source("B\n")
        for name in ("schedule", "workflow_dispatch", "schedule"):
            result, _ = self.event(name, {})
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(self.calls(), 1)

    def test_manual_revision_selects_a_specific_new_commit(self) -> None:
        self.fixture.change_source("B\n")
        selected = self.fixture.git("rev-parse", "HEAD")
        self.fixture.change_source("C\n")
        result, _ = self.event("workflow_dispatch", {}, f"--revision={selected}")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(CIStore(self.ci).current()["source_commit"], selected)
