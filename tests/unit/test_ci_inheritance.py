"""Candidate inheritance and event safety without invoking an Agent."""

from __future__ import annotations

import shutil
import unittest
from pathlib import Path

import test_ci_store as fixtures

from specula.ci_inheritance import inherit, register_candidate
from specula.ci_store import CIError, git
from specula.github_ci import Event, GitHubCI


class InheritanceTests(unittest.TestCase):
    def setUp(self) -> None:
        self.fixture = fixtures.StoreTests()
        self.fixture.setUp()
        self.addCleanup(self.fixture.doCleanups)
        self.store = self.fixture.store
        self.store.publish(self.fixture.run_dir, self.fixture.work, self.fixture.inputs)
        self.initial = self.store.current_token()
        self.candidate_run = self.fixture.root / "runs/candidate"
        self.candidate_work = self.candidate_run / "project/.specula-output"
        self.candidate_source = self.candidate_run / "ci-source"
        shutil.copytree(self.fixture.work, self.candidate_work)
        shutil.copytree(self.fixture.source, self.candidate_source)
        (self.candidate_source / "code").write_text("updated source\n")
        git(self.candidate_source, "add", ".")
        git(self.candidate_source, "commit", "--quiet", "-m", "candidate")
        candidate_commit = git(self.candidate_source, "rev-parse", "HEAD")
        self.inputs = {
            **self.fixture.inputs,
            "previous": self.initial,
            "source": "runs/candidate/ci-source",
            "source_commit": candidate_commit,
            "snapshot_commit": candidate_commit,
            "check_key": "a" * 64,
        }
        candidate = self.store.publish(self.candidate_run, self.candidate_work, self.inputs, advance=False)
        self.token = candidate.relative_to(self.fixture.root).as_posix()
        register_candidate(self.store, self.token)
        self.merged = self.fixture.root / "merged"
        shutil.copytree(self.candidate_source, self.merged)
        original_commit = self.fixture.inputs["source_commit"]
        assert isinstance(original_commit, str)
        self.merge_commit = git(
            self.merged,
            "commit-tree",
            f"{candidate_commit}^{{tree}}",
            "-p",
            original_commit,
            "-m",
            "squash result",
        )
        git(self.merged, "checkout", "--quiet", "--detach", self.merge_commit)

    def test_candidate_is_read_only_until_matching_merge(self) -> None:
        self.assertEqual(self.store.current_token(), self.initial)
        self.assertNotEqual(self.merge_commit, self.inputs["source_commit"])
        inherited = inherit(self.store, self.merged, self.merge_commit, "a" * 64)
        assert inherited is not None
        self.assertEqual(inherited["source_commit"], self.merge_commit)
        self.assertEqual(inherited["checked_source_commit"], self.inputs["source_commit"])
        self.assertEqual(inherited["evidence_run_id"], "candidate")
        self.assertNotEqual(self.store.current_token(), self.initial)

    def test_different_configuration_cannot_inherit(self) -> None:
        self.assertIsNone(inherit(self.store, self.merged, self.merge_commit, "b" * 64))
        self.assertIsNone(inherit(self.store, self.merged, self.merge_commit, None))
        self.assertEqual(self.store.current_token(), self.initial)

    def test_advanced_model_baseline_cannot_be_overwritten_by_old_candidate(self) -> None:
        self.store.publish(self.fixture.run_dir, self.fixture.work, {**self.fixture.inputs, "previous": self.initial})
        advanced = self.store.current_token()
        self.assertIsNone(inherit(self.store, self.merged, self.merge_commit, "a" * 64))
        self.assertEqual(self.store.current_token(), advanced)

    def test_changed_merged_tree_cannot_inherit(self) -> None:
        (self.merged / "new-module").write_text("untested interaction")
        git(self.merged, "add", ".")
        git(self.merged, "commit", "--quiet", "-m", "changed merge")
        commit = git(self.merged, "rev-parse", "HEAD")
        self.assertIsNone(inherit(self.store, self.merged, commit, "a" * 64))
        self.assertEqual(self.store.current_token(), self.initial)

    def test_modified_candidate_assets_are_rejected(self) -> None:
        (self.fixture.root / self.token / "model/spec/base.tla").write_text("unverified modification")
        with self.assertRaises(CIError):
            inherit(self.store, self.merged, self.merge_commit, "a" * 64)
        self.assertEqual(self.store.current_token(), self.initial)

    def test_repeated_inheritance_does_not_replace_current_again(self) -> None:
        inherit(self.store, self.merged, self.merge_commit, "a" * 64)
        published = self.store.current_token()
        reused = inherit(self.store, self.merged, self.merge_commit, "a" * 64)
        assert reused is not None
        self.assertEqual(reused["reuse_kind"], "current")
        self.assertEqual(self.store.current_token(), published)


class EventTests(unittest.TestCase):
    def test_configured_branch_is_not_hardcoded_to_main(self) -> None:
        event = Event.parse(
            "push",
            {"repository": {"full_name": "owner/repo"}, "ref": "refs/heads/release/v2", "after": "a" * 40},
            {"GITHUB_REPOSITORY": "owner/repo"},
        )
        assert event is not None
        self.assertEqual(event.branch, "release/v2")

    def test_cross_repository_events_are_rejected(self) -> None:
        with self.assertRaises(CIError):
            Event.parse("push", {"repository": {"full_name": "elsewhere/repo"}}, {"GITHUB_REPOSITORY": "owner/repo"})

    def test_deleted_pr_heads_and_external_forks_are_not_executed(self) -> None:
        for head in ({"repo": None}, {"repo": {"full_name": "fork/repo"}}):
            with self.subTest(head=head):
                self.assertIsNone(
                    Event.parse(
                        "pull_request_target",
                        {"repository": {"full_name": "owner/repo"}, "pull_request": {"head": head}},
                        {"GITHUB_REPOSITORY": "owner/repo"},
                    )
                )

    def test_tag_push_and_malformed_sha_are_rejected(self) -> None:
        for ref, revision in (("refs/tags/v1", "a" * 40), ("refs/heads/trunk", "--config=bad")):
            with self.subTest(ref=ref), self.assertRaises(CIError):
                Event.parse(
                    "push",
                    {"repository": {"full_name": "owner/repo"}, "ref": ref, "after": revision},
                    {"GITHUB_REPOSITORY": "owner/repo"},
                )

    def test_report_export_cannot_overwrite_ci_storage(self) -> None:
        runner = GitHubCI(Path("/tmp/project-ci"), Path("/tmp/project-code"), Path("/tmp/project-ci/current"), [])
        with self.assertRaises(CIError):
            runner.validate_reports()
