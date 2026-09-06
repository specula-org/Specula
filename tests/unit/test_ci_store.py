"""Persistent state is replaced only as a complete, version-bound publication."""

from __future__ import annotations

import contextlib
import io
import os
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from specula.adapters.utils.run_lock import CI_LOCK_FD_ENV, RUN_LOCK_FD_ENV, inherited_run_lock_fds
from specula.ci_store import CIError, CIStore, asset_hashes, git
from specula.ci_workflow import CIPipeline


class StoreTests(unittest.TestCase):
    def setUp(self) -> None:
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        self.store = CIStore(self.root)
        self.run_dir = self.root / "runs/first"
        self.work = self.run_dir / "project/.specula-output"
        (self.work / "spec").mkdir(parents=True)
        (self.work / "harness").mkdir()
        (self.work / "spec/base.tla").write_text("model\n")
        (self.work / "harness/run.sh").write_text("#!/bin/sh\n")
        self.source = self.run_dir / "ci-source"
        self.source.mkdir()
        git(self.source, "init", "--quiet")
        (self.source / "code").write_text("source\n")
        git(self.source, "add", ".")
        git(self.source, "commit", "--quiet", "-m", "fixture")
        commit = git(self.source, "rev-parse", "HEAD")
        self.inputs = {
            "previous": None,
            "target": "project",
            "artifact": str(self.source),
            "source": "runs/first/ci-source",
            "source_commit": commit,
            "snapshot_commit": commit,
            "dirty": False,
            "guidance": "scope",
        }

    def test_publication_copies_assets_and_binds_source(self) -> None:
        current = self.store.publish(self.run_dir, self.work, self.inputs)
        state = self.store.current()
        self.assertEqual(state["source_commit"], self.inputs["source_commit"])
        self.assertEqual(state["files_sha256"], asset_hashes(current / "model"))
        (self.work / "spec/base.tla").write_text("working edit\n")
        self.assertEqual((current / "model/spec/base.tla").read_text(), "model\n")

    def test_stale_publication_does_not_replace_current(self) -> None:
        self.store.publish(self.run_dir, self.work, self.inputs)
        current = self.store.current_token()
        with self.assertRaisesRegex(CIError, "advanced"):
            self.store.publish(self.run_dir, self.work, self.inputs)
        self.assertEqual(self.store.current_token(), current)

    def test_missing_harness_does_not_publish(self) -> None:
        (self.work / "harness/run.sh").unlink()
        with self.assertRaisesRegex(CIError, "harness"):
            self.store.publish(self.run_dir, self.work, self.inputs)
        self.assertIsNone(self.store.current_token())

    def test_model_diff_excludes_tlc_states_and_execution_logs(self) -> None:
        self.store.publish(self.run_dir, self.work, self.inputs)
        next_inputs = {**self.inputs, "previous": self.store.current_token()}
        (self.work / "spec/base.tla").write_text("changed model\n")
        (self.work / "spec/states").mkdir()
        (self.work / "spec/states/intermediate").write_text("never inline this state data")
        (self.work / "spec/MC.out").write_text("TLC log")
        self.store.publish(self.run_dir, self.work, next_inputs)
        diff = (self.run_dir / "model.diff").read_text()
        self.assertIn("-model\n+changed model", diff)
        self.assertNotIn("intermediate", diff)
        self.assertNotIn("TLC log", diff)
        self.assertFalse((self.root / "current/model/spec/states").exists())

    def test_external_model_symlink_is_not_adopted(self) -> None:
        outside = self.root / "external.tla"
        outside.write_text("external")
        (self.work / "spec/helper.tla").symlink_to(outside)
        with self.assertRaisesRegex(CIError, "unsupported assets"):
            self.store.publish(self.run_dir, self.work, self.inputs)
        self.assertIsNone(self.store.current_token())
        self.assertEqual(outside.read_text(), "external")

    def test_current_symlink_cannot_escape_store(self) -> None:
        (self.root / "current").symlink_to("../outside")
        with self.assertRaises(CIError):
            self.store.current()

    def test_regular_current_file_is_not_replaced(self) -> None:
        (self.root / "current").write_text("user file")
        with self.assertRaises(CIError):
            self.store.publish(self.run_dir, self.work, self.inputs)
        self.assertEqual((self.root / "current").read_text(), "user file")

    def test_modified_current_assets_and_source_are_detected(self) -> None:
        current = self.store.publish(self.run_dir, self.work, self.inputs)
        (self.source / "code").write_text("unexpected source change")
        with self.assertRaisesRegex(CIError, "saved source"):
            self.store.current()
        (self.source / "code").write_text("source\n")
        (current / "model/spec/base.tla").write_text("unexpected model change")
        with self.assertRaisesRegex(CIError, "model assets"):
            self.store.current()

    def test_ci_lease_is_inherited_with_the_run_lease(self) -> None:
        with mock.patch.dict(os.environ, {}, clear=True):
            self.store.acquire()
            try:
                with tempfile.TemporaryFile() as run_lock:
                    env = {CI_LOCK_FD_ENV: str(self.store.fd), RUN_LOCK_FD_ENV: str(run_lock.fileno())}
                    self.assertEqual(inherited_run_lock_fds(env), (run_lock.fileno(), self.store.fd))
                assert self.store.fd is not None
                child = subprocess.Popen(["sleep", "10"], pass_fds=(self.store.fd,))
                self.addCleanup(child.wait)
                self.addCleanup(child.terminate)
                self.store.close()
                with self.assertRaises(BlockingIOError):
                    CIStore(self.root).acquire()
            finally:
                self.store.close()

    def test_invalid_mode_flags_fail_before_creating_ci_storage(self) -> None:
        for extra in (
            ["--skip-validate"],
            ["--ci-init"],
            ["--no-isolate"],
            ["--enable-reviews"],
            ["--policy-retries=1"],
        ):
            with self.subTest(extra=extra), contextlib.redirect_stderr(io.StringIO()):
                pipeline = CIPipeline()
                self.assertEqual(
                    pipeline.parse_args(["--incremental", f"--ci-dir={self.root / 'not-created'}", *extra]), 1
                )
        self.assertFalse((self.root / "not-created").exists())

    def test_ci_resume_rejects_missing_invalid_and_symlinked_runs_before_locking(self) -> None:
        alias = self.root / "runs/alias"
        alias.symlink_to(self.run_dir, target_is_directory=True)
        (self.root / "runs/file").write_text("not a run directory")
        for run_id in ("missing", "", "../first", "alias", "file"):
            with self.subTest(run_id=run_id), contextlib.redirect_stderr(io.StringIO()):
                pipeline = CIPipeline()
                self.assertIsNone(pipeline.parse_args([f"--ci-dir={self.root}", f"--run-id={run_id}"]))
                assert pipeline.store is not None
                with mock.patch.object(pipeline.store, "acquire") as acquire:
                    self.assertEqual(pipeline.resolve_run_dir(acquire_lock=True), 1)
                acquire.assert_not_called()
        self.assertFalse((self.root / "runs/missing").exists())
        self.assertFalse((self.root / ".lock").exists())
