"""CI initialization composes inputs and registers artifacts, not correctness."""

from __future__ import annotations

import contextlib
import hashlib
import io
import json
import os
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from specula import ci_init, resumelib
from specula import pipelinelib as pl


class TestCIInit(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.run_dir = self.root / "run"
        self.work = self.run_dir / "project" / ".specula-output"
        self.work.mkdir(parents=True)

    def artifact(self, name: str, text: str = "retained input\n") -> Path:
        path = self.work / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        return path

    def register(self, invocation: str = "first", exit_code: int = 0) -> Path | None:
        _, inputs = ci_init.stage_inputs(self.run_dir, "user scope\n")
        return ci_init.register_baseline(
            self.run_dir,
            self.work,
            target="project",
            invocation=invocation,
            inputs_dir=inputs,
            source={"before": {"commit": "a" * 40}},
            pipeline_exit_code=exit_code,
        )

    def test_composition_preserves_user_text_and_is_idempotent(self) -> None:
        user = "  Explicit exclusions\n{{literal}} $HOME `not a command`\n\n"
        effective, inputs = ci_init.stage_inputs(self.run_dir, user)
        again, same_inputs = ci_init.stage_inputs(self.run_dir, user)
        self.assertEqual((inputs / "user-guidance.md").read_text(), user)
        self.assertEqual((inputs / "effective-guidance.md").read_text(), effective)
        self.assertTrue(effective.endswith(user))
        self.assertEqual((effective, inputs), (again, same_inputs))
        self.assertEqual(effective.count((inputs / "ci-guidance.md").read_text()), 1)

    def test_input_changes_keep_previous_effective_guidance(self) -> None:
        previous, first = ci_init.stage_inputs(self.run_dir, "first")
        current, second = ci_init.stage_inputs(self.run_dir, "second")
        self.assertNotEqual(first, second)
        self.assertEqual((first / "effective-guidance.md").read_text(), previous)
        self.assertEqual((second / "effective-guidance.md").read_text(), current)

    def test_tampered_input_snapshot_is_not_overwritten(self) -> None:
        _, inputs = ci_init.stage_inputs(self.run_dir, "scope")
        (inputs / "user-guidance.md").write_text("unexpected")
        with self.assertRaises(ci_init.CIInitError):
            ci_init.stage_inputs(self.run_dir, "scope")

    def test_control_directory_cannot_be_a_symlink(self) -> None:
        outside = self.root / "outside"
        outside.mkdir()
        (self.run_dir / "ci-init").symlink_to(outside, target_is_directory=True)
        with self.assertRaises(ci_init.CIInitError):
            ci_init.stage_inputs(self.run_dir, "scope")
        self.assertEqual(list(outside.iterdir()), [])

    def test_missing_or_empty_model_does_not_register(self) -> None:
        self.assertIsNone(self.register())
        self.artifact("spec/base.tla", "")
        self.assertIsNone(self.register())
        self.assertFalse((self.run_dir / ci_init.BASELINE_FILENAME).exists())

    def test_failed_validation_still_registers_unverified_model(self) -> None:
        self.artifact("spec/base.tla", "---- MODULE base ----\n====\n")
        self.artifact("spec/changelog.md", "Trace validation failed; MC limited.\n")
        self.artifact("harness/run.sh", "#!/bin/sh\nexit 0\n").chmod(0o755)
        self.artifact("traces/captured.ndjson", '{"event":"actual"}\n')
        record = self.register(exit_code=9)
        assert record is not None
        data = json.loads(record.read_text())
        self.assertEqual(data["validation_status"], "UNVERIFIED")
        self.assertEqual(data["pipeline_exit_code"], 9)
        self.assertIn("spec/MC.tla", data["missing_artifacts"])
        snapshot = self.run_dir / data["assets"]
        self.assertEqual((snapshot / "spec/changelog.md").read_text(), "Trace validation failed; MC limited.\n")
        self.assertTrue(os.access(snapshot / "harness/run.sh", os.X_OK))
        for path, digest in data["files_sha256"].items():
            self.assertEqual(hashlib.sha256((snapshot / path).read_bytes()).hexdigest(), digest)

    def test_successful_process_does_not_certify_model(self) -> None:
        self.artifact("spec/base.tla")
        record = self.register()
        assert record is not None
        self.assertEqual(json.loads(record.read_text())["validation_status"], "UNVERIFIED")

    def test_invalid_existing_registration_is_not_silently_accepted(self) -> None:
        self.artifact("spec/base.tla")
        (self.run_dir / ci_init.BASELINE_FILENAME).write_text("not a registration")
        with self.assertRaises(ci_init.CIInitError):
            self.register()
        self.assertEqual((self.run_dir / ci_init.BASELINE_FILENAME).read_text(), "not a registration")

    def test_resume_keeps_first_registration_and_artifacts(self) -> None:
        model = self.artifact("spec/base.tla", "old reference\n")
        first = self.register()
        assert first is not None
        original = first.read_bytes()
        old_assets = self.run_dir / json.loads(original)["assets"]
        model.write_text("repaired reference\n")
        second = self.register(invocation="resumed")
        assert second is not None
        self.assertNotEqual(first, second)
        self.assertEqual(first.read_bytes(), original)
        self.assertEqual((old_assets / "spec/base.tla").read_text(), "old reference\n")
        new_assets = self.run_dir / json.loads(second.read_text())["assets"]
        self.assertEqual((new_assets / "spec/base.tla").read_text(), "repaired reference\n")

    def test_artifact_symlinks_and_scratch_are_not_copied(self) -> None:
        self.artifact("spec/base.tla")
        self.artifact("spec/states/temporary", "intermediate")
        self.artifact("artifact/private", "source tree")
        secret = self.root / "secret"
        secret.write_text("must not copy")
        (self.work / "spec" / "linked.tla").symlink_to(secret)
        record = self.register()
        assert record is not None
        data = json.loads(record.read_text())
        self.assertIn("spec/linked.tla", data["omitted_paths"])
        self.assertIn("spec/states", data["omitted_paths"])
        self.assertNotIn("artifact/private", data["files_sha256"])
        self.assertFalse((self.run_dir / data["assets"] / "spec/linked.tla").exists())

    def test_symlinked_target_does_not_register_external_model(self) -> None:
        self.artifact("spec/base.tla")
        target = self.work.parent
        outside = self.root / "outside"
        target.rename(outside)
        target.symlink_to(outside, target_is_directory=True)
        self.assertIsNone(self.register())

    def test_ci_mode_rejects_skips_byom_and_multiple_targets(self) -> None:
        provided = self.root / "model.tla"
        provided.write_text("provided")
        invalid = [[flag, "project"] for flag in pl.BYOM_CONFLICTING_FLAGS]
        invalid += [[f"--byom={provided}", "project"], ["a", "b"], ["--no-isolate", "project"]]
        for args in invalid:
            with self.subTest(args=args), contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(pl.Pipeline().parse_args(["--ci-init", *args]), 1)

    def test_ci_mode_restores_on_resume_and_rejects_explicit_skip(self) -> None:
        initial = pl.Pipeline()
        self.assertIsNone(initial.parse_args(["--ci-init", "project"]))
        saved = initial._resume_configuration_document()
        resumed = pl.Pipeline()
        self.assertIsNone(resumed.parse_args([]))
        resumed._restore_resume_configuration(saved)
        self.assertTrue(resumed.ci_init)
        self.assertEqual(resumed.targets, ["project"])
        invalid = pl.Pipeline()
        self.assertIsNone(invalid.parse_args(["--skip-validate"]))
        with self.assertRaisesRegex(resumelib.ResumeError, "--ci-init conflicts"):
            invalid._restore_resume_configuration(saved)

    def test_ordinary_run_cannot_be_converted_in_place(self) -> None:
        ordinary = pl.Pipeline()
        self.assertIsNone(ordinary.parse_args(["project"]))
        saved = ordinary._resume_configuration_document()
        self.assertNotIn("ci_init", saved)
        for override in (False, True):
            candidate = pl.Pipeline()
            self.assertIsNone(candidate.parse_args(["--ci-init", "project"]))
            with self.assertRaisesRegex(resumelib.ResumeError, "existing ordinary run"):
                candidate._restore_resume_configuration(saved, allow_overrides=override)

    def test_ci_fresh_context_cannot_change_project(self) -> None:
        initial = pl.Pipeline()
        self.assertIsNone(initial.parse_args(["--ci-init", "project"]))
        replacement = pl.Pipeline()
        self.assertIsNone(replacement.parse_args(["other-project"]))
        with self.assertRaisesRegex(resumelib.ResumeError, "targets cannot change"):
            replacement._restore_resume_configuration(initial._resume_configuration_document(), allow_overrides=True)

    def test_private_source_identity_keeps_original_revision(self) -> None:
        pipeline = pl.Pipeline()
        pipeline.run_dir = self.run_dir
        pipeline.keep_original = True
        original = self.root / "source"
        pipeline._snapshot_sources = {"project": original}
        private = self.run_dir / "project/source"
        commits = {original: "a" * 40, private: "b" * 40}
        with (
            mock.patch.object(pl, "_git_source_commit", side_effect=lambda path: commits[path]),
            mock.patch("specula.pipelinelib.subprocess.run", return_value=subprocess.CompletedProcess([], 0, "", "")),
        ):
            state = pipeline._ci_source_state("project")
        self.assertEqual(state["commit"], "b" * 40)
        self.assertEqual(state["original_commit"], "a" * 40)
        self.assertEqual(state["source_mode"], "snapshot")

    def test_guidance_cannot_be_published_through_symlinked_target(self) -> None:
        target = self.work.parent
        outside = self.root / "outside"
        target.rename(outside)
        target.symlink_to(outside, target_is_directory=True)
        pipeline = pl.Pipeline()
        self.assertIsNone(pipeline.parse_args(["--ci-init", "project"]))
        pipeline.run_dir = self.run_dir
        with self.assertRaises(ci_init.CIInitError):
            pipeline.stage_guidance(["project"])
        self.assertFalse((outside / ".specula-output/.prompt-extra.md").exists())

    def test_ci_default_guidance_never_prompts(self) -> None:
        pipeline = pl.Pipeline()
        self.assertIsNone(pipeline.parse_args(["--ci-init", "project"]))
        with mock.patch("builtins.input", side_effect=AssertionError("must not prompt")):
            self.assertFalse(pipeline.should_confirm_without_guidance_before_resolve())
            self.assertTrue(pipeline.confirm_without_guidance())

    def test_legacy_guidance_is_preserved_without_repeated_ci_prefix(self) -> None:
        legacy = self.artifact(".prompt-extra.md", "user's existing guidance\n")
        pipeline = pl.Pipeline()
        self.assertIsNone(pipeline.parse_args(["--ci-init", "project"]))
        pipeline.run_dir = self.run_dir
        with contextlib.redirect_stdout(io.StringIO()):
            pipeline.stage_guidance(["project"])
            once = legacy.read_text()
            pipeline.stage_guidance(["project"])
        self.assertEqual(legacy.read_text(), once)
        assert pipeline._ci_init_inputs is not None
        self.assertEqual((pipeline._ci_init_inputs / "user-guidance.md").read_text(), "user's existing guidance\n")

    def test_explicit_guidance_wins_over_compatibility_file(self) -> None:
        self.artifact(".prompt-extra.md", "fallback that must not leak")
        user = self.root / "guidance.md"
        user.write_text("explicit scope\n")
        pipeline = pl.Pipeline()
        self.assertIsNone(pipeline.parse_args(["--ci-init", f"--guidance={user}", "project"]))
        pipeline.run_dir = self.run_dir
        with contextlib.redirect_stdout(io.StringIO()):
            pipeline.stage_guidance(["project"])
        effective = (self.work / ".prompt-extra.initial.md").read_text()
        self.assertTrue(effective.endswith("explicit scope\n"))
        self.assertNotIn("fallback that must not leak", effective)


if __name__ == "__main__":
    unittest.main()
