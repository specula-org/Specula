"""Execution options follow the initialization or single-conversation CI mode."""

from __future__ import annotations

import contextlib
import io
import json
import tempfile
import unittest
from pathlib import Path

from specula.agent_config import PHASES
from specula.ci_phase import IncrementalPhase
from specula.ci_workflow import CIPipeline
from specula.phaselib import Workspace
from specula.pipelinelib import Pipeline
from specula.resumelib import ResumeError

PHASE_FLAGS = (
    "--legacy-confirm",
    "--max-repair-rounds=1",
)


class CIOptions(unittest.TestCase):
    def setUp(self) -> None:
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        self.ci_flag = f"--ci-dir={self.root / 'ci'}"
        self.config = self.root / "agents.json"
        self.document = {
            "version": 1,
            "default_profile": "selected",
            "profiles": {
                "selected": {"agent": "codex", "model": "selected-model", "effort": "high"},
                "unused": {"agent": "unused-adapter", "model": "unused-model"},
            },
        }
        self.config.write_text(json.dumps(self.document))

    def test_oneshot_and_initialization_keep_the_classification_summary_setting(self) -> None:
        for pipeline in (Pipeline(), CIPipeline()):
            for skipped in (False, True):
                with self.subTest(pipeline=type(pipeline).__name__, skipped=skipped):
                    pipeline.skip_classification = skipped
                    self.assertEqual(pipeline._summary_findings_enabled(), not skipped)

    def test_incremental_summary_uses_the_final_result_contract(self) -> None:
        pipeline = CIPipeline()
        self.assertIsNone(pipeline.parse_args(["--incremental", self.ci_flag]))
        for inputs, enabled in ((None, False), ({}, False), ({"final_result_version": 1}, True)):
            with self.subTest(inputs=inputs):
                pipeline.inputs = inputs
                self.assertEqual(pipeline._summary_findings_enabled(), enabled)
                self.assertTrue(pipeline.skip_classification)

    def test_final_marker_cannot_skip_confirmation_repair_reconciliation(self) -> None:
        ws = Workspace(["project"], run_dir=self.root)
        work = ws.work_dir("project")
        (work / "spec").mkdir(parents=True)
        (work / "incremental.log").write_text(f"SPECULA_INCREMENTAL_COMPLETE {self.root.name}\n")
        (work / "spec/.repair-phase3-snapshot.json").write_text("{}")
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            failures = IncrementalPhase().finalize_outputs(ws, ["project"], adapter=Path("fake.sh"), dry_run=False)
        self.assertEqual(failures, [("project", 1)])
        self.assertIn("confirmation repair is unfinished", output.getvalue())

    def test_phase_options_are_rejected_only_for_incremental_runs(self) -> None:
        for flag in PHASE_FLAGS:
            with self.subTest(flag=flag):
                error = io.StringIO()
                with contextlib.redirect_stderr(error):
                    self.assertEqual(CIPipeline().parse_args([self.ci_flag, flag, "--incremental"]), 1)
                self.assertIn("not supported for incremental CI", error.getvalue())
                self.assertIn(flag.split("=", 1)[0], error.getvalue())
                self.assertFalse((self.root / "ci").exists())
                self.assertIsNone(CIPipeline().parse_args(["--ci-init", self.ci_flag, flag, "project"]))
                self.assertIsNone(Pipeline().parse_args([flag, "project"]))

    def test_phase_options_are_rejected_after_restoring_incremental_mode(self) -> None:
        original = CIPipeline()
        self.assertIsNone(original.parse_args(["--incremental", self.ci_flag]))
        saved = original._resume_configuration_document()
        for flag in PHASE_FLAGS:
            with self.subTest(flag=flag):
                resumed = CIPipeline()
                self.assertIsNone(resumed.parse_args([self.ci_flag, "--run-id=existing", flag]))
                with self.assertRaisesRegex(ResumeError, "not supported for incremental CI"):
                    resumed._restore_resume_configuration(saved)

    def test_phase_routes_are_rejected_for_new_and_resumed_incremental_runs(self) -> None:
        original = CIPipeline()
        self.assertIsNone(original.parse_args(["--incremental", self.ci_flag, f"--agent-config={self.config}"]))
        saved = original._resume_configuration_document()
        for phase in sorted(PHASES - {"confirm"}):
            with self.subTest(phase=phase):
                self.config.write_text(json.dumps({**self.document, "phases": {phase: "selected"}}))
                error = io.StringIO()
                with contextlib.redirect_stderr(error):
                    self.assertEqual(
                        CIPipeline().parse_args(["--incremental", self.ci_flag, f"--agent-config={self.config}"]), 1
                    )
                self.assertIn("supports only phases.confirm", error.getvalue())
                resumed = CIPipeline()
                self.assertIsNone(
                    resumed.parse_args([self.ci_flag, "--run-id=existing", f"--agent-config={self.config}"])
                )
                with self.assertRaisesRegex(ResumeError, "supports only phases.confirm"):
                    resumed._restore_resume_configuration(saved)
                self.assertIsNone(
                    CIPipeline().parse_args(["--ci-init", self.ci_flag, f"--agent-config={self.config}", "project"])
                )

    def test_multiple_profiles_select_only_the_default_for_execution_and_resume(self) -> None:
        for include_phases in (False, True):
            with self.subTest(include_phases=include_phases):
                document = dict(self.document)
                if include_phases:
                    document["phases"] = {}
                self.config.write_text(json.dumps(document))
                original = CIPipeline()
                self.assertIsNone(original.parse_args(["--incremental", self.ci_flag, f"--agent-config={self.config}"]))
                original.validate_agent_adapter()  # The unused adapter does not exist.
                args = original._phase_args(["project"])
                self.assertIn("--agent=codex", args)
                self.assertIn("--model=selected-model", args)
                self.assertIn("--effort=high", args)
                saved = original._resume_configuration_document()
                self.assertEqual(set(saved["routes"]), {"incremental", "confirm"})
                resumed = CIPipeline()
                self.assertIsNone(resumed.parse_args([self.ci_flag, "--run-id=existing"]))
                resumed._restore_resume_configuration(saved)
                resumed.validate_agent_adapter()
                self.assertEqual(resumed._phase_args(["project"]), args)

    def test_resume_compares_the_selected_profile_only(self) -> None:
        original = CIPipeline()
        self.assertIsNone(original.parse_args(["--incremental", self.ci_flag, f"--agent-config={self.config}"]))
        saved = original._resume_configuration_document()
        for selected_model, succeeds in (("selected-model", True), ("different-model", False)):
            with self.subTest(selected_model=selected_model):
                self.config.write_text(
                    json.dumps(
                        {
                            **self.document,
                            "profiles": {
                                "selected": {"agent": "codex", "model": selected_model, "effort": "high"},
                                "unused": {"agent": "another-unused-adapter"},
                            },
                        }
                    )
                )
                resumed = CIPipeline()
                self.assertIsNone(
                    resumed.parse_args([self.ci_flag, "--run-id=existing", f"--agent-config={self.config}"])
                )
                if succeeds:
                    resumed._restore_resume_configuration(saved)
                else:
                    with self.assertRaisesRegex(ResumeError, "agent-config differs"):
                        resumed._restore_resume_configuration(saved)

    def test_confirm_route_and_controls_survive_resume_without_the_config_file(self) -> None:
        profiles = self.document["profiles"]
        assert isinstance(profiles, dict)
        document = {
            **self.document,
            "profiles": {
                **profiles,
                "confirmation": {"agent": "pi", "model": "confirm-model", "effort": "low"},
            },
            "phases": {"confirm": "confirmation"},
        }
        self.config.write_text(json.dumps(document))
        original = CIPipeline()
        self.assertIsNone(
            original.parse_args(
                [
                    "--incremental",
                    self.ci_flag,
                    f"--agent-config={self.config}",
                    "--confirm-debate",
                    "--max-parallel=2",
                ]
            )
        )
        saved = original._resume_configuration_document()
        self.config.unlink()
        resumed = CIPipeline()
        self.assertIsNone(resumed.parse_args([self.ci_flag, "--run-id=existing"]))
        resumed._restore_resume_configuration(saved)
        self.assertEqual(resumed._configured_agents(), {"codex", "pi"})
        self.assertTrue(resumed.confirm_debate)
        self.assertEqual(resumed.max_parallel, "2")
        self.assertIn("--model=confirm-model", resumed._phase_args(["project"], phase="confirm"))
        self.assertIn("--model=selected-model", resumed._phase_args(["project"]))

    def test_incremental_help_is_mode_specific_and_order_independent(self) -> None:
        for args in (["--incremental", "--help"], ["--help", "--incremental"]):
            with self.subTest(args=args):
                output = io.StringIO()
                with contextlib.redirect_stdout(output):
                    self.assertEqual(CIPipeline().parse_args(args), 0)
                text = output.getvalue()
                self.assertIn("default_profile", text)
                self.assertIn("--policy-retries", text)
                for flag in (*PHASE_FLAGS, "--skip-analysis", "--enable-reviews", "--fresh-context", "--byom"):
                    self.assertNotIn(flag.split("=", 1)[0], text)
