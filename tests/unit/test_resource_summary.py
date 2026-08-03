"""Focused tests for per-target resource summary checkpoints."""

from __future__ import annotations

import json
import os
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from specula.resource_summary import (
    INVOCATION_DIRNAME,
    PHASES,
    STATE_FILENAME,
    SUMMARY_FILENAME,
    ResourceInvocationRecorder,
    ResourceSummaryTracker,
)


def _normalized(
    *,
    session: str | None,
    tokens: int,
    cached: int,
    cost: float | None,
    agent: str = "codex",
    complete: bool | None = None,
) -> dict[str, object]:
    payload: dict[str, object] = {
        "agent": agent,
        "session_id": session,
        "total_cost_usd": cost,
        "usage": {
            "total_tokens": tokens,
            "cached_input_tokens": cached,
        },
    }
    if complete is not None:
        payload["usage_complete"] = complete
    return payload


class ResourceSummaryCase(unittest.TestCase):
    def setUp(self) -> None:
        self._temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self._temporary.cleanup)
        self.root = Path(self._temporary.name).resolve()
        self.work_dir = self.root / "demo" / ".specula-output"

    def tracker(self) -> ResourceSummaryTracker:
        return ResourceSummaryTracker(
            {"demo": self.work_dir},
            output_root=self.root,
            maximum_parallelism="1",
            tlc_memory_limit="8G",
            tlc_worker_limit="4",
        )

    def write_json(self, relative: str, payload: object) -> Path:
        path = self.work_dir / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(payload) + "\n")
        return path

    def summary(self) -> str:
        return (self.work_dir / SUMMARY_FILENAME).read_text()

    def state(self) -> dict[str, object]:
        value = json.loads((self.work_dir / STATE_FILENAME).read_text())
        assert isinstance(value, dict)
        return value

    @staticmethod
    def phase_state(state: dict[str, object], phase: str) -> dict[str, object]:
        phases = state["phases"]
        assert isinstance(phases, dict)
        value = phases[phase]
        assert isinstance(value, dict)
        return value


class TestRenderingAndRuntime(ResourceSummaryCase):
    def test_initialize_creates_only_the_small_resource_summary(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)

        self.assertTrue((self.work_dir / STATE_FILENAME).is_file())
        text = self.summary()
        self.assertIn("# Specula Summary", text)
        self.assertIn("| Phase | Runtime | Tokens | Estimated cost |", text)
        for label in ("Phase 1", "Phase 2", "Phase 2.5", "Phase 3", "Phase 4a", "Phase 4b"):
            self.assertIn(f"| {label} | - | - | - |", text)
        self.assertIn("| **Total (incomplete)** | - | - | - |", text)
        self.assertIn("- Configured maximum parallelism: 1", text)
        self.assertIn("- Configured TLC limits: 8G memory; 4 workers", text)

    def test_empty_resume_without_a_checkpoint_is_not_historical_loss(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=True)

        self.assertFalse(self.state()["history_incomplete"])

    def test_resume_without_a_checkpoint_shows_available_usage_as_partial(self) -> None:
        self.write_json(
            "agent.usage.json",
            _normalized(session="orphaned", tokens=420, cached=200, cost=1.5),
        )
        tracker = self.tracker()

        tracker.initialize(resume=True)

        self.assertTrue(self.state()["history_incomplete"])
        self.assertIn("420 total (200 cached)", self.summary())
        self.assertIn("$1.50", self.summary())
        self.assertIn("**Total (incomplete)**", self.summary())


class TestInvocationAccounting(ResourceSummaryCase):
    def recorder(self, phase: str, invocation_id: str) -> ResourceInvocationRecorder:
        path = self.root / INVOCATION_DIRNAME / f"{invocation_id}.json"
        return ResourceInvocationRecorder(self.root, path, phase, invocation_id)

    def test_serial_targets_receive_only_their_own_runtime(self) -> None:
        second_work_dir = self.root / "second" / ".specula-output"
        tracker = ResourceSummaryTracker(
            {"demo": self.work_dir, "second": second_work_dir},
            output_root=self.root,
            maximum_parallelism="1",
            tlc_memory_limit="8G",
            tlc_worker_limit="4",
        )
        tracker.initialize(resume=False)
        invocation_id = "1" * 32
        recorder = self.recorder("phase1", invocation_id)
        with mock.patch("specula.resource_summary.time.monotonic", side_effect=[0.0, 10.0, 10.0, 30.0, 30.0]):
            recorder.start_target("demo", self.work_dir)
            recorder.finish_target("demo", True)
            recorder.start_target("second", second_work_dir)
            recorder.finish_target("second", True)
            recorder.finalize(True)

        tracker.capture_invocation(
            "phase1",
            ["demo", "second"],
            invocation_id,
            launcher_succeeded=True,
        )

        first = json.loads((self.work_dir / STATE_FILENAME).read_text())
        second = json.loads((second_work_dir / STATE_FILENAME).read_text())
        self.assertEqual(self.phase_state(first, "phase1")["runtime_seconds"], 10.0)
        self.assertEqual(self.phase_state(second, "phase1")["runtime_seconds"], 20.0)

    def test_failed_target_does_not_mark_successful_sibling_incomplete(self) -> None:
        second_work_dir = self.root / "second" / ".specula-output"
        tracker = ResourceSummaryTracker(
            {"demo": self.work_dir, "second": second_work_dir},
            output_root=self.root,
            maximum_parallelism="2",
            tlc_memory_limit="8G",
            tlc_worker_limit="4",
        )
        tracker.initialize(resume=False)
        invocation_id = "2" * 32
        recorder = self.recorder("phase2_5", invocation_id)
        with mock.patch("specula.resource_summary.time.monotonic", side_effect=[0.0, 0.0, 5.0, 7.0, 7.0]):
            recorder.start_target("demo", self.work_dir)
            recorder.start_target("second", second_work_dir)
            recorder.finish_target("demo", True)
            recorder.finish_target("second", False)
            recorder.finalize(False)

        tracker.capture_invocation(
            "phase2_5",
            ["demo", "second"],
            invocation_id,
            launcher_succeeded=False,
        )

        first = json.loads((self.work_dir / STATE_FILENAME).read_text())
        second = json.loads((second_work_dir / STATE_FILENAME).read_text())
        self.assertFalse(self.phase_state(first, "phase2_5")["usage_incomplete"])
        self.assertTrue(self.phase_state(second, "phase2_5")["usage_incomplete"])

    def test_successful_zero_agent_invocation_preserves_existing_usage(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        self.write_json(
            "bug-confirmation.usage.json",
            _normalized(session="existing", tokens=100, cached=80, cost=1.0),
        )
        tracker.capture_usage("phase4a", ["demo"])
        invocation_id = "3" * 32
        recorder = self.recorder("phase4a", invocation_id)
        with mock.patch("specula.resource_summary.time.monotonic", side_effect=[0.0, 1.0, 1.0]):
            recorder.start_target("demo", self.work_dir)
            recorder.finish_target("demo", True)
            recorder.finalize(True)

        tracker.capture_invocation("phase4a", ["demo"], invocation_id, launcher_succeeded=True)

        phase = self.phase_state(self.state(), "phase4a")
        self.assertFalse(phase["usage_incomplete"])
        self.assertEqual(phase["total_tokens"], 100)
        self.assertEqual(phase["cost_usd"], 1.0)

    def test_successful_fresh_zero_agent_invocation_records_known_zero_usage(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        invocation_id = "8" * 32
        recorder = self.recorder("phase4a", invocation_id)
        with mock.patch("specula.resource_summary.time.monotonic", side_effect=[0.0, 1.0, 1.0]):
            recorder.start_target("demo", self.work_dir)
            recorder.finish_target("demo", True)
            recorder.finalize(True)

        tracker.capture_invocation("phase4a", ["demo"], invocation_id, launcher_succeeded=True)

        phase = self.phase_state(self.state(), "phase4a")
        self.assertTrue(phase["tokens_observed"])
        self.assertTrue(phase["cost_observed"])
        self.assertFalse(phase["usage_incomplete"])
        self.assertIn("| Phase 4a | 1s | 0 total (0 cached) | $0.00 |", self.summary())

    def test_agent_without_a_changed_usage_sidecar_is_incomplete(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        invocation_id = "4" * 32
        recorder = self.recorder("phase1", invocation_id)
        with mock.patch("specula.resource_summary.time.monotonic", side_effect=[0.0, 1.0, 1.0]):
            recorder.start_target("demo", self.work_dir)
            recorder.note_agent(self.work_dir, self.work_dir / "agent.usage.json")
            recorder.finish_target("demo", True)
            recorder.finalize(True)

        tracker.capture_invocation("phase1", ["demo"], invocation_id, launcher_succeeded=True)

        self.assertTrue(self.phase_state(self.state(), "phase1")["usage_incomplete"])

    def test_each_expected_turn_needs_its_own_usage_sidecar(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        invocation_id = "6" * 32
        recorder = self.recorder("phase4a", invocation_id)
        first = self.work_dir / "confirmation" / "MC-1" / "turn01_A.usage.json"
        second = self.work_dir / "confirmation" / "MC-1" / "turn01_B.usage.json"
        with mock.patch("specula.resource_summary.time.monotonic", side_effect=[0.0, 1.0, 1.0]):
            recorder.start_target("demo", self.work_dir)
            recorder.note_agent(self.work_dir, first)
            recorder.note_agent(self.work_dir, second)
            recorder.finish_target("demo", True)
            recorder.finalize(True)
        self.write_json(
            "confirmation/MC-1/turn01_A.usage.json",
            _normalized(session="first", tokens=100, cached=80, cost=1.0),
        )

        tracker.capture_invocation("phase4a", ["demo"], invocation_id, launcher_succeeded=True)

        self.assertTrue(self.phase_state(self.state(), "phase4a")["usage_incomplete"])

    def test_repeated_agent_invocations_on_one_usage_path_are_incomplete(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        invocation_id = "9" * 32
        recorder = self.recorder("phase1", invocation_id)
        usage_path = self.work_dir / "agent.usage.json"
        with mock.patch("specula.resource_summary.time.monotonic", side_effect=[0.0, 1.0, 1.0]):
            recorder.start_target("demo", self.work_dir)
            recorder.note_agent(self.work_dir, usage_path)
            recorder.note_agent(self.work_dir, usage_path)
            recorder.finish_target("demo", True)
            recorder.finalize(True)
        self.write_json(
            "agent.usage.json",
            _normalized(session="last-attempt", tokens=100, cached=80, cost=1.0),
        )

        tracker.capture_invocation("phase1", ["demo"], invocation_id, launcher_succeeded=True)

        phase = self.phase_state(self.state(), "phase1")
        self.assertEqual(phase["total_tokens"], 100)
        self.assertTrue(phase["usage_incomplete"])
        manifest = json.loads((self.root / INVOCATION_DIRNAME / f"{invocation_id}.json").read_text())
        self.assertEqual(manifest["targets"]["demo"]["usage_paths"], ["agent.usage.json", "agent.usage.json"])

    def test_resume_recovers_an_uncheckpointed_target_manifest(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        invocation_id = "7" * 32
        recorder = self.recorder("phase1", invocation_id)
        with mock.patch("specula.resource_summary.time.monotonic", side_effect=[0.0, 9.0, 9.0]):
            recorder.start_target("demo", self.work_dir)
            recorder.note_agent(self.work_dir, self.work_dir / "agent.usage.json")
            recorder.finish_target("demo", True)
            recorder.finalize(True)
        self.write_json(
            "agent.usage.json",
            _normalized(session="recovered", tokens=100, cached=80, cost=1.0),
        )

        resumed = self.tracker()
        resumed.initialize(resume=True)

        phase = self.phase_state(self.state(), "phase1")
        self.assertEqual(phase["runtime_seconds"], 9.0)
        self.assertEqual(phase["total_tokens"], 100)
        self.assertEqual(phase["cost_usd"], 1.0)
        self.assertFalse(self.state()["history_incomplete"])

    def test_resume_marks_two_manifests_sharing_one_sidecar_incomplete(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        usage_path = self.work_dir / "agent.usage.json"
        for invocation_id in ("d" * 32, "e" * 32):
            recorder = self.recorder("phase1", invocation_id)
            recorder.start_target("demo", self.work_dir)
            recorder.note_agent(self.work_dir, usage_path)
            recorder.finish_target("demo", True)
            recorder.finalize(True)
        self.write_json(
            "agent.usage.json",
            _normalized(session="only-visible-session", tokens=100, cached=80, cost=1.0),
        )

        resumed = self.tracker()
        resumed.initialize(resume=True)

        phase = self.phase_state(self.state(), "phase1")
        self.assertEqual(phase["total_tokens"], 100)
        self.assertTrue(phase["usage_incomplete"])

    def test_resume_trusts_one_pending_non_codex_rewrite(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        usage_path = self.work_dir / "spec-repair.usage.json"
        first_id = "1" * 32
        first = self.recorder("phase4a", first_id)
        first.start_target("demo", self.work_dir)
        first.note_agent(self.work_dir, usage_path)
        first.finish_target("demo", True)
        first.finalize(True)
        self.write_json(
            "spec-repair.usage.json",
            _normalized(session=first_id, tokens=100, cached=80, cost=1.0, agent="claude-code"),
        )
        tracker.capture_invocation("phase4a", ["demo"], first_id, launcher_succeeded=True)

        second_id = "2" * 32
        second = self.recorder("phase4a", second_id)
        second.start_target("demo", self.work_dir)
        second.note_agent(self.work_dir, usage_path)
        second.finish_target("demo", True)
        second.finalize(True)
        self.write_json(
            "spec-repair.usage.json",
            _normalized(session=second_id, tokens=50, cached=40, cost=0.5, agent="claude-code"),
        )

        resumed = self.tracker()
        resumed.initialize(resume=True)

        phase = self.phase_state(self.state(), "phase4a")
        self.assertEqual(phase["total_tokens"], 150)
        self.assertEqual(phase["cost_usd"], 1.5)
        self.assertFalse(phase["usage_incomplete"])
        self.assertFalse(self.state()["history_incomplete"])

    def test_resume_detects_tampered_accounted_manifest(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        invocation_id = "3" * 32
        recorder = self.recorder("phase1", invocation_id)
        recorder.start_target("demo", self.work_dir)
        recorder.finish_target("demo", True)
        recorder.finalize(True)
        tracker.capture_invocation("phase1", ["demo"], invocation_id, launcher_succeeded=True)
        path = self.root / INVOCATION_DIRNAME / f"{invocation_id}.json"
        document = json.loads(path.read_text())
        document["targets"]["demo"]["elapsed_seconds"] = 999
        path.write_text(json.dumps(document) + "\n")

        resumed = self.tracker()
        resumed.initialize(resume=True)

        self.assertTrue(self.state()["history_incomplete"])
        phase = self.phase_state(self.state(), "phase1")
        self.assertTrue(phase["runtime_incomplete"])
        self.assertTrue(phase["usage_incomplete"])

    def test_resume_detects_missing_accounted_manifest(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        invocation_id = "4" * 32
        recorder = self.recorder("phase1", invocation_id)
        recorder.start_target("demo", self.work_dir)
        recorder.finish_target("demo", True)
        recorder.finalize(True)
        tracker.capture_invocation("phase1", ["demo"], invocation_id, launcher_succeeded=True)
        (self.root / INVOCATION_DIRNAME / f"{invocation_id}.json").unlink()

        resumed = self.tracker()
        resumed.initialize(resume=True)

        self.assertTrue(self.state()["history_incomplete"])

    def test_resume_marks_malformed_invocation_manifest_incomplete(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        invocation_id = "5" * 32
        path = self.root / INVOCATION_DIRNAME / f"{invocation_id}.json"
        path.parent.mkdir()
        path.write_text("{not json\n")

        resumed = self.tracker()
        resumed.initialize(resume=True)

        self.assertTrue(self.state()["history_incomplete"])

    def test_resume_rejects_invalid_invocation_signature(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        state = self.state()
        signatures = state["invocation_signatures"]
        assert isinstance(signatures, dict)
        signatures["6" * 32] = "not-a-sha256"
        (self.work_dir / STATE_FILENAME).write_text(json.dumps(state) + "\n")

        resumed = self.tracker()
        resumed.initialize(resume=True)

        self.assertTrue(self.state()["history_incomplete"])
        self.assertNotIn("not-a-sha256", json.dumps(self.state()))

    def test_failed_complete_manifest_without_a_target_record_does_not_pollute_targets(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        invocation_id = "5" * 32
        recorder = self.recorder("phase1", invocation_id)
        recorder.finalize(False)

        tracker.capture_invocation("phase1", ["demo"], invocation_id, launcher_succeeded=False)

        phase = self.phase_state(self.state(), "phase1")
        self.assertFalse(phase["runtime_incomplete"])
        self.assertFalse(phase["usage_incomplete"])

    def test_successful_complete_manifest_requires_a_target_record(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        invocation_id = "7" * 32
        recorder = self.recorder("phase1", invocation_id)
        recorder.finalize(True)

        tracker.capture_invocation("phase1", ["demo"], invocation_id, launcher_succeeded=True)

        phase = self.phase_state(self.state(), "phase1")
        self.assertTrue(phase["runtime_incomplete"])
        self.assertTrue(phase["usage_incomplete"])

    def test_missing_manifest_marks_failed_launcher_incomplete(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)

        tracker.capture_invocation("phase1", ["demo"], "f" * 32, launcher_succeeded=False)

        phase = self.phase_state(self.state(), "phase1")
        self.assertTrue(phase["runtime_incomplete"])
        self.assertTrue(phase["usage_incomplete"])

    def test_corrupt_manifest_marks_launcher_incomplete(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        invocation_id = "0" * 32
        path = self.root / INVOCATION_DIRNAME / f"{invocation_id}.json"
        path.parent.mkdir()
        path.write_text("{not json\n")

        tracker.capture_invocation("phase1", ["demo"], invocation_id, launcher_succeeded=True)

        phase = self.phase_state(self.state(), "phase1")
        self.assertTrue(phase["runtime_incomplete"])
        self.assertTrue(phase["usage_incomplete"])

    def test_unfinalized_manifest_is_not_accepted_as_complete(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        invocation_id = "a" * 32
        recorder = self.recorder("phase4a", invocation_id)
        recorder.start_target("demo", self.work_dir)
        recorder.finish_target("demo", True)

        tracker.capture_invocation("phase4a", ["demo"], invocation_id, launcher_succeeded=True)

        phase = self.phase_state(self.state(), "phase4a")
        self.assertFalse(phase["runtime_observed"])
        self.assertTrue(phase["runtime_incomplete"])
        self.assertTrue(phase["usage_incomplete"])

    def test_exceptional_finalize_revokes_provisional_target_success(self) -> None:
        invocation_id = "b" * 32
        recorder = self.recorder("phase1", invocation_id)
        recorder.start_target("demo", self.work_dir)
        recorder.finish_target("demo", True)

        recorder.finalize(False, outcomes_complete=False)

        path = self.root / INVOCATION_DIRNAME / f"{invocation_id}.json"
        document = json.loads(path.read_text())
        self.assertFalse(document["targets"]["demo"]["succeeded"])

    def test_invalid_recorder_path_has_no_directory_side_effect(self) -> None:
        invocation_id = "c" * 32
        unexpected = self.root / "unexpected" / f"{invocation_id}.json"

        with self.assertRaises(ValueError):
            ResourceInvocationRecorder(self.root, unexpected, "phase1", invocation_id)

        self.assertFalse(unexpected.parent.exists())
        self.assertFalse((self.root / INVOCATION_DIRNAME).exists())

    def test_manifest_owned_non_codex_rewrite_is_a_complete_new_invocation(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        usage_path = self.work_dir / "spec-repair.usage.json"
        for invocation_id, tokens, cached, cost in (
            ("d" * 32, 100, 80, 1.0),
            ("e" * 32, 50, 40, 0.5),
        ):
            recorder = self.recorder("phase4a", invocation_id)
            recorder.start_target("demo", self.work_dir)
            recorder.note_agent(self.work_dir, usage_path)
            recorder.finish_target("demo", True)
            recorder.finalize(True)
            self.write_json(
                "spec-repair.usage.json",
                _normalized(
                    session=invocation_id,
                    tokens=tokens,
                    cached=cached,
                    cost=cost,
                    agent="claude-code",
                ),
            )
            tracker.capture_invocation("phase4a", ["demo"], invocation_id, launcher_succeeded=True)

        phase = self.phase_state(self.state(), "phase4a")
        self.assertEqual(phase["total_tokens"], 150)
        self.assertEqual(phase["cached_input_tokens"], 120)
        self.assertEqual(phase["cost_usd"], 1.5)
        self.assertFalse(phase["usage_incomplete"])

    def test_runtime_is_cumulative_and_stale_active_time_is_not_guessed(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        tracker.start_phase("phase1", ["demo"])
        tracker.finish_phase("phase1", ["demo"], 65.2, succeeded=True)
        tracker.start_phase("phase2", ["demo"])

        resumed = self.tracker()
        resumed.initialize(resume=True)
        resumed.start_phase("phase1", ["demo"])
        resumed.finish_phase("phase1", ["demo"], 4.8, succeeded=True)

        phase1 = self.phase_state(self.state(), "phase1")
        phase2 = self.phase_state(self.state(), "phase2")
        self.assertEqual(phase1["runtime_seconds"], 70.0)
        self.assertFalse(phase1["runtime_incomplete"])
        self.assertTrue(phase2["runtime_incomplete"])
        self.assertIn("| Phase 1 | 1m 10s |", self.summary())
        self.assertIn("**Total (incomplete)**", self.summary())

    def test_interrupted_new_segment_hides_an_older_runtime_value(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        tracker.start_phase("phase1", ["demo"])
        tracker.finish_phase("phase1", ["demo"], 65, succeeded=True)
        tracker.start_phase("phase1", ["demo"])

        resumed = self.tracker()
        resumed.initialize(resume=True)

        self.assertIn("| Phase 1 | - |", self.summary())
        self.assertEqual(self.phase_state(self.state(), "phase1")["runtime_seconds"], 65.0)

    def test_skip_does_not_manufacture_zero_usage(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        tracker.skip_phase("phase2_5", ["demo"])
        tracker.complete_run()

        self.assertIn("| Phase 2.5 | - | - | - |", self.summary())
        self.assertIn("**Total (incomplete)**", self.summary())

    def test_skipped_phases_without_accounted_history_remain_partial(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        for definition in PHASES:
            tracker.skip_phase(definition.key, ["demo"])
        tracker.complete_run()

        self.assertIn("| **Total (incomplete)** | - | - | - |", self.summary())


class TestUsageCapture(ResourceSummaryCase):
    def test_resume_rejects_parent_traversal_in_source_checkpoint(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        outside = self.root / "outside-usage.json"
        outside.write_text(json.dumps(_normalized(session="outside", tokens=999, cached=0, cost=9.0)))
        state = self.state()
        sources = state["source_signatures"]
        assert isinstance(sources, dict)
        phase1 = sources["phase1"]
        assert isinstance(phase1, dict)
        phase1["../../outside-usage.json"] = "missing"
        (self.work_dir / STATE_FILENAME).write_text(json.dumps(state))

        resumed = self.tracker()
        resumed.initialize(resume=True)

        phase = self.phase_state(self.state(), "phase1")
        self.assertEqual(phase["total_tokens"], 0)
        self.assertEqual(phase["cost_usd"], 0.0)
        self.assertTrue(self.state()["history_incomplete"])
        self.assertNotIn("outside-usage.json", json.dumps(self.state()))

    def test_resume_rejects_absolute_checkpoint_path_without_disabling_target(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        outside = self.root / "absolute-usage.json"
        outside.write_text(json.dumps(_normalized(session="outside", tokens=999, cached=0, cost=9.0)))
        state = self.state()
        attempts = state["attempt_signatures"]
        assert isinstance(attempts, dict)
        phase1 = attempts["phase1"]
        assert isinstance(phase1, dict)
        phase1[str(outside)] = "missing"
        (self.work_dir / STATE_FILENAME).write_text(json.dumps(state))

        resumed = self.tracker()
        resumed.initialize(resume=True)

        self.assertTrue((self.work_dir / SUMMARY_FILENAME).is_file())
        self.assertTrue(self.state()["history_incomplete"])
        self.assertNotIn(str(outside), json.dumps(self.state()))

    def test_resume_rejects_noncanonical_alias_without_double_counting(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        self.write_json(
            "agent.usage.json",
            _normalized(session="canonical", tokens=100, cached=80, cost=1.0),
        )
        state = self.state()
        sources = state["source_signatures"]
        assert isinstance(sources, dict)
        phase1 = sources["phase1"]
        assert isinstance(phase1, dict)
        phase1["./agent.usage.json"] = "missing"
        (self.work_dir / STATE_FILENAME).write_text(json.dumps(state))

        resumed = self.tracker()
        resumed.initialize(resume=True)

        phase = self.phase_state(self.state(), "phase1")
        self.assertEqual(phase["total_tokens"], 100)
        self.assertEqual(phase["cost_usd"], 1.0)
        self.assertTrue(self.state()["history_incomplete"])

    def test_resume_rejects_dot_as_a_checkpoint_path(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        state = self.state()
        sources = state["source_signatures"]
        assert isinstance(sources, dict)
        phase1 = sources["phase1"]
        assert isinstance(phase1, dict)
        phase1["."] = "missing"
        (self.work_dir / STATE_FILENAME).write_text(json.dumps(state))

        resumed = self.tracker()
        resumed.initialize(resume=True)

        self.assertTrue(self.state()["history_incomplete"])
        self.assertNotIn('".": "missing"', json.dumps(self.state()))

    def test_resume_rejects_unrecognized_in_workdir_usage_path(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        self.write_json(
            "unrecognized.json",
            _normalized(session="injected", tokens=999, cached=0, cost=9.0),
        )
        state = self.state()
        sources = state["source_signatures"]
        assert isinstance(sources, dict)
        phase1 = sources["phase1"]
        assert isinstance(phase1, dict)
        phase1["unrecognized.json"] = "missing"
        (self.work_dir / STATE_FILENAME).write_text(json.dumps(state))

        resumed = self.tracker()
        resumed.initialize(resume=True)

        phase = self.phase_state(self.state(), "phase1")
        self.assertEqual(phase["total_tokens"], 0)
        self.assertEqual(phase["cost_usd"], 0.0)
        self.assertTrue(self.state()["history_incomplete"])

    def test_no_changed_sidecar_is_not_marked_partial_until_phase_finish(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        tracker.start_phase("phase1", ["demo"])

        tracker.capture_usage("phase1", ["demo"])
        self.assertFalse(self.phase_state(self.state(), "phase1")["usage_incomplete"])

        tracker.finish_phase("phase1", ["demo"], 1, succeeded=True)
        self.assertTrue(self.phase_state(self.state(), "phase1")["usage_incomplete"])

    def test_expected_invocation_without_a_changed_sidecar_is_partial(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        tracker.start_phase("phase1", ["demo"])
        self.write_json(
            "agent.usage.json",
            _normalized(session="main", tokens=100, cached=80, cost=1.0),
        )
        tracker.capture_usage("phase1", ["demo"], require_change=True)
        tracker.capture_usage("phase1", ["demo"], require_change=True)
        tracker.finish_phase("phase1", ["demo"], 1, succeeded=True)

        self.assertTrue(self.phase_state(self.state(), "phase1")["usage_incomplete"])
        self.assertIn("**Total (incomplete)**", self.summary())

    def test_failed_group_remains_partial_even_when_one_usage_record_exists(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        tracker.start_phase("phase4a", ["demo"])
        self.write_json(
            "bug-confirmation.usage.json",
            _normalized(session="partial-group", tokens=100, cached=80, cost=1.0),
        )
        tracker.capture_usage("phase4a", ["demo"], require_change=True)

        tracker.finish_phase("phase4a", ["demo"], 1, succeeded=False)

        self.assertTrue(self.phase_state(self.state(), "phase4a")["usage_incomplete"])
        self.assertIn("**Total (incomplete)**", self.summary())

    def test_normalized_usage_and_wall_time_are_rendered(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        tracker.start_phase("phase1", ["demo"])
        self.write_json(
            "agent.usage.json",
            _normalized(session="session-1", tokens=61_000_000, cached=58_900_000, cost=47.55),
        )
        tracker.capture_usage("phase1", ["demo"])
        tracker.finish_phase("phase1", ["demo"], 12_480, succeeded=True)

        text = self.summary()
        self.assertIn("| Phase 1 | 3h 28m | 61.0M total (58.9M cached) | $47.55 |", text)
        phase = self.phase_state(self.state(), "phase1")
        self.assertEqual(phase["total_tokens"], 61_000_000)
        self.assertEqual(phase["cached_input_tokens"], 58_900_000)

    def test_claude_model_usage_is_preferred_over_parent_usage(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        payload = {
            "session_id": "claude-session",
            "total_cost_usd": 3.5,
            "usage": {
                "input_tokens": 1,
                "cache_creation_input_tokens": 2,
                "cache_read_input_tokens": 3,
                "output_tokens": 4,
            },
            "model_usage": {
                "large": {
                    "inputTokens": 10,
                    "cacheCreationInputTokens": 20,
                    "cacheReadInputTokens": 30,
                    "outputTokens": 40,
                },
                "small": {
                    "inputTokens": 1,
                    "cacheCreationInputTokens": 2,
                    "cacheReadInputTokens": 3,
                    "outputTokens": 4,
                },
            },
        }
        self.write_json("agent.usage.json", payload)
        tracker.capture_usage("phase1", ["demo"])

        phase = self.phase_state(self.state(), "phase1")
        self.assertEqual(phase["total_tokens"], 110)
        self.assertEqual(phase["cached_input_tokens"], 33)
        self.assertEqual(phase["cost_usd"], 3.5)

    def test_claude_native_usage_is_the_fallback(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        self.write_json(
            "agent.usage.json",
            {
                "session_id": "claude-session",
                "total_cost_usd": 0.5,
                "usage": {
                    "input_tokens": 10,
                    "cache_creation_input_tokens": 20,
                    "cache_read_input_tokens": 30,
                    "output_tokens": 40,
                },
                "model_usage": {},
            },
        )
        tracker.capture_usage("phase1", ["demo"])

        phase = self.phase_state(self.state(), "phase1")
        self.assertEqual(phase["total_tokens"], 100)
        self.assertEqual(phase["cached_input_tokens"], 30)

    def test_retry_archive_is_not_counted_and_marks_total_incomplete(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        self.write_json(
            "agent.usage.attempt-1.json",
            _normalized(session="same-session", tokens=100, cached=80, cost=1.0),
        )
        self.write_json(
            "agent.usage.json",
            _normalized(session="same-session", tokens=150, cached=120, cost=1.5),
        )
        tracker.capture_usage("phase1", ["demo"])

        phase = self.phase_state(self.state(), "phase1")
        self.assertEqual(phase["total_tokens"], 150)
        self.assertEqual(phase["cost_usd"], 1.5)
        self.assertTrue(phase["usage_incomplete"])
        self.assertIn("**Total (incomplete)**", self.summary())

    def test_same_session_uses_cumulative_delta_across_resume(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        sidecar = self.write_json(
            "agent.usage.json",
            _normalized(session="same-session", tokens=100, cached=80, cost=1.0),
        )
        tracker.capture_usage("phase1", ["demo"])

        resumed = self.tracker()
        resumed.initialize(resume=True)
        sidecar.write_text(json.dumps(_normalized(session="same-session", tokens=150, cached=120, cost=1.5)) + "\n")
        resumed.capture_usage("phase1", ["demo"])
        resumed.capture_usage("phase1", ["demo"])

        phase = self.phase_state(self.state(), "phase1")
        self.assertEqual(phase["total_tokens"], 150)
        self.assertEqual(phase["cached_input_tokens"], 120)
        self.assertEqual(phase["cost_usd"], 1.5)

    def test_new_session_on_the_same_source_is_added(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        sidecar = self.write_json(
            "agent.usage.json",
            _normalized(session="first", tokens=100, cached=80, cost=1.0),
        )
        tracker.capture_usage("phase1", ["demo"])
        sidecar.write_text(json.dumps(_normalized(session="second", tokens=50, cached=40, cost=0.5)) + "\n")
        tracker.capture_usage("phase1", ["demo"])

        phase = self.phase_state(self.state(), "phase1")
        self.assertEqual(phase["total_tokens"], 150)
        self.assertEqual(phase["cached_input_tokens"], 120)
        self.assertEqual(phase["cost_usd"], 1.5)

    def test_anonymous_rewrite_adds_observed_values_but_marks_them_partial(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        sidecar = self.write_json(
            "agent.usage.json",
            _normalized(session=None, tokens=100, cached=80, cost=1.0),
        )
        tracker.capture_usage("phase1", ["demo"])
        sidecar.write_text(json.dumps(_normalized(session=None, tokens=150, cached=120, cost=1.5)) + "\n")
        tracker.capture_usage("phase1", ["demo"])

        phase = self.phase_state(self.state(), "phase1")
        self.assertEqual(phase["total_tokens"], 250)
        self.assertEqual(phase["cached_input_tokens"], 200)
        self.assertEqual(phase["cost_usd"], 2.5)
        self.assertTrue(phase["usage_incomplete"])

    def test_partial_normalized_usage_keeps_values_and_marks_incomplete(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        self.write_json(
            "agent.usage.json",
            _normalized(
                session="partial",
                tokens=420,
                cached=200,
                cost=1.5,
                agent="pi",
                complete=False,
            ),
        )
        tracker.capture_usage("phase1", ["demo"])

        self.assertIn("420 total (200 cached)", self.summary())
        self.assertTrue(self.phase_state(self.state(), "phase1")["usage_incomplete"])

    def test_missing_cost_is_a_dash_while_tokens_remain_visible(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        self.write_json(
            "agent.usage.json",
            _normalized(session="no-cost", tokens=420, cached=200, cost=None),
        )
        tracker.capture_usage("phase1", ["demo"])

        self.assertIn("| Phase 1 | - | 420 total (200 cached) | - |", self.summary())

    def test_parallel_confirmation_turns_are_counted_but_unlisted_files_are_not(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        self.write_json(
            "confirmation/MC-1/turn01_A.usage.json",
            _normalized(session="turn-a", tokens=100, cached=90, cost=1.0),
        )
        self.write_json(
            "confirmation/MC-1/not-a-turn.usage.json",
            _normalized(session="fake", tokens=9_999, cached=9_999, cost=99.0),
        )
        self.write_json(
            "fake.usage.json",
            _normalized(session="fake-root", tokens=9_999, cached=9_999, cost=99.0),
        )
        tracker.capture_usage("phase4a", ["demo"])

        phase = self.phase_state(self.state(), "phase4a")
        self.assertEqual(phase["total_tokens"], 100)
        self.assertEqual(phase["cost_usd"], 1.0)

    def test_symlinked_canonical_sidecar_is_not_followed(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        outside = self.root / "outside.json"
        outside.write_text(json.dumps(_normalized(session="outside", tokens=999, cached=900, cost=9.0)))
        (self.work_dir / "agent.usage.json").symlink_to(outside)
        tracker.capture_usage("phase1", ["demo"])

        phase = self.phase_state(self.state(), "phase1")
        self.assertFalse(phase["tokens_observed"])
        self.assertIn("| Phase 1 | - | - | - |", self.summary())


class TestCompleteSummary(ResourceSummaryCase):
    def test_complete_run_drops_incomplete_only_when_every_metric_is_present(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        source_by_phase = {
            "phase1": "agent.usage.json",
            "phase2": "spec-gen.usage.json",
            "phase2_5": "harness-gen.usage.json",
            "phase3": "spec-validation.usage.json",
            "phase4a": "bug-confirmation.usage.json",
            "phase4b": "bug-classification.usage.json",
        }
        for index, definition in enumerate(PHASES, 1):
            tracker.start_phase(definition.key, ["demo"])
            self.write_json(
                source_by_phase[definition.key],
                _normalized(session=f"session-{index}", tokens=100, cached=80, cost=1.0),
            )
            tracker.capture_usage(definition.key, ["demo"])
            tracker.finish_phase(definition.key, ["demo"], 10, succeeded=True)
        tracker.complete_run()

        text = self.summary()
        self.assertIn("| **Total** | 1m 0s | 600 total (480 cached) | $6.00 |", text)
        self.assertNotIn("Total (incomplete)", text)

    def test_fresh_initialize_resets_an_old_legacy_checkpoint(self) -> None:
        first = self.tracker()
        first.initialize(resume=False)
        self.write_json(
            "agent.usage.json",
            _normalized(session="old", tokens=100, cached=80, cost=1.0),
        )
        first.capture_usage("phase1", ["demo"])

        fresh = self.tracker()
        fresh.initialize(resume=False)

        self.assertIn("| Phase 1 | - | - | - |", self.summary())
        self.assertEqual(self.phase_state(self.state(), "phase1")["total_tokens"], 0)

    def test_atomic_refresh_leaves_no_temporary_files(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        tracker.refresh()

        leftovers = [path.name for path in self.work_dir.iterdir() if path.name.endswith(".tmp")]
        self.assertEqual(leftovers, [])

    @unittest.skipUnless(hasattr(os, "symlink"), "symlinks unavailable")
    def test_symlinked_summary_destination_is_rejected_not_replaced(self) -> None:
        self.work_dir.mkdir(parents=True)
        outside = self.root / "outside-summary.md"
        outside.write_text("keep\n")
        summary = self.work_dir / SUMMARY_FILENAME
        summary.symlink_to(outside)
        tracker = self.tracker()

        tracker.initialize(resume=False)

        self.assertTrue(summary.is_symlink())
        self.assertEqual(outside.read_text(), "keep\n")

    @unittest.skipUnless(hasattr(os, "symlink"), "symlinks unavailable")
    def test_symlinked_state_destination_is_rejected_not_replaced(self) -> None:
        self.work_dir.mkdir(parents=True)
        outside = self.root / "outside-state.json"
        outside.write_text("keep\n")
        state = self.work_dir / STATE_FILENAME
        state.symlink_to(outside)
        tracker = self.tracker()

        tracker.initialize(resume=False)

        self.assertTrue(state.is_symlink())
        self.assertEqual(outside.read_text(), "keep\n")

    def test_directory_summary_destination_is_rejected_not_replaced(self) -> None:
        (self.work_dir / SUMMARY_FILENAME).mkdir(parents=True)
        tracker = self.tracker()

        tracker.initialize(resume=False)

        self.assertTrue((self.work_dir / SUMMARY_FILENAME).is_dir())

    @unittest.skipUnless(hasattr(os, "symlink"), "symlinks unavailable")
    def test_symlinked_work_directory_is_rejected_without_touching_target(self) -> None:
        outside = self.root / "outside"
        outside.mkdir()
        linked = self.root / "linked"
        linked.symlink_to(outside, target_is_directory=True)
        tracker = ResourceSummaryTracker(
            {"demo": linked},
            output_root=self.root,
            maximum_parallelism="1",
            tlc_memory_limit="8G",
            tlc_worker_limit="4",
        )

        tracker.initialize(resume=False)

        self.assertFalse((outside / STATE_FILENAME).exists())
        self.assertFalse((outside / SUMMARY_FILENAME).exists())

    @unittest.skipUnless(hasattr(os, "symlink"), "symlinks unavailable")
    def test_symlinked_target_ancestor_cannot_escape_the_output_root(self) -> None:
        outside = self.root / "outside"
        outside.mkdir()
        target = self.root / "run" / "demo"
        target.parent.mkdir()
        target.symlink_to(outside, target_is_directory=True)
        work_dir = target / ".specula-output"
        tracker = ResourceSummaryTracker(
            {"demo": work_dir},
            output_root=self.root / "run",
            maximum_parallelism="1",
            tlc_memory_limit="8G",
            tlc_worker_limit="4",
        )

        tracker.initialize(resume=False)

        self.assertFalse((outside / ".specula-output" / SUMMARY_FILENAME).exists())
        self.assertFalse((outside / ".specula-output" / STATE_FILENAME).exists())


if __name__ == "__main__":
    unittest.main()
