"""Focused tests for target-local resource summary records."""

from __future__ import annotations

import json
import os
import tempfile
import unittest
from pathlib import Path
from typing import cast
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


def _claude(*, session: str, tokens: tuple[int, int, int, int], cost: float) -> dict[str, object]:
    input_tokens, cache_write, cached, output = tokens
    return {
        "session_id": session,
        "total_cost_usd": cost,
        "usage": {
            "input_tokens": input_tokens,
            "cache_creation_input_tokens": cache_write,
            "cache_read_input_tokens": cached,
            "output_tokens": output,
        },
        "model_usage": {},
    }


class ResourceSummaryCase(unittest.TestCase):
    def setUp(self) -> None:
        self._temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self._temporary.cleanup)
        self.root = Path(self._temporary.name).resolve()
        self.work_dir = self.target_dir("demo")

    def target_dir(self, name: str) -> Path:
        return self.root / name / ".specula-output"

    def tracker(self, targets: dict[str, Path] | None = None) -> ResourceSummaryTracker:
        return ResourceSummaryTracker(
            targets or {"demo": self.work_dir},
            output_root=self.root,
            maximum_parallelism="1",
            tlc_memory_limit="8G",
            tlc_worker_limit="4",
        )

    def recorder(self, phase: str, invocation_id: str) -> ResourceInvocationRecorder:
        return ResourceInvocationRecorder(self.root, phase, invocation_id)

    @staticmethod
    def record_path(work_dir: Path, invocation_id: str) -> Path:
        return work_dir / INVOCATION_DIRNAME / f"{invocation_id}.json"

    @staticmethod
    def write_json(work_dir: Path, relative: str, payload: object) -> Path:
        path = work_dir / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(payload) + "\n")
        return path

    @staticmethod
    def state(work_dir: Path) -> dict[str, object]:
        value = json.loads((work_dir / STATE_FILENAME).read_text())
        assert isinstance(value, dict)
        return value

    @staticmethod
    def phase_state(state: dict[str, object], phase: str) -> dict[str, object]:
        phases = state["phases"]
        assert isinstance(phases, dict)
        value = phases[phase]
        assert isinstance(value, dict)
        return value

    @staticmethod
    def summary(work_dir: Path) -> str:
        return (work_dir / SUMMARY_FILENAME).read_text()


class TestTargetLocalAccounting(ResourceSummaryCase):
    def test_serial_targets_receive_only_their_own_runtime(self) -> None:
        first_dir = self.target_dir("first")
        second_dir = self.target_dir("second")
        tracker = self.tracker({"first": first_dir, "second": second_dir})
        tracker.initialize(resume=False)
        invocation_id = "1" * 32
        recorder = self.recorder("phase1", invocation_id)

        with mock.patch(
            "specula.resource_summary.time.monotonic",
            side_effect=[0.0, 10.0, 10.0, 30.0],
        ):
            recorder.start_target("first", first_dir)
            recorder.finish_target("first")
            recorder.start_target("second", second_dir)
            recorder.finish_target("second")

        tracker.capture_invocation("phase1", ["first", "second"], invocation_id)

        first = self.phase_state(self.state(first_dir), "phase1")
        second = self.phase_state(self.state(second_dir), "phase1")
        self.assertEqual(first["runtime_seconds"], 10.0)
        self.assertEqual(second["runtime_seconds"], 20.0)
        self.assertFalse(first["runtime_incomplete"])
        self.assertFalse(second["runtime_incomplete"])

    def test_interrupted_parallel_target_does_not_degrade_completed_sibling(self) -> None:
        first_dir = self.target_dir("first")
        second_dir = self.target_dir("second")
        tracker = self.tracker({"first": first_dir, "second": second_dir})
        tracker.initialize(resume=False)
        invocation_id = "2" * 32
        recorder = self.recorder("phase2_5", invocation_id)

        with mock.patch(
            "specula.resource_summary.time.monotonic",
            side_effect=[0.0, 0.0, 5.0],
        ):
            recorder.start_target("first", first_dir)
            recorder.start_target("second", second_dir)
            recorder.finish_target("first")

        tracker.capture_invocation("phase2_5", ["first", "second"], invocation_id)

        first = self.phase_state(self.state(first_dir), "phase2_5")
        second = self.phase_state(self.state(second_dir), "phase2_5")
        self.assertEqual(first["runtime_seconds"], 5.0)
        self.assertTrue(first["tokens_observed"])
        self.assertTrue(first["cost_observed"])
        self.assertFalse(first["runtime_incomplete"])
        self.assertFalse(first["usage_incomplete"])
        self.assertFalse(second["runtime_observed"])
        self.assertTrue(second["runtime_incomplete"])
        self.assertTrue(second["usage_incomplete"])

    def test_retry_runtime_is_cumulative_but_backoff_is_not_counted(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        invocation_id = "3" * 32
        recorder = self.recorder("phase3", invocation_id)
        with mock.patch(
            "specula.resource_summary.time.monotonic",
            side_effect=[0.0, 3.0, 100.0, 104.0],
        ):
            recorder.start_target("demo", self.work_dir)
            recorder.pause_target("demo")
            recorder.start_target("demo", self.work_dir)
            recorder.finish_target("demo")
        tracker.capture_invocation("phase3", ["demo"], invocation_id)

        phase = self.phase_state(self.state(self.work_dir), "phase3")
        self.assertEqual(phase["runtime_seconds"], 7.0)
        self.assertTrue(phase["tokens_observed"])
        self.assertTrue(phase["cost_observed"])

    def test_zero_agent_invocation_is_known_zero(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        invocation_id = "5" * 32
        recorder = self.recorder("phase4a", invocation_id)
        with mock.patch("specula.resource_summary.time.monotonic", side_effect=[0.0, 1.0]):
            recorder.start_target("demo", self.work_dir)
            recorder.finish_target("demo")

        tracker.capture_invocation("phase4a", ["demo"], invocation_id)

        phase = self.phase_state(self.state(self.work_dir), "phase4a")
        self.assertEqual(phase["total_tokens"], 0)
        self.assertEqual(phase["cost_usd"], 0.0)
        self.assertTrue(phase["tokens_observed"])
        self.assertTrue(phase["cost_observed"])
        self.assertFalse(phase["usage_incomplete"])

    def test_unstarted_reused_target_has_no_record_and_keeps_completed_state(self) -> None:
        active_dir = self.target_dir("active")
        reused_dir = self.target_dir("reused")
        targets = {"active": active_dir, "reused": reused_dir}
        tracker = self.tracker(targets)
        tracker.initialize(resume=False)
        tracker.complete_run()
        reused_before = self.state(reused_dir)

        invocation_id = "6" * 32
        recorder = self.recorder("phase1", invocation_id)
        self.assertFalse((active_dir / INVOCATION_DIRNAME).exists())
        self.assertFalse((reused_dir / INVOCATION_DIRNAME).exists())
        with mock.patch("specula.resource_summary.time.monotonic", return_value=0.0):
            recorder.start_target("active", active_dir)

        resumed = self.tracker(targets)
        resumed.initialize(resume=True)

        self.assertTrue(self.record_path(active_dir, invocation_id).is_file())
        self.assertFalse((reused_dir / INVOCATION_DIRNAME).exists())
        self.assertEqual(self.state(reused_dir), reused_before)

    def test_missing_record_is_a_no_op(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        tracker.complete_run()
        before = self.state(self.work_dir)

        tracker.capture_invocation("phase1", ["demo"], "7" * 32)

        self.assertEqual(self.state(self.work_dir), before)


class TestRecoveryAndSnapshots(ResourceSummaryCase):
    def test_resume_recovers_completed_local_record_once(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        invocation_id = "8" * 32
        recorder = self.recorder("phase1", invocation_id)
        with mock.patch("specula.resource_summary.time.monotonic", side_effect=[0.0, 9.0]):
            recorder.start_target("demo", self.work_dir)
            recorder.finish_target("demo")

        resumed = self.tracker()
        resumed.initialize(resume=True)
        first_state = self.state(self.work_dir)
        self.assertEqual(self.phase_state(first_state, "phase1")["runtime_seconds"], 9.0)

        resumed_again = self.tracker()
        resumed_again.initialize(resume=True)
        second_state = self.state(self.work_dir)
        self.assertEqual(self.phase_state(second_state, "phase1")["runtime_seconds"], 9.0)

    def test_active_record_degrades_only_its_owner_on_resume(self) -> None:
        active_dir = self.target_dir("active")
        stable_dir = self.target_dir("stable")
        targets = {"active": active_dir, "stable": stable_dir}
        tracker = self.tracker(targets)
        tracker.initialize(resume=False)
        tracker.complete_run()
        stable_before = self.state(stable_dir)
        invocation_id = "9" * 32
        recorder = self.recorder("phase4b", invocation_id)
        with mock.patch("specula.resource_summary.time.monotonic", return_value=0.0):
            recorder.start_target("active", active_dir)

        resumed = self.tracker(targets)
        resumed.initialize(resume=True)

        active = self.state(active_dir)
        active_phase = self.phase_state(active, "phase4b")
        self.assertTrue(active["history_incomplete"])
        self.assertFalse(active["run_complete"])
        self.assertTrue(active_phase["runtime_incomplete"])
        self.assertTrue(active_phase["usage_incomplete"])
        self.assertEqual(self.state(stable_dir), stable_before)

    def test_corrupt_record_degrades_only_its_owner_on_resume(self) -> None:
        corrupt_dir = self.target_dir("corrupt")
        stable_dir = self.target_dir("stable")
        targets = {"corrupt": corrupt_dir, "stable": stable_dir}
        tracker = self.tracker(targets)
        tracker.initialize(resume=False)
        tracker.complete_run()
        stable_before = self.state(stable_dir)
        path = self.record_path(corrupt_dir, "a" * 32)
        path.parent.mkdir(parents=True)
        path.write_text("{not-json\n")

        resumed = self.tracker(targets)
        resumed.initialize(resume=True)

        corrupt = self.state(corrupt_dir)
        self.assertTrue(corrupt["history_incomplete"])
        self.assertFalse(corrupt["run_complete"])
        self.assertEqual(self.state(stable_dir), stable_before)

    def test_completed_record_uses_immutable_usage_snapshot(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        sidecar = self.work_dir / "agent.usage.json"
        invocation_id = "b" * 32
        recorder = self.recorder("phase1", invocation_id)
        with mock.patch("specula.resource_summary.time.monotonic", side_effect=[0.0, 2.0]):
            recorder.start_target("demo", self.work_dir)
            recorder.note_agent(self.work_dir, sidecar)
            self.write_json(
                self.work_dir,
                "agent.usage.json",
                _normalized(session="snapshot", tokens=100, cached=80, cost=1.0),
            )
            recorder.finish_target("demo")
        sidecar.write_text(json.dumps(_normalized(session="snapshot", tokens=999, cached=900, cost=9.0)) + "\n")

        tracker.capture_invocation("phase1", ["demo"], invocation_id)

        phase = self.phase_state(self.state(self.work_dir), "phase1")
        self.assertEqual(phase["total_tokens"], 100)
        self.assertEqual(phase["cached_input_tokens"], 80)
        self.assertEqual(phase["cost_usd"], 1.0)
        record = json.loads(self.record_path(self.work_dir, invocation_id).read_text())
        self.assertEqual(record["usage"][0]["total_tokens"], 100)

    def test_missing_sidecar_keeps_runtime_but_marks_usage_incomplete(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        invocation_id = "c" * 32
        recorder = self.recorder("phase1", invocation_id)
        missing = self.work_dir / "agent.usage.json"
        with mock.patch("specula.resource_summary.time.monotonic", side_effect=[0.0, 2.0]):
            recorder.start_target("demo", self.work_dir)
            recorder.note_agent(self.work_dir, missing)
            recorder.finish_target("demo")

        tracker.capture_invocation("phase1", ["demo"], invocation_id)

        phase = self.phase_state(self.state(self.work_dir), "phase1")
        self.assertEqual(phase["runtime_seconds"], 2.0)
        self.assertTrue(phase["runtime_observed"])
        self.assertFalse(phase["tokens_observed"])
        self.assertFalse(phase["cost_observed"])
        self.assertTrue(phase["usage_incomplete"])

    def test_stale_sidecar_is_not_reused_when_the_next_agent_writes_nothing(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        sidecar = self.work_dir / "agent.usage.json"

        first_id = "bc" * 16
        first = self.recorder("phase1", first_id)
        with mock.patch("specula.resource_summary.time.monotonic", side_effect=[0.0, 1.0]):
            first.start_target("demo", self.work_dir)
            first.note_agent(self.work_dir, sidecar)
            self.write_json(
                self.work_dir,
                "agent.usage.json",
                _normalized(session=None, tokens=100, cached=80, cost=1.0, agent="pi"),
            )
            first.finish_target("demo")
        tracker.capture_invocation("phase1", ["demo"], first_id)

        second_id = "bd" * 16
        second = self.recorder("phase1", second_id)
        with mock.patch("specula.resource_summary.time.monotonic", side_effect=[2.0, 3.0]):
            second.start_target("demo", self.work_dir)
            second.note_agent(self.work_dir, sidecar)
            self.assertFalse(sidecar.exists())
            second.finish_target("demo")
        tracker.capture_invocation("phase1", ["demo"], second_id)

        phase = self.phase_state(self.state(self.work_dir), "phase1")
        self.assertEqual(phase["total_tokens"], 100)
        self.assertEqual(phase["cost_usd"], 1.0)
        self.assertTrue(phase["usage_incomplete"])

    def test_failed_stale_sidecar_cleanup_is_incomplete_and_ignored(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        sidecar = self.write_json(
            self.work_dir,
            "agent.usage.json",
            _normalized(session=None, tokens=999, cached=900, cost=9.0, agent="pi"),
        )
        invocation_id = "be" * 16
        recorder = self.recorder("phase1", invocation_id)
        with mock.patch("specula.resource_summary.time.monotonic", side_effect=[0.0, 1.0]):
            recorder.start_target("demo", self.work_dir)
            with (
                mock.patch.object(Path, "unlink", autospec=True, side_effect=PermissionError("denied")),
                self.assertRaisesRegex(OSError, "cannot clear stale resource usage"),
            ):
                recorder.note_agent(self.work_dir, sidecar)
            recorder.finish_target("demo")
        tracker.capture_invocation("phase1", ["demo"], invocation_id)

        phase = self.phase_state(self.state(self.work_dir), "phase1")
        self.assertFalse(phase["tokens_observed"])
        self.assertFalse(phase["cost_observed"])
        self.assertTrue(phase["usage_incomplete"])

    def test_rejected_usage_path_cannot_be_reported_as_known_zero(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        invocation_id = "cd" * 16
        recorder = self.recorder("phase1", invocation_id)
        with mock.patch("specula.resource_summary.time.monotonic", side_effect=[0.0, 2.0]):
            recorder.start_target("demo", self.work_dir)
            with self.assertRaises(ValueError):
                recorder.note_agent(self.work_dir, self.work_dir / "unexpected.usage.json")
            recorder.finish_target("demo")

        tracker.capture_invocation("phase1", ["demo"], invocation_id)

        phase = self.phase_state(self.state(self.work_dir), "phase1")
        self.assertFalse(phase["tokens_observed"])
        self.assertFalse(phase["cost_observed"])
        self.assertTrue(phase["usage_incomplete"])

    def test_partial_snapshot_keeps_available_values_and_marks_incomplete(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        sidecar = self.work_dir / "agent.usage.json"
        invocation_id = "d" * 32
        recorder = self.recorder("phase1", invocation_id)
        with mock.patch("specula.resource_summary.time.monotonic", side_effect=[0.0, 1.0]):
            recorder.start_target("demo", self.work_dir)
            recorder.note_agent(self.work_dir, sidecar)
            self.write_json(
                self.work_dir,
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
            recorder.finish_target("demo")

        tracker.capture_invocation("phase1", ["demo"], invocation_id)

        phase = self.phase_state(self.state(self.work_dir), "phase1")
        self.assertEqual(phase["total_tokens"], 420)
        self.assertEqual(phase["cost_usd"], 1.5)
        self.assertTrue(phase["usage_incomplete"])
        self.assertIn("420 total (200 cached)", self.summary(self.work_dir))

    def test_resume_does_not_guess_usage_from_orphaned_sidecar(self) -> None:
        self.write_json(
            self.work_dir,
            "agent.usage.json",
            _normalized(session="orphaned", tokens=999, cached=900, cost=9.0),
        )

        tracker = self.tracker()
        tracker.initialize(resume=True)

        state = self.state(self.work_dir)
        phase = self.phase_state(state, "phase1")
        self.assertTrue(state["history_incomplete"])
        self.assertFalse(phase["tokens_observed"])
        self.assertFalse(phase["cost_observed"])


class TestUsageParsingAndRendering(ResourceSummaryCase):
    def test_normalized_usage_and_wall_time_are_rendered(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        sidecar = self.work_dir / "agent.usage.json"
        payload = _normalized(
            session="session-1",
            tokens=61_000_000,
            cached=58_900_000,
            cost=47.55,
        )
        invocation_id = "e" * 32
        recorder = self.recorder("phase1", invocation_id)
        with mock.patch("specula.resource_summary.time.monotonic", side_effect=[0.0, 12_480.0]):
            recorder.start_target("demo", self.work_dir)
            recorder.note_agent(self.work_dir, sidecar)
            self.write_json(self.work_dir, "agent.usage.json", payload)
            recorder.finish_target("demo")

        tracker.capture_invocation("phase1", ["demo"], invocation_id)

        self.assertIn(
            "| Phase 1 | 3h 28m | 61.0M total (58.9M cached) | $47.55 |",
            self.summary(self.work_dir),
        )

    def test_claude_model_usage_is_preferred_over_parent_usage(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        sidecar = self.work_dir / "agent.usage.json"
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
        invocation_id = "f" * 32
        recorder = self.recorder("phase1", invocation_id)
        with mock.patch("specula.resource_summary.time.monotonic", side_effect=[0.0, 1.0]):
            recorder.start_target("demo", self.work_dir)
            recorder.note_agent(self.work_dir, sidecar)
            self.write_json(self.work_dir, "agent.usage.json", payload)
            recorder.finish_target("demo")

        tracker.capture_invocation("phase1", ["demo"], invocation_id)

        phase = self.phase_state(self.state(self.work_dir), "phase1")
        self.assertEqual(phase["total_tokens"], 110)
        self.assertEqual(phase["cached_input_tokens"], 33)
        self.assertEqual(phase["cost_usd"], 3.5)

    def test_claude_native_usage_is_the_fallback(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        sidecar = self.work_dir / "agent.usage.json"
        payload = {
            "session_id": "claude-session",
            "total_cost_usd": 0.5,
            "usage": {
                "input_tokens": 10,
                "cache_creation_input_tokens": 20,
                "cache_read_input_tokens": 30,
                "output_tokens": 40,
            },
            "model_usage": {},
        }
        invocation_id = "0" * 32
        recorder = self.recorder("phase1", invocation_id)
        with mock.patch("specula.resource_summary.time.monotonic", side_effect=[0.0, 1.0]):
            recorder.start_target("demo", self.work_dir)
            recorder.note_agent(self.work_dir, sidecar)
            self.write_json(self.work_dir, "agent.usage.json", payload)
            recorder.finish_target("demo")

        tracker.capture_invocation("phase1", ["demo"], invocation_id)

        phase = self.phase_state(self.state(self.work_dir), "phase1")
        self.assertEqual(phase["total_tokens"], 100)
        self.assertEqual(phase["cached_input_tokens"], 30)
        self.assertEqual(phase["cost_usd"], 0.5)

    def test_codex_cumulative_session_adds_only_the_delta(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        sidecar = self.work_dir / "agent.usage.json"
        first_id = "1a" * 16
        first = self.recorder("phase1", first_id)
        with mock.patch("specula.resource_summary.time.monotonic", side_effect=[0.0, 1.0]):
            first.start_target("demo", self.work_dir)
            first.note_agent(self.work_dir, sidecar)
            self.write_json(
                self.work_dir,
                "agent.usage.json",
                _normalized(session="same-session", tokens=100, cached=80, cost=1.0),
            )
            first.finish_target("demo")
        tracker.capture_invocation("phase1", ["demo"], first_id)

        second_id = "2b" * 16
        second = self.recorder("phase1", second_id)
        with mock.patch("specula.resource_summary.time.monotonic", side_effect=[2.0, 3.0]):
            second.start_target("demo", self.work_dir)
            second.note_agent(self.work_dir, sidecar)
            self.write_json(
                self.work_dir,
                "agent.usage.json",
                _normalized(session="same-session", tokens=150, cached=120, cost=1.5),
            )
            second.finish_target("demo")
        tracker.capture_invocation("phase1", ["demo"], second_id)

        phase = self.phase_state(self.state(self.work_dir), "phase1")
        self.assertEqual(phase["total_tokens"], 150)
        self.assertEqual(phase["cached_input_tokens"], 120)
        self.assertEqual(phase["cost_usd"], 1.5)

    def test_claude_retry_adds_archived_invocation_usage(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        sidecar = self.work_dir / "agent.usage.json"
        archived = self.work_dir / "agent.usage.attempt-1.json"
        invocation_id = "2c" * 16
        recorder = self.recorder("phase1", invocation_id)
        with mock.patch("specula.resource_summary.time.monotonic", side_effect=[0.0, 1.0]):
            recorder.start_target("demo", self.work_dir)
            recorder.note_agent(self.work_dir, sidecar, attempt=1)
            self.write_json(
                self.work_dir,
                "agent.usage.json",
                _claude(session="claude-retry", tokens=(400, 100, 200, 40), cost=0.001784),
            )
            sidecar.replace(archived)
            recorder.note_agent(
                self.work_dir,
                sidecar,
                attempt=2,
                archived_usage_path=archived,
            )
            self.write_json(
                self.work_dir,
                "agent.usage.json",
                _claude(session="claude-retry", tokens=(100, 50, 70, 30), cost=0.001430),
            )
            recorder.finish_target("demo")
        tracker.capture_invocation("phase1", ["demo"], invocation_id)

        phase = self.phase_state(self.state(self.work_dir), "phase1")
        self.assertEqual(phase["total_tokens"], 990)
        self.assertEqual(phase["cached_input_tokens"], 270)
        self.assertAlmostEqual(cast(float, phase["cost_usd"]), 0.003214)
        self.assertFalse(phase["usage_incomplete"])
        record = json.loads(self.record_path(self.work_dir, invocation_id).read_text())
        self.assertEqual(
            [entry["path"] for entry in record["usage"]],
            ["agent.usage.attempt-1.json", "agent.usage.json"],
        )

    def test_codex_retry_uses_delta_across_archived_snapshot(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        sidecar = self.work_dir / "agent.usage.json"
        archived = self.work_dir / "agent.usage.attempt-1.json"
        invocation_id = "2d" * 16
        recorder = self.recorder("phase1", invocation_id)
        with mock.patch("specula.resource_summary.time.monotonic", side_effect=[0.0, 1.0]):
            recorder.start_target("demo", self.work_dir)
            recorder.note_agent(self.work_dir, sidecar, attempt=1)
            self.write_json(
                self.work_dir,
                "agent.usage.json",
                _normalized(session="codex-retry", tokens=740, cached=200, cost=0.001784),
            )
            sidecar.replace(archived)
            recorder.note_agent(
                self.work_dir,
                sidecar,
                attempt=2,
                archived_usage_path=archived,
            )
            self.write_json(
                self.work_dir,
                "agent.usage.json",
                _normalized(session="codex-retry", tokens=990, cached=270, cost=0.003214),
            )
            recorder.finish_target("demo")
        tracker.capture_invocation("phase1", ["demo"], invocation_id)

        phase = self.phase_state(self.state(self.work_dir), "phase1")
        self.assertEqual(phase["total_tokens"], 990)
        self.assertEqual(phase["cached_input_tokens"], 270)
        self.assertAlmostEqual(cast(float, phase["cost_usd"]), 0.003214)
        self.assertFalse(phase["usage_incomplete"])

    def test_unknown_retry_keeps_latest_snapshot_and_marks_incomplete(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        sidecar = self.work_dir / "agent.usage.json"
        archived = self.work_dir / "agent.usage.attempt-1.json"
        invocation_id = "31" * 16
        recorder = self.recorder("phase1", invocation_id)
        with mock.patch("specula.resource_summary.time.monotonic", side_effect=[0.0, 1.0]):
            recorder.start_target("demo", self.work_dir)
            recorder.note_agent(self.work_dir, sidecar, attempt=1)
            self.write_json(
                self.work_dir,
                "agent.usage.json",
                _normalized(
                    session="opencode-retry",
                    tokens=740,
                    cached=200,
                    cost=0.001784,
                    agent="opencode",
                ),
            )
            sidecar.replace(archived)
            recorder.note_agent(
                self.work_dir,
                sidecar,
                attempt=2,
                archived_usage_path=archived,
            )
            self.write_json(
                self.work_dir,
                "agent.usage.json",
                _normalized(
                    session="opencode-retry",
                    tokens=250,
                    cached=70,
                    cost=0.001430,
                    agent="opencode",
                ),
            )
            recorder.finish_target("demo")
        tracker.capture_invocation("phase1", ["demo"], invocation_id)

        phase = self.phase_state(self.state(self.work_dir), "phase1")
        self.assertEqual(phase["total_tokens"], 250)
        self.assertEqual(phase["cached_input_tokens"], 70)
        self.assertAlmostEqual(cast(float, phase["cost_usd"]), 0.001430)
        self.assertTrue(phase["tokens_observed"])
        self.assertTrue(phase["cost_observed"])
        self.assertTrue(phase["usage_incomplete"])
        record = json.loads(self.record_path(self.work_dir, invocation_id).read_text())
        self.assertFalse(record["usage_complete"])
        self.assertEqual(
            [entry["path"] for entry in record["usage"]],
            ["agent.usage.attempt-1.json", "agent.usage.json"],
        )

    def test_manual_resume_does_not_recount_prior_claude_archive(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        sidecar = self.work_dir / "agent.usage.json"
        archived = self.work_dir / "agent.usage.attempt-1.json"

        first_id = "2e" * 16
        first = self.recorder("phase1", first_id)
        with mock.patch("specula.resource_summary.time.monotonic", side_effect=[0.0, 1.0]):
            first.start_target("demo", self.work_dir)
            first.note_agent(self.work_dir, sidecar, attempt=1)
            self.write_json(
                self.work_dir,
                "agent.usage.json",
                _claude(session="claude-resume", tokens=(400, 100, 200, 40), cost=0.001784),
            )
            first.finish_target("demo")
        tracker.capture_invocation("phase1", ["demo"], first_id)
        sidecar.replace(archived)

        second_id = "2f" * 16
        second = self.recorder("phase1", second_id)
        with mock.patch("specula.resource_summary.time.monotonic", side_effect=[2.0, 3.0]):
            second.start_target("demo", self.work_dir)
            second.note_agent(
                self.work_dir,
                sidecar,
                attempt=2,
                archived_usage_path=archived,
            )
            self.write_json(
                self.work_dir,
                "agent.usage.json",
                _claude(session="claude-resume", tokens=(100, 50, 70, 30), cost=0.001430),
            )
            second.finish_target("demo")
        tracker.capture_invocation("phase1", ["demo"], second_id)

        phase = self.phase_state(self.state(self.work_dir), "phase1")
        self.assertEqual(phase["total_tokens"], 990)
        self.assertAlmostEqual(cast(float, phase["cost_usd"]), 0.003214)
        second_record = json.loads(self.record_path(self.work_dir, second_id).read_text())
        self.assertEqual([entry["path"] for entry in second_record["usage"]], ["agent.usage.json"])

    def test_unknown_manual_continuation_is_not_double_counted(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        sidecar = self.work_dir / "agent.usage.json"
        archived = self.work_dir / "agent.usage.attempt-1.json"

        first_id = "32" * 16
        first = self.recorder("phase1", first_id)
        with mock.patch("specula.resource_summary.time.monotonic", side_effect=[0.0, 1.0]):
            first.start_target("demo", self.work_dir)
            first.note_agent(self.work_dir, sidecar)
            self.write_json(
                self.work_dir,
                "agent.usage.json",
                _normalized(
                    session="opencode-manual",
                    tokens=740,
                    cached=200,
                    cost=0.001784,
                    agent="opencode",
                ),
            )
            first.finish_target("demo")
        tracker.capture_invocation("phase1", ["demo"], first_id)
        sidecar.replace(archived)

        second_id = "33" * 16
        second = self.recorder("phase1", second_id)
        with mock.patch("specula.resource_summary.time.monotonic", side_effect=[2.0, 3.0]):
            second.start_target("demo", self.work_dir)
            second.note_agent(
                self.work_dir,
                sidecar,
                attempt=2,
                archived_usage_path=archived,
            )
            self.write_json(
                self.work_dir,
                "agent.usage.json",
                _normalized(
                    session="opencode-manual",
                    tokens=990,
                    cached=270,
                    cost=0.003214,
                    agent="opencode",
                ),
            )
            second.finish_target("demo")
        tracker.capture_invocation("phase1", ["demo"], second_id)

        phase = self.phase_state(self.state(self.work_dir), "phase1")
        self.assertEqual(phase["total_tokens"], 740)
        self.assertEqual(phase["cached_input_tokens"], 200)
        self.assertAlmostEqual(cast(float, phase["cost_usd"]), 0.001784)
        self.assertTrue(phase["usage_incomplete"])
        second_record = json.loads(self.record_path(self.work_dir, second_id).read_text())
        self.assertFalse(second_record["usage_complete"])
        self.assertEqual(second_record["continued_usage"], ["agent.usage.json"])

    def test_missing_retry_archive_keeps_final_usage_but_marks_incomplete(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        sidecar = self.work_dir / "agent.usage.json"
        invocation_id = "30" * 16
        recorder = self.recorder("phase1", invocation_id)
        with mock.patch("specula.resource_summary.time.monotonic", side_effect=[0.0, 1.0]):
            recorder.start_target("demo", self.work_dir)
            recorder.note_agent(self.work_dir, sidecar, attempt=1)
            recorder.note_agent(self.work_dir, sidecar, attempt=2)
            self.write_json(
                self.work_dir,
                "agent.usage.json",
                _claude(session="claude-missing", tokens=(100, 50, 70, 30), cost=0.001430),
            )
            recorder.finish_target("demo")
        tracker.capture_invocation("phase1", ["demo"], invocation_id)

        phase = self.phase_state(self.state(self.work_dir), "phase1")
        self.assertEqual(phase["total_tokens"], 250)
        self.assertAlmostEqual(cast(float, phase["cost_usd"]), 0.001430)
        self.assertTrue(phase["usage_incomplete"])
        record = json.loads(self.record_path(self.work_dir, invocation_id).read_text())
        self.assertFalse(record["usage_complete"])
        self.assertEqual([entry["path"] for entry in record["usage"]], ["agent.usage.json"])

    def test_missing_cost_is_a_dash_while_tokens_remain_visible(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        sidecar = self.work_dir / "agent.usage.json"
        invocation_id = "3c" * 16
        recorder = self.recorder("phase1", invocation_id)
        with mock.patch("specula.resource_summary.time.monotonic", side_effect=[0.0, 1.0]):
            recorder.start_target("demo", self.work_dir)
            recorder.note_agent(self.work_dir, sidecar)
            self.write_json(
                self.work_dir,
                "agent.usage.json",
                _normalized(session="no-cost", tokens=420, cached=200, cost=None),
            )
            recorder.finish_target("demo")
        tracker.capture_invocation("phase1", ["demo"], invocation_id)

        self.assertIn(
            "| Phase 1 | 1s | 420 total (200 cached) | - |",
            self.summary(self.work_dir),
        )

    def test_complete_run_has_an_unqualified_total_when_all_phases_are_known(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)
        for index, definition in enumerate(PHASES, 1):
            invocation_id = f"{index:x}" * 32
            recorder = self.recorder(definition.key, invocation_id)
            with mock.patch("specula.resource_summary.time.monotonic", side_effect=[0.0, 10.0]):
                recorder.start_target("demo", self.work_dir)
                recorder.finish_target("demo")
            tracker.capture_invocation(definition.key, ["demo"], invocation_id)
        tracker.complete_run()

        text = self.summary(self.work_dir)
        self.assertIn("| **Total** | 1m 0s | 0 total (0 cached) | $0.00 |", text)
        self.assertNotIn("Total (incomplete)", text)

    def test_initialize_renders_small_summary_and_configuration(self) -> None:
        tracker = self.tracker()
        tracker.initialize(resume=False)

        text = self.summary(self.work_dir)
        self.assertIn("# Specula Summary", text)
        self.assertIn("| Phase | Runtime | Tokens | Estimated cost |", text)
        for label in ("Phase 1", "Phase 2", "Phase 2.5", "Phase 3", "Phase 4a", "Phase 4b"):
            self.assertIn(f"| {label} | - | - | - |", text)
        self.assertIn("| **Total (incomplete)** | - | - | - |", text)
        self.assertIn("- Configured maximum parallelism: 1", text)
        self.assertIn("- Configured TLC limits: 8G memory; 4 workers", text)


class TestSafety(ResourceSummaryCase):
    def test_restored_usage_path_cannot_escape_target(self) -> None:
        outside = self.root / "outside-usage.json"
        outside.write_text(json.dumps(_normalized(session="outside", tokens=999, cached=900, cost=9.0)) + "\n")
        tracker = self.tracker()
        tracker.initialize(resume=False)
        invocation_id = "4d" * 16
        path = self.record_path(self.work_dir, invocation_id)
        path.parent.mkdir(parents=True)
        path.write_text(
            json.dumps(
                {
                    "version": 1,
                    "invocation_id": invocation_id,
                    "phase": "phase1",
                    "target": "demo",
                    "status": "completed",
                    "elapsed_seconds": 1.0,
                    "usage_complete": True,
                    "usage": [
                        {
                            "path": "../../../outside-usage.json",
                            "agent": "codex",
                            "session_id": "outside",
                            "total_tokens": 999,
                            "cached_input_tokens": 900,
                            "cost_usd": 9.0,
                            "complete": True,
                        }
                    ],
                }
            )
            + "\n"
        )

        tracker.capture_invocation("phase1", ["demo"], invocation_id)

        phase = self.phase_state(self.state(self.work_dir), "phase1")
        self.assertEqual(phase["total_tokens"], 0)
        self.assertFalse(phase["tokens_observed"])
        self.assertTrue(phase["usage_incomplete"])

    @unittest.skipUnless(hasattr(os, "symlink"), "symlinks unavailable")
    def test_symlinked_usage_sidecar_is_not_followed(self) -> None:
        outside = self.root / "outside.json"
        outside.write_text(json.dumps(_normalized(session="outside", tokens=999, cached=900, cost=9.0)) + "\n")
        self.work_dir.mkdir(parents=True)
        sidecar = self.work_dir / "agent.usage.json"
        sidecar.symlink_to(outside)
        tracker = self.tracker()
        tracker.initialize(resume=False)
        invocation_id = "5e" * 16
        recorder = self.recorder("phase1", invocation_id)
        with mock.patch("specula.resource_summary.time.monotonic", side_effect=[0.0, 1.0]):
            recorder.start_target("demo", self.work_dir)
            recorder.note_agent(self.work_dir, sidecar)
            recorder.finish_target("demo")

        tracker.capture_invocation("phase1", ["demo"], invocation_id)

        phase = self.phase_state(self.state(self.work_dir), "phase1")
        self.assertTrue(outside.is_file())
        self.assertFalse(sidecar.exists())
        self.assertFalse(phase["tokens_observed"])
        self.assertFalse(phase["cost_observed"])
        self.assertTrue(phase["usage_incomplete"])

    @unittest.skipUnless(hasattr(os, "symlink"), "symlinks unavailable")
    def test_symlinked_usage_parent_is_rejected_without_touching_destination(self) -> None:
        outside = self.root / "outside"
        outside.mkdir()
        outside_sidecar = outside / "turn01_A.usage.json"
        outside_sidecar.write_text(json.dumps(_normalized(session=None, tokens=999, cached=900, cost=9.0)) + "\n")
        confirmation = self.work_dir / "confirmation"
        confirmation.mkdir(parents=True)
        (confirmation / "MC-1").symlink_to(outside, target_is_directory=True)
        invocation_id = "5f" * 16
        recorder = self.recorder("phase4a", invocation_id)

        with mock.patch("specula.resource_summary.time.monotonic", side_effect=[0.0, 1.0]):
            recorder.start_target("demo", self.work_dir)
            with self.assertRaisesRegex(OSError, "unsafe resource usage directory"):
                recorder.note_agent(self.work_dir, confirmation / "MC-1" / "turn01_A.usage.json")
            recorder.finish_target("demo")

        self.assertTrue(outside_sidecar.is_file())

    def test_invalid_invocation_identity_has_no_directory_side_effect(self) -> None:
        with self.assertRaises(ValueError):
            self.recorder("phase1", "../outside")

        self.assertFalse((self.work_dir / INVOCATION_DIRNAME).exists())

    @unittest.skipUnless(hasattr(os, "symlink"), "symlinks unavailable")
    def test_symlinked_work_directory_is_rejected_without_touching_destination(self) -> None:
        outside = self.root / "outside"
        outside.mkdir()
        linked = self.root / "linked"
        linked.symlink_to(outside, target_is_directory=True)
        recorder = self.recorder("phase1", "6f" * 16)

        with self.assertRaises(OSError):
            recorder.start_target("demo", linked)

        self.assertEqual(list(outside.iterdir()), [])


if __name__ == "__main__":
    unittest.main()
