"""Focused tests for adapter child-session usage reconciliation."""

from __future__ import annotations

import json
import sqlite3
import tempfile
import unittest
from pathlib import Path

from specula.adapters.utils.copilot_usage import collect_usage
from specula.adapters.utils.event_stream import stream_events
from specula.adapters.utils.usage import augment_pi_usage, pi_subagent_results


def _usage(input_tokens: int = 100) -> dict[str, object]:
    return {"input": input_tokens, "output": 20, "cacheRead": 200, "cacheWrite": 100, "cost": 1.5, "turns": 3}


def _result(input_tokens: int = 100, **extra: object) -> dict[str, object]:
    return {"agent": "worker", "model": "glm-5.2", "exitCode": 0, "usage": _usage(input_tokens), **extra}


def _event(*results: dict[str, object]) -> dict[str, object]:
    return {"type": "tool_execution_end", "toolName": "subagent", "result": {"details": {"results": list(results)}}}


def _parent_payload() -> dict[str, object]:
    usage = {
        "input_tokens": 10,
        "cached_input_tokens": 20,
        "cache_write_input_tokens": 10,
        "output_tokens": 2,
        "reasoning_output_tokens": 0,
        "total_tokens": 42,
    }
    return {"agent": "pi", "session_id": "parent", "session_file": None, "total_cost_usd": 0.1, "usage": usage}


def _mapping(value: object) -> dict[str, object]:
    assert isinstance(value, dict)
    return value


def _total(payload: dict[str, object], section: str) -> object:
    return _mapping(_mapping(payload[section])["usage"])["total_tokens"]


def _copilot_database(path: Path, rows: list[tuple[object, ...]]) -> Path:
    path.mkdir(parents=True, exist_ok=True)
    database = path / "session-store.db"
    with sqlite3.connect(database) as connection:
        connection.execute(
            """
            CREATE TABLE assistant_usage_events (
                session_id TEXT NOT NULL,
                model TEXT NOT NULL,
                copilot_usage_model TEXT,
                input_tokens INTEGER,
                output_tokens INTEGER,
                cache_read_tokens INTEGER,
                cache_write_tokens INTEGER,
                reasoning_tokens INTEGER,
                total_nano_aiu INTEGER,
                duration_ms INTEGER
            )
            """
        )
        connection.executemany(
            "INSERT INTO assistant_usage_events VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)",
            rows,
        )
    return database


class TestCopilotUsage(unittest.TestCase):
    def test_collects_cumulative_session_usage_without_double_counting_cache(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            database = _copilot_database(
                root,
                [
                    ("session", "gpt-a", None, 100, 30, 70, 20, 5, 1_200_000_000_000, 400),
                    ("session", "gpt-b", "billing-b", 50, 8, 10, 5, 2, 300_000_000_000, 100),
                    ("other", "gpt-a", None, 999, 999, 0, 0, 0, 999, 999),
                ],
            )
            payload = collect_usage("session", database)

        usage = _mapping(payload["usage"])
        self.assertTrue(payload["usage_complete"])
        self.assertEqual(payload["usage_scope"], "session_cumulative")
        self.assertEqual(payload["request_count"], 2)
        self.assertEqual(usage["input_tokens"], 45)
        self.assertEqual(usage["cached_input_tokens"], 80)
        self.assertEqual(usage["cache_write_input_tokens"], 25)
        self.assertEqual(usage["output_tokens"], 38)
        self.assertEqual(usage["reasoning_output_tokens"], 7)
        self.assertEqual(usage["total_tokens"], 188)
        self.assertEqual(payload["total_nano_aiu"], 1_500_000_000_000)
        self.assertEqual(payload["ai_credits"], 1500.0)
        self.assertEqual(payload["total_cost_usd"], 15.0)
        self.assertEqual(payload["duration_ms"], 500)
        model_usage = _mapping(payload["model_usage"])
        self.assertEqual(set(model_usage), {"gpt-a", "billing-b"})
        self.assertEqual(_mapping(model_usage["gpt-a"])["total_cost_usd"], 12.0)
        self.assertEqual(_mapping(model_usage["billing-b"])["total_cost_usd"], 3.0)

    def test_missing_or_inconsistent_telemetry_is_explicitly_unavailable(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            database = _copilot_database(
                root,
                [("session", "gpt-a", None, 5, 3, 4, 2, 0, 100, 20)],
            )
            inconsistent = collect_usage("session", database)
            missing_cost_database = _copilot_database(
                root / "missing-cost",
                [("session", "gpt-a", None, 5, 3, 4, 1, 0, None, 20)],
            )
            missing_cost = collect_usage("session", missing_cost_database)
            missing_session = collect_usage(None, database)
            missing_database = collect_usage("session", root / "missing.db")

        for payload in (inconsistent, missing_cost, missing_session, missing_database):
            with self.subTest(warning=payload["usage_warning"]):
                self.assertFalse(payload["usage_complete"])
                self.assertEqual(payload["usage"], {})
                self.assertIn("usage", str(payload["usage_warning"]).casefold())


class TestPiSubagentUsage(unittest.TestCase):
    def test_streamed_inline_usage_reaches_combined_total(self) -> None:
        terminal = {
            "type": "message_end",
            "message": {
                "role": "assistant",
                "stopReason": "stop",
                "usage": {"input": 10, "output": 2, "cacheRead": 20, "cacheWrite": 10, "cost": {"total": 0.1}},
            },
        }
        records = [{"type": "session", "id": "parent"}, _event(_result()), terminal]
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            status = stream_events(
                "pi",
                root / "activity.jsonl",
                root / "agent.log",
                (json.dumps(record).encode() + b"\n" for record in records),
            )
            combined = augment_pi_usage(status.usage, status.subagent_results, root)

        self.assertTrue(combined["usage_complete"])
        self.assertEqual(_total(combined, "parent"), 42)
        self.assertEqual(_total(combined, "subagents"), 420)
        self.assertEqual(_total(combined, "combined"), 462)

    def test_nested_results_count_and_missing_usage_is_partial(self) -> None:
        nested = _event(_result(messages=[{"role": "toolResult", "details": {"results": [_result(50)]}}]))
        missing = _event({"agent": "unaccounted", "exitCode": 0})
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            nested_usage = augment_pi_usage(_parent_payload(), pi_subagent_results(nested), root)
            partial = augment_pi_usage(_parent_payload(), pi_subagent_results(missing), root)

        self.assertEqual(_mapping(nested_usage["subagents"])["session_count"], 2)
        self.assertEqual(_total(nested_usage, "subagents"), 790)
        self.assertFalse(partial["usage_complete"])
        self.assertIn("usage unavailable", str(partial["usage_warning"]))

    def test_inline_usage_supersedes_same_session_file(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            session_file = root / "session.jsonl"
            records = [
                {"type": "session", "id": "child"},
                {"type": "message", "message": {"role": "assistant", "usage": {**_usage(), "cost": {"total": 1.5}}}},
            ]
            session_file.write_text("\n".join(json.dumps(record) for record in records) + "\n")
            event = _event(_result(sessionFile=str(session_file)))
            combined = augment_pi_usage(_parent_payload(), pi_subagent_results(event), root)

        self.assertTrue(combined["usage_complete"])
        self.assertEqual(_mapping(combined["subagents"])["session_count"], 1)
        self.assertEqual(_total(combined, "subagents"), 420)
        self.assertEqual(_total(combined, "combined"), 462)


if __name__ == "__main__":
    unittest.main()
