"""Focused tests for adapter child-session usage reconciliation."""

from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

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
