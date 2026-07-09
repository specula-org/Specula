"""Focused tests for agent activity parsing and terminal-safe reporting."""

from __future__ import annotations

import contextlib
import io
import json
import subprocess
import tempfile
import time
import unittest
from collections.abc import Iterator
from pathlib import Path

from specula import activity, progress
from specula.adapters.event_stream import stream_events


class TestProgressParsing(unittest.TestCase):
    def test_summary_removes_terminal_control_sequences(self) -> None:
        text = "\x1b]0;spoofed title\x07hello \x1b[31mred\x1b[0m\rworld"
        self.assertEqual(activity.summary(text), "hello red world")

    def test_tool_summary_removes_shell_wrapper_quotes(self) -> None:
        self.assertEqual(
            activity.tool_summary("command_execution", {"command": "/bin/bash -lc 'rg needle src'"}),
            "running rg needle src",
        )

    def test_final_unterminated_event_is_reported(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            activity = root / "agent.activity.jsonl"
            activity.write_text(
                '{"type":"item.completed","item":{"type":"agent_message","text":"finished"}}'
            )
            proc = subprocess.Popen(["true"])
            proc.wait()
            agent = progress.RunningAgent(
                name="target",
                proc=proc,
                work_dir=root,
                log=root / "agent.log",
                activity_log=activity,
                ignored={activity.relative_to(root)},
                snapshot={},
                reported_snapshot={},
                last_observed_at=time.monotonic(),
                log_stamp=None,
                activity_stamp=None,
                adapter_name="codex",
            )
            output = io.StringIO()
            with contextlib.redirect_stdout(output):
                progress.report([agent], progress.ProgressConfig())
            self.assertIn("target: finished", output.getvalue())

    def test_readable_log_is_flushed_before_stream_interruption(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            raw = root / "agent.activity.jsonl"
            log = root / "agent.log"
            event = json.dumps(
                {
                    "type": "tool.execution_start",
                    "data": {"toolName": "view", "arguments": {"path": "kilo.c"}},
                }
            ).encode()

            def interrupted_stream() -> Iterator[bytes]:
                self.assertTrue(log.is_file())
                yield event
                raise KeyboardInterrupt

            with self.assertRaises(KeyboardInterrupt):
                stream_events("copilot", raw, log, interrupted_stream())

            self.assertEqual(raw.read_bytes(), event)
            self.assertEqual(log.read_text(), "reading kilo.c\n")


if __name__ == "__main__":
    unittest.main()
