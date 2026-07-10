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

from specula import progress
from specula.adapters.event_stream import parse_events, readable, stream_events, summary, tool_summary


class TestProgressParsing(unittest.TestCase):
    def test_summary_removes_terminal_control_sequences(self) -> None:
        text = "\x1b]0;spoofed title\x07hello \x1b[31mred\x1b[0m\rworld"
        self.assertEqual(summary(text), "hello red world")

    def test_tool_summary_removes_shell_wrapper_quotes(self) -> None:
        self.assertEqual(
            tool_summary("command_execution", {"command": "/bin/bash -lc 'rg needle src'"}),
            "running rg needle src",
        )

    def test_unknown_tool_name_is_sanitized(self) -> None:
        # an MCP server names its own tools, and the name reaches the terminal
        self.assertEqual(tool_summary("evil\x1b[2J\x1b]0;pwn\x07", {}), "using evil")
        self.assertEqual(tool_summary("\x1b[2J", {}), "using tool")

    def test_stream_tool_names_are_sanitized(self) -> None:
        cases = [
            ("copilot-cli", {"type": "tool.execution_start", "data": {"toolName": "x\x1b]0;pwn\x07", "arguments": {}}}),
            ("claude-code", {"type": "assistant", "message": {"content": [{"type": "tool_use", "name": "y\x1b[31m"}]}}),
        ]
        for adapter, record in cases:
            with self.subTest(adapter=adapter):
                events = parse_events(adapter, [json.dumps(record)])
                self.assertNotIn("\x1b", "".join(events))

    def test_workspace_change_paths_are_sanitized(self) -> None:
        # the agent chooses these filenames
        line = progress._describe_changes([("created", Path("re\x1b[2Jport.md"))])
        self.assertEqual(line, "created report.md")

    def test_readable_keeps_line_structure_but_drops_escapes(self) -> None:
        # agent.log holds the final markdown report; only the CLI ticker flattens
        self.assertEqual(readable("# H\n\n- a\x1b[31m\n- b  \n"), "# H\n\n- a\n- b")
        self.assertEqual(summary("# H\n\n- a\n- b"), "# H - a - b")

    def test_final_unterminated_event_is_reported(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            activity = root / "agent.activity.jsonl"
            activity.write_text('{"type":"item.completed","item":{"type":"agent_message","text":"finished"}}')
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
