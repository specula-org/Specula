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
from specula.adapters.utils.event_stream import parse_events, stream_events
from specula.adapters.utils.text import readable, summary, tool_summary


class TestProgressParsing(unittest.TestCase):
    def test_opencode_text_tool_and_error_events(self) -> None:
        records = [
            {
                "type": "text",
                "sessionID": "ses_1",
                "part": {"type": "text", "text": "finished"},
            },
            {
                "type": "tool_use",
                "sessionID": "ses_1",
                "part": {
                    "type": "tool",
                    "tool": "bash",
                    "state": {"input": {"command": "pytest -q"}},
                },
            },
            {"type": "error", "error": {"message": "provider unavailable"}},
        ]
        self.assertEqual(
            parse_events("opencode", [json.dumps(record) for record in records]),
            ["finished", "running pytest -q", "adapter error: provider unavailable"],
        )

    def test_opencode_native_error_envelope_uses_message_fallbacks(self) -> None:
        records = [
            {
                "type": "error",
                "error": {
                    "name": "ProviderAuthError",
                    "data": {"providerID": "openai", "message": "API key is missing"},
                },
            },
            {"type": "error", "error": {"name": "APIError", "message": "provider unavailable"}},
            {"type": "error", "error": {"name": "MessageOutputLengthError", "data": {}}},
        ]
        self.assertEqual(
            parse_events("opencode", [json.dumps(record) for record in records]),
            [
                "adapter error: API key is missing",
                "adapter error: provider unavailable",
                "adapter error: MessageOutputLengthError",
            ],
        )

    def test_pi_message_end_tool_and_error_events(self) -> None:
        records = [
            {
                "type": "message_update",
                "assistantMessageEvent": {"type": "text_delta", "delta": "work"},
            },
            {
                "type": "message_update",
                "assistantMessageEvent": {"type": "text_delta", "delta": "ing"},
            },
            {
                "type": "message_end",
                "message": {
                    "role": "assistant",
                    "content": [{"type": "text", "text": "working"}],
                },
            },
            {
                "type": "tool_execution_start",
                "toolName": "read",
                "args": {"path": "src/main.py"},
            },
            {"type": "error", "message": "request failed"},
        ]
        self.assertEqual(
            parse_events("pi", [json.dumps(record) for record in records]),
            ["working", "reading src/main.py", "adapter error: request failed"],
        )

    def test_pi_stream_reconstructs_fragments_and_delimits_messages(self) -> None:
        deltas = [
            "\x1b]0;spoofed\x07Split",
            " ",
            "wor",
            "d",
            " ",
            " ",
            "\n",
            "# He",
            "ading",
            "\n\n",
            "- **bo",
            "ld**  ",
            "\n",
        ]
        records = [
            *(
                {
                    "type": "message_update",
                    "assistantMessageEvent": {"type": "text_delta", "delta": delta},
                }
                for delta in deltas
            ),
            {
                "type": "message_end",
                "message": {
                    "role": "assistant",
                    "content": [{"type": "text", "text": "Split word  \n# Heading\n\n- **bold**  \n"}],
                },
            },
            {
                "type": "tool_execution_start",
                "toolName": "read",
                "args": {"path": "src/main.py"},
            },
            {
                "type": "message_update",
                "assistantMessageEvent": {"type": "text_delta", "delta": "repeat"},
            },
            {
                "type": "message_update",
                "assistantMessageEvent": {"type": "text_delta", "delta": "repeat"},
            },
            {
                "type": "message_update",
                "assistantMessageEvent": {"type": "text_delta", "delta": "\n"},
            },
            {
                "type": "message_update",
                "assistantMessageEvent": {"type": "text_delta", "delta": "tail"},
            },
            {
                "type": "message_end",
                "message": {
                    "role": "assistant",
                    "content": [{"type": "text", "text": "repeatrepeat\ntail"}],
                },
            },
        ]
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            log = root / "agent.log"
            stream_events(
                "pi",
                root / "agent.activity.jsonl",
                log,
                (json.dumps(record).encode() + b"\n" for record in records),
            )

            self.assertEqual(
                log.read_text(),
                "Split word  \n# Heading\n\n- **bold**  \nreading src/main.py\nrepeatrepeat\ntail\n",
            )

    def test_opencode_stream_accumulates_step_finish_usage(self) -> None:
        records = [
            {
                "type": "step_finish",
                "sessionID": "ses_first",
                "part": {
                    "tokens": {
                        "input": 10,
                        "output": 20,
                        "reasoning": 30,
                        "cache": {"read": 40, "write": 50},
                    },
                    "cost": 0.25,
                },
            },
            {
                "type": "step_finish",
                "sessionID": "ses_later",
                "part": {
                    "tokens": {
                        "input": 1,
                        "output": 2,
                        "reasoning": 3,
                        "cache": {"read": 4, "write": 5},
                    },
                    "cost": 0.75,
                },
            },
        ]
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            status = stream_events(
                "opencode",
                root / "agent.activity.jsonl",
                root / "agent.log",
                (json.dumps(record).encode() + b"\n" for record in records),
            )

        self.assertEqual(
            status.usage,
            {
                "agent": "opencode",
                "session_id": "ses_first",
                "session_file": None,
                "total_cost_usd": 1.0,
                "usage": {
                    "input_tokens": 11,
                    "cached_input_tokens": 44,
                    "cache_write_input_tokens": 55,
                    "output_tokens": 22,
                    "reasoning_output_tokens": 33,
                    "total_tokens": 132,
                },
            },
        )

    def test_opencode_step_cost_does_not_require_token_usage(self) -> None:
        record = {"type": "step_finish", "sessionID": "ses_cost", "part": {"cost": 0.5}}
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            status = stream_events(
                "opencode",
                root / "agent.activity.jsonl",
                root / "agent.log",
                [json.dumps(record).encode()],
            )

        self.assertEqual(status.usage["total_cost_usd"], 0.5)

    def test_pi_stream_accumulates_only_assistant_message_usage(self) -> None:
        records = [
            {
                "type": "session",
                "version": 3,
                "id": "pi_session",
                "timestamp": "2026-07-14T00:00:00.000Z",
                "cwd": "/workspace",
            },
            {
                "type": "message_end",
                "message": {
                    "role": "user",
                    "usage": {
                        "input": 100,
                        "output": 100,
                        "cacheRead": 100,
                        "cacheWrite": 100,
                        "cost": {"total": 100.0},
                    },
                },
            },
            {
                "type": "message_end",
                "message": {
                    "role": "assistant",
                    "content": [{"type": "text", "text": "message-end-only text"}],
                    "usage": {
                        "input": 10,
                        "output": 20,
                        "cacheRead": 30,
                        "cacheWrite": 40,
                        "cost": {"total": 0.25},
                    },
                },
            },
            {
                "type": "message_end",
                "message": {
                    "role": "assistant",
                    "usage": {
                        "input": 1,
                        "output": 2,
                        "cacheRead": 3,
                        "cacheWrite": 4,
                        "cost": {"total": 0.75},
                    },
                },
            },
        ]
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            log = root / "agent.log"
            status = stream_events(
                "pi",
                root / "agent.activity.jsonl",
                log,
                (json.dumps(record).encode() + b"\n" for record in records),
            )
            self.assertEqual(log.read_text(), "message-end-only text\n")

        self.assertEqual(
            status.usage,
            {
                "agent": "pi",
                "session_id": "pi_session",
                "session_file": None,
                "total_cost_usd": 1.0,
                "usage": {
                    "input_tokens": 11,
                    "cached_input_tokens": 33,
                    "cache_write_input_tokens": 44,
                    "output_tokens": 22,
                    "reasoning_output_tokens": 0,
                    "total_tokens": 110,
                },
            },
        )

    def test_pi_subagent_result_records_exact_session_files(self) -> None:
        record = {
            "type": "tool_execution_end",
            "toolName": "subagent",
            "result": {
                "details": {
                    "results": [
                        {"sessionFile": "/tmp/pi-one/session.jsonl"},
                        {"sessionPath": "/tmp/pi-two/session.jsonl"},
                    ]
                }
            },
        }
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            status = stream_events(
                "pi",
                root / "agent.activity.jsonl",
                root / "agent.log",
                [json.dumps(record).encode()],
            )

        self.assertEqual(
            status.session_files,
            ("/tmp/pi-one/session.jsonl", "/tmp/pi-two/session.jsonl"),
        )

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

    def test_old_copilot_plain_stream_remains_live_and_sanitized(self) -> None:
        events = parse_events("copilot-cli", ["Inspecting\x1b[2J input handling."])
        self.assertEqual(events, ["Inspecting input handling."])

    def test_old_copilot_plain_stream_does_not_guess_error_severity(self) -> None:
        events = parse_events("copilot-cli", ["Tests failed before; fixed now.", "API Error: 529 overloaded_error"])
        self.assertEqual(events, ["Tests failed before; fixed now.", "API Error: 529 overloaded_error"])

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

    def test_pi_fragment_log_is_flushed_before_stream_interruption(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            raw = root / "agent.activity.jsonl"
            log = root / "agent.log"
            event = json.dumps(
                {
                    "type": "message_update",
                    "assistantMessageEvent": {"type": "text_delta", "delta": "live "},
                }
            ).encode()

            def interrupted_stream() -> Iterator[bytes]:
                yield event
                self.assertEqual(log.read_text(), "live ")
                raise KeyboardInterrupt

            with self.assertRaises(KeyboardInterrupt):
                stream_events("pi", raw, log, interrupted_stream())

            self.assertEqual(
                raw.read_bytes(),
                b'{"type":"message_update","assistantMessageEvent":{"type":"text_delta","delta":"live "}}',
            )
            self.assertEqual(log.read_text(), "live ")

    @unittest.skipUnless(Path("/dev/full").exists(), "requires /dev/full")
    def test_raw_sink_failure_drains_source_and_preserves_readable_log(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            log = root / "agent.log"
            records = [
                json.dumps({"type": "assistant.message", "data": {"content": "first"}}).encode(),
                json.dumps({"type": "assistant.message", "data": {"content": "final"}}).encode(),
            ]
            drained = False

            def source() -> Iterator[bytes]:
                nonlocal drained
                yield from records
                drained = True

            stderr = io.StringIO()
            with contextlib.redirect_stderr(stderr):
                status = stream_events("copilot", Path("/dev/full"), log, source())

            self.assertTrue(drained)
            self.assertFalse(status.activity_ok)
            self.assertTrue(status.log_ok)
            self.assertIn("activity log", stderr.getvalue())
            self.assertEqual(log.read_text(), "first\nfinal\n")

    def test_finished_agent_never_claims_process_is_still_alive(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            proc = subprocess.Popen(["true"])
            proc.wait()
            agent = progress.RunningAgent(
                name="done",
                proc=proc,
                work_dir=root,
                log=root / "agent.log",
                activity_log=root / "agent.activity.jsonl",
                ignored=set(),
                snapshot={},
                reported_snapshot={},
                last_observed_at=time.monotonic() - 600,
                log_stamp=None,
                activity_stamp=None,
                adapter_name="codex",
            )
            output = io.StringIO()
            with contextlib.redirect_stdout(output):
                progress.report([agent], progress.ProgressConfig())
            self.assertNotIn("process is still alive", output.getvalue())

    def test_finished_agent_does_not_report_output_as_active(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            log = root / "agent.log"
            log.write_text("final output\n")
            proc = subprocess.Popen(["true"])
            proc.wait()
            agent = progress.RunningAgent(
                name="done",
                proc=proc,
                work_dir=root,
                log=log,
                activity_log=root / "agent.activity.jsonl",
                ignored={Path("agent.log")},
                snapshot={},
                reported_snapshot={},
                last_observed_at=time.monotonic(),
                log_stamp=None,
                activity_stamp=None,
                adapter_name="fake",
                reported_output=True,
                last_output_report_at=0.0,
            )
            output = io.StringIO()
            with contextlib.redirect_stdout(output):
                progress.report([agent], progress.ProgressConfig(status_after_seconds=0.0))
            self.assertNotIn("active", output.getvalue())


if __name__ == "__main__":
    unittest.main()
