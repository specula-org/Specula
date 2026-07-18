"""Boundary tests for exact native-session resume state and transient errors."""

from __future__ import annotations

import contextlib
import io
import json
import os
import tempfile
import threading
import unittest
from collections.abc import Iterator
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from unittest.mock import patch

from specula.adapters.utils.event_stream import stream_events
from specula.adapters.utils.resume import ResumeStateError, capture_session_id, read_session_id
from specula.adapters.utils.transient import (
    failed_log_has_transient_failure,
    final_diagnostic_has_transient_failure,
    looks_transient,
)


class TestResumeState(unittest.TestCase):
    def test_capture_is_atomic_and_round_trips_exact_binding(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            state = root / "nested" / "turn.resume.json"

            capture_session_id(
                state,
                adapter="codex",
                session_id="thread-123",
                cwd=str(root),
                model="gpt-5.5",
                effort="high",
            )

            self.assertEqual(
                read_session_id(
                    state,
                    adapter="codex",
                    cwd=str(root),
                    model="gpt-5.5",
                    effort="high",
                ),
                "thread-123",
            )
            self.assertEqual(list(state.parent.glob(f".{state.name}.*.tmp")), [])
            payload = json.loads(state.read_text(encoding="utf-8"))
            self.assertEqual(payload["version"], 1)
            self.assertEqual(payload["cwd"], os.path.realpath(root))

    def test_failed_atomic_publish_leaves_no_state_or_temporary_file(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            state = root / "turn.resume.json"

            with (
                patch("specula.adapters.utils.resume.os.link", side_effect=OSError("disk full")),
                self.assertRaisesRegex(ResumeStateError, "cannot write"),
            ):
                capture_session_id(
                    state,
                    adapter="codex",
                    session_id="thread-123",
                    cwd=str(root),
                )

            self.assertFalse(state.exists())
            self.assertEqual(list(root.glob(f".{state.name}.*.tmp")), [])

    def test_missing_state_means_fresh_turn(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            self.assertIsNone(
                read_session_id(
                    root / "missing.resume.json",
                    adapter="codex",
                    cwd=str(root),
                )
            )

    def test_malformed_state_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            state = root / "turn.resume.json"
            state.write_text("{not-json", encoding="utf-8")

            with self.assertRaisesRegex(ResumeStateError, "cannot read"):
                read_session_id(state, adapter="codex", cwd=str(root))

    def test_symlink_state_is_rejected_for_read_and_capture(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            target = root / "target.json"
            target.write_text("{}", encoding="utf-8")
            state = root / "turn.resume.json"
            state.symlink_to(target)

            with self.assertRaisesRegex(ResumeStateError, "not a regular file"):
                read_session_id(state, adapter="codex", cwd=str(root))
            with self.assertRaisesRegex(ResumeStateError, "not a regular file"):
                capture_session_id(
                    state,
                    adapter="codex",
                    session_id="thread-123",
                    cwd=str(root),
                )
            self.assertEqual(target.read_text(encoding="utf-8"), "{}")

    def test_option_like_session_id_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            with self.assertRaisesRegex(ResumeStateError, "must not begin"):
                capture_session_id(
                    root / "turn.resume.json",
                    adapter="codex",
                    session_id="--last",
                    cwd=str(root),
                )

    def test_each_binding_field_must_match_exactly(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            other = root / "other"
            other.mkdir()
            state = root / "turn.resume.json"
            capture_session_id(
                state,
                adapter="codex",
                session_id="thread-123",
                cwd=str(root),
                model="gpt-5.5",
                effort="high",
            )
            mismatches = (
                {"adapter": "claude-code", "cwd": str(root), "model": "gpt-5.5", "effort": "high"},
                {"adapter": "codex", "cwd": str(other), "model": "gpt-5.5", "effort": "high"},
                {"adapter": "codex", "cwd": str(root), "model": "gpt-5.4", "effort": "high"},
                {"adapter": "codex", "cwd": str(root), "model": "gpt-5.5", "effort": "medium"},
            )

            for binding in mismatches:
                with self.subTest(binding=binding), self.assertRaises(ResumeStateError):
                    read_session_id(state, **binding)

    def test_different_session_id_fails_without_replacing_original(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            state = root / "turn.resume.json"
            capture_session_id(state, adapter="opencode", session_id="ses-one", cwd=str(root))

            with self.assertRaisesRegex(ResumeStateError, "changed session ID"):
                capture_session_id(state, adapter="opencode", session_id="ses-two", cwd=str(root))

            self.assertEqual(
                read_session_id(state, adapter="opencode", cwd=str(root)),
                "ses-one",
            )

    def test_concurrent_first_capture_cannot_silently_replace_another_id(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            state = root / "turn.resume.json"
            barrier = threading.Barrier(2)
            real_link = os.link

            def racing_link(
                source: str | bytes | os.PathLike[str] | os.PathLike[bytes],
                destination: str | bytes | os.PathLike[str] | os.PathLike[bytes],
                *,
                follow_symlinks: bool = True,
            ) -> None:
                barrier.wait(timeout=2)
                real_link(source, destination, follow_symlinks=follow_symlinks)

            def capture(session_id: str) -> Exception | None:
                try:
                    capture_session_id(state, adapter="codex", session_id=session_id, cwd=str(root))
                except Exception as exc:  # Return both outcomes to the parent thread for exact assertions.
                    return exc
                return None

            with (
                patch("specula.adapters.utils.resume.os.link", side_effect=racing_link),
                ThreadPoolExecutor(max_workers=2) as executor,
            ):
                outcomes = list(executor.map(capture, ("thread-one", "thread-two")))

            failures = [outcome for outcome in outcomes if outcome is not None]
            self.assertEqual(len(failures), 1)
            self.assertIsInstance(failures[0], ResumeStateError)
            self.assertIn(
                read_session_id(state, adapter="codex", cwd=str(root)),
                {"thread-one", "thread-two"},
            )


class TestEventStreamSessionCapture(unittest.TestCase):
    def test_all_structured_adapters_capture_documented_session_id(self) -> None:
        cases = (
            ("claude", "claude-code", {"type": "system", "subtype": "init", "session_id": "claude-1"}, "claude-1"),
            ("codex", "codex", {"type": "thread.started", "thread_id": "codex-1"}, "codex-1"),
            (
                "copilot-json",
                "copilot-cli",
                {
                    "type": "result",
                    "sessionId": "11111111-1111-4111-8111-111111111111",
                    "exitCode": 0,
                    "usage": {},
                },
                "11111111-1111-4111-8111-111111111111",
            ),
            (
                "opencode",
                "opencode",
                {"type": "text", "sessionID": "opencode-1", "part": {"type": "text", "text": "work"}},
                "opencode-1",
            ),
            ("pi", "pi", {"type": "session", "id": "pi-1"}, "pi-1"),
        )
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            previous_cwd = Path.cwd()
            os.chdir(root)
            try:
                for stream_adapter, state_adapter, record, session_id in cases:
                    with self.subTest(adapter=stream_adapter):
                        state = root / f"{stream_adapter}.resume.json"

                        def explicit_capture(
                            value: str,
                            *,
                            state_path: Path = state,
                            adapter_name: str = state_adapter,
                        ) -> None:
                            capture_session_id(
                                state_path,
                                adapter=adapter_name,
                                session_id=value,
                                cwd=str(root),
                                model="test-model",
                                effort="test-effort",
                            )

                        status = stream_events(
                            stream_adapter,
                            root / f"{stream_adapter}.activity.jsonl",
                            root / f"{stream_adapter}.log",
                            [json.dumps(record).encode() + b"\n"],
                            session_capture=explicit_capture,
                        )

                        self.assertEqual(status.session_id, session_id)
                        self.assertEqual(
                            read_session_id(
                                state,
                                adapter=state_adapter,
                                cwd=str(root),
                                model="test-model",
                                effort="test-effort",
                            ),
                            session_id,
                        )
            finally:
                os.chdir(previous_cwd)

    def test_ambient_resume_variables_do_not_enable_capture(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            state = root / "ambient.resume.json"
            with patch.dict(
                os.environ,
                {
                    "SPECULA_RESUME_STATE": str(state),
                    "SPECULA_RESUME_MODEL": "ambient-model",
                    "SPECULA_RESUME_EFFORT": "ambient-effort",
                },
                clear=False,
            ):
                status = stream_events(
                    "codex",
                    root / "agent.activity.jsonl",
                    root / "agent.log",
                    [b'{"type":"thread.started","thread_id":"thread-ambient"}\n'],
                )

            self.assertEqual(status.session_id, "thread-ambient")
            self.assertTrue(status.resume_ok)
            self.assertFalse(state.exists())

    def test_session_id_change_reports_failure_but_drains_stream(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            state = root / "turn.resume.json"
            records = (
                {"type": "text", "sessionID": "ses-one", "part": {"type": "text", "text": "before"}},
                {"type": "text", "sessionID": "ses-two", "part": {"type": "text", "text": "after"}},
                {"type": "step_finish", "sessionID": "ses-two", "part": {"reason": "stop"}},
            )
            consumed: list[str] = []

            def source() -> Iterator[bytes]:
                for record in records:
                    consumed.append(str(record["type"]))
                    yield json.dumps(record).encode() + b"\n"

            previous_cwd = Path.cwd()
            os.chdir(root)
            try:

                def explicit_capture(value: str) -> None:
                    capture_session_id(
                        state,
                        adapter="opencode",
                        session_id=value,
                        cwd=str(root),
                    )

                stderr = io.StringIO()
                with contextlib.redirect_stderr(stderr):
                    status = stream_events(
                        "opencode",
                        root / "agent.activity.jsonl",
                        root / "agent.log",
                        source(),
                        session_capture=explicit_capture,
                    )
            finally:
                os.chdir(previous_cwd)

            self.assertEqual(consumed, ["text", "text", "step_finish"])
            self.assertFalse(status.log_ok)
            self.assertFalse(status.resume_ok)
            self.assertTrue(status.successful_terminal)
            self.assertIn("changed session ID", stderr.getvalue())
            self.assertEqual((root / "agent.log").read_text(encoding="utf-8"), "before\nafter\n")
            self.assertEqual(read_session_id(state, adapter="opencode", cwd=str(root)), "ses-one")


class TestTransientFailureClassification(unittest.TestCase):
    def test_recognizes_typed_codes_statuses_and_capacity_message(self) -> None:
        payloads = (
            {"code": "overloaded_error"},
            {"statusCode": 503},
            {"error": {"message": "Selected model is at capacity. Please try a different model."}},
            {"cause": {"error_type": "request_timeout"}},
            {"name": "APIConnectionError"},
            {"errorType": "APITimeoutError"},
            {"cause": {"name": "TransportError"}},
            {"name": "ServiceUnavailableError"},
            {"errorType": "RequestTimeoutError"},
            {"code": "ECONNRESET"},
            {"cause": {"code": "ETIMEDOUT"}},
            {"message": "socket hang up"},
            {"message": "fetch failed"},
        )
        for payload in payloads:
            with self.subTest(payload=payload):
                self.assertTrue(looks_transient(payload))

    def test_non_transient_client_errors_are_not_classified(self) -> None:
        payloads = (
            {"status": 400, "message": "invalid request"},
            {"status": 401, "message": "invalid API key"},
            {"status": 429, "message": "rate limited"},
            {"code": "content_policy_violation"},
        )
        for payload in payloads:
            with self.subTest(payload=payload):
                self.assertFalse(looks_transient(payload))

    def test_structured_provider_failure_is_classified(self) -> None:
        records = [
            {"type": "thread.started", "thread_id": "thread-1"},
            {"type": "turn.failed", "error": {"code": "server_error", "message": "HTTP 503"}},
        ]
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            status = stream_events(
                "codex",
                root / "agent.activity.jsonl",
                root / "agent.log",
                [json.dumps(record).encode() + b"\n" for record in records],
            )

        self.assertIsNotNone(status.transient_error)
        self.assertFalse(status.successful_terminal)

    def test_agent_quote_is_not_a_provider_failure(self) -> None:
        records = [
            {"type": "thread.started", "thread_id": "thread-1"},
            {
                "type": "item.completed",
                "item": {
                    "type": "agent_message",
                    "text": "The log says: Selected model is at capacity. Please try a different model.",
                },
            },
            {"type": "turn.failed", "error": {"code": "invalid_request", "message": "bad input"}},
        ]
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            status = stream_events(
                "codex",
                root / "agent.activity.jsonl",
                root / "agent.log",
                [json.dumps(record).encode() + b"\n" for record in records],
            )

        self.assertIsNone(status.transient_error)
        self.assertIsNone(status.plain_transient_error)

    def test_successful_terminal_clears_earlier_transient_error(self) -> None:
        records = [
            {"type": "turn.failed", "error": {"code": "overloaded_error", "message": "overloaded"}},
            {"type": "turn.completed", "usage": {}},
        ]
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            status = stream_events(
                "codex",
                root / "agent.activity.jsonl",
                root / "agent.log",
                [json.dumps(record).encode() + b"\n" for record in records],
            )

        self.assertTrue(status.successful_terminal)
        self.assertIsNone(status.transient_error)

    def test_only_final_plain_diagnostic_of_unsuccessful_stream_is_classified(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            detected = stream_events(
                "codex",
                root / "detected.activity.jsonl",
                root / "detected.log",
                [b"HTTP 503: Selected model is at capacity. Please try a different model.\n"],
            )
            superseded = stream_events(
                "codex",
                root / "superseded.activity.jsonl",
                root / "superseded.log",
                [
                    b"HTTP 503: service temporarily unavailable\n",
                    b'{"type":"turn.failed","error":{"code":"invalid_request","message":"bad input"}}\n',
                ],
            )
            successful = stream_events(
                "codex",
                root / "successful.activity.jsonl",
                root / "successful.log",
                [
                    b'{"type":"turn.completed","usage":{}}\n',
                    b"HTTP 503: service temporarily unavailable\n",
                ],
            )

        self.assertIsNotNone(detected.plain_transient_error)
        self.assertIsNone(superseded.plain_transient_error)
        self.assertIsNone(successful.plain_transient_error)

    def test_failed_log_fallback_uses_only_final_non_json_line(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            log = root / "agent.log"
            log.write_text("HTTP 503: service unavailable\n", encoding="utf-8")
            self.assertTrue(failed_log_has_transient_failure(log))

            log.write_text("HTTP 503: service unavailable\nfatal: invalid request\n", encoding="utf-8")
            self.assertFalse(failed_log_has_transient_failure(log))

            self.assertFalse(
                final_diagnostic_has_transient_failure(
                    '{"type":"turn.failed","error":{"message":"HTTP 503: service unavailable"}}\n'
                )
            )

    def test_plain_http_status_must_start_like_a_cli_diagnostic(self) -> None:
        diagnostics = (
            "HTTP 503: service unavailable\n",
            "Error: API error 529 overloaded\n",
            "Error: read ECONNRESET\n",
            "Error: getaddrinfo EAI_AGAIN registry.npmjs.org\n",
            "Error: connect ETIMEDOUT 10.0.0.1:443\n",
            "Error: connect ECONNREFUSED 127.0.0.1:443\n",
            "Error: write EPIPE\n",
            "TypeError: fetch failed\n",
            "fetch failed\n",
        )
        for diagnostic in diagnostics:
            with self.subTest(diagnostic=diagnostic):
                self.assertTrue(final_diagnostic_has_transient_failure(diagnostic))

        prose = (
            "500 tests failed\n",
            "The implementation deliberately returns HTTP 503 in this test.\n",
            "The test fixture contains Error: write EPIPE\n",
            "The implementation handles connect ETIMEDOUT correctly.\n",
            "The test fixture contains TypeError: fetch failed\n",
            "TypeError: fetch failed is expected by this test.\n",
            "TypeError: invalid URL\n",
        )
        for text in prose:
            with self.subTest(text=text):
                self.assertFalse(final_diagnostic_has_transient_failure(text))


if __name__ == "__main__":
    unittest.main()
