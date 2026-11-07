"""Boundary tests for provider-policy error classification."""

from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path

SRC = Path(__file__).resolve().parents[2] / "src"
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from specula.adapters.utils.event_stream import StreamStatus, stream_events  # noqa: E402
from specula.adapters.utils.policy import (  # noqa: E402
    failed_log_has_policy_block,
    final_diagnostic_has_policy_block,
    looks_claude_safeguard_block,
    looks_policy_blocked,
    refusal_policy_block,
)

# Claude Code 2.1.316's final stream-json result for a real-time cyber
# safeguard block (session, request, and message IDs sanitized).
CLAUDE_CYBER_REFUSAL = Path(__file__).resolve().parent / "fixtures" / "claude-cyber-refusal.result.json"


def claude_cyber_refusal() -> dict[str, object]:
    record = json.loads(CLAUDE_CYBER_REFUSAL.read_text(encoding="utf-8"))
    assert isinstance(record, dict)
    return record


class TestPolicyErrorPayload(unittest.TestCase):
    """The caller has already established that each payload is an error."""

    def test_typed_policy_codes(self) -> None:
        cases = (
            {"code": "cyber_policy"},
            {"errorCode": "CYBER-POLICY"},
            {"error_code": "content_policy_violation"},
            {"errorType": "content-policy-violation"},
        )
        for payload in cases:
            with self.subTest(payload=payload):
                self.assertTrue(looks_policy_blocked(payload))

    def test_narrow_policy_text_fallbacks(self) -> None:
        messages = (
            "Output blocked by content filtering policy",
            "Your previous response was blocked by the model's content filter.",
            "This content was flagged for possible cybersecurity risk.",
        )
        for message in messages:
            with self.subTest(message=message):
                self.assertTrue(looks_policy_blocked({"message": message}))

    def test_generic_http_400_is_not_a_policy_block(self) -> None:
        cases = (
            {
                "statusCode": 400,
                "code": "invalid_request_error",
                "message": "Invalid parameter: messages",
            },
            {
                "error": {
                    "status": 400,
                    "type": "bad_request",
                    "message": "The request body could not be parsed",
                }
            },
        )
        for payload in cases:
            with self.subTest(payload=payload):
                self.assertFalse(looks_policy_blocked(payload))

    def test_text_fallback_does_not_match_broad_policy_language(self) -> None:
        messages = (
            "The request was rejected by policy",
            "Cybersecurity analysis failed before producing a result",
            "The output filter returned no rows",
        )
        for message in messages:
            with self.subTest(message=message):
                self.assertFalse(looks_policy_blocked({"message": message}))

    def test_claude_safeguard_diagnostic_is_recognized(self) -> None:
        result = claude_cyber_refusal()["result"]
        messages = (
            result,
            "API Error: Opus 4.8's safeguards flagged this message.",
            "API Error: Sonnet 5's safeguards flagged this message. Learn more: https://example.invalid",
            "Details: `[cyber]`",
            "Details: [cyber]",
        )
        for message in messages:
            with self.subTest(message=message):
                self.assertTrue(looks_claude_safeguard_block(message))
                # The wording is Claude Code's: shared provider-error
                # classification for other adapters is unchanged.
                self.assertFalse(looks_policy_blocked(message))
                self.assertFalse(looks_policy_blocked({"message": message}))

    def test_prose_about_cyber_safeguards_is_not_a_policy_block(self) -> None:
        # Even inside an error envelope, ordinary words are not a verdict: only
        # the safeguard's own wording or its details marker are.
        messages = (
            "API Error: 400 invalid_request_error: messages.0.content is empty",
            "API Error: Request was aborted.",
            "The confirmation report reviews the cyber safeguards in auth.c; no bypass was found.",
            "Our safeguards flagged messages from the fuzzing corpus as malformed.",
            "The harness reported a cybersecurity-relevant race in the session cache.",
            "Details: cyber-defense module timed out",
            "Details: `[network]`",
        )
        for message in messages:
            with self.subTest(message=message):
                self.assertFalse(looks_claude_safeguard_block(message))
                self.assertFalse(looks_policy_blocked(message))
                self.assertFalse(looks_policy_blocked({"message": message}))
        self.assertFalse(looks_claude_safeguard_block({"message": "safeguards flagged this message"}))

    def test_refusal_policy_block_requires_a_refusal_stop(self) -> None:
        self.assertTrue(refusal_policy_block(claude_cyber_refusal()))
        self.assertTrue(refusal_policy_block({"stop_reason": "REFUSAL"}))
        for record in (
            {"stop_reason": "end_turn"},
            {"stop_reason": None},
            {"stop_reason": ["refusal"]},
            {"result": "stop_reason: refusal"},
            {},
        ):
            with self.subTest(record=record):
                self.assertFalse(refusal_policy_block(record))

    def test_refusal_with_api_status_or_transient_failure_is_not_a_policy_block(self) -> None:
        refusal = claude_cyber_refusal()
        for status in (None, "", 0, "0"):
            with self.subTest(status=status):
                self.assertTrue(refusal_policy_block({**refusal, "api_error_status": status}))
        for status in (429, "429", 500, 503, 529, "529", 400):
            with self.subTest(status=status):
                self.assertFalse(refusal_policy_block({**refusal, "api_error_status": status}))
        for result in ("API Error: Connection reset by server.", "Selected model is at capacity."):
            with self.subTest(result=result):
                self.assertFalse(refusal_policy_block({**refusal, "result": result}))

    def test_deeply_nested_provider_error_is_recognized(self) -> None:
        payload = {
            "error": {
                "data": {
                    "response": {
                        "body": {
                            "error_code": "content_policy_violation",
                        }
                    }
                }
            }
        }

        self.assertTrue(looks_policy_blocked(payload))

    def test_recursion_is_bounded(self) -> None:
        payload = {
            "error": {
                "error": {
                    "error": {
                        "error": {
                            "error": {
                                "code": "cyber_policy",
                            }
                        }
                    }
                }
            }
        }

        self.assertFalse(looks_policy_blocked(payload))


class TestFailedLogPolicyFallback(unittest.TestCase):
    def test_failed_log_with_observed_cybersecurity_message(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            log = Path(raw) / "agent.log"
            log.write_text(
                "HTTP 400: This content was flagged for possible cybersecurity risk.\n",
                encoding="utf-8",
            )

            self.assertTrue(failed_log_has_policy_block(log))

    def test_failed_log_with_typed_cyber_policy_code(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            log = Path(raw) / "agent.log"
            log.write_text("HTTP 400: error code=cyber_policy\n", encoding="utf-8")

            self.assertTrue(failed_log_has_policy_block(log))

    def test_failed_log_with_generic_400_is_not_a_policy_block(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            log = Path(raw) / "agent.log"
            log.write_text("HTTP 400: invalid request body\n", encoding="utf-8")

            self.assertFalse(failed_log_has_policy_block(log))

    def test_failed_log_fallback_scans_only_the_recent_tail(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            log = Path(raw) / "agent.log"
            log.write_text(
                "output blocked by content filtering policy\n" + ("x" * 300_000),
                encoding="utf-8",
            )
            self.assertFalse(failed_log_has_policy_block(log))

            log.write_text(
                ("x" * 300_000) + "\noutput blocked by content filtering policy\n",
                encoding="utf-8",
            )
            self.assertTrue(failed_log_has_policy_block(log))

    def test_quoted_policy_text_before_unrelated_failure_is_not_a_policy_block(self) -> None:
        text = (
            "The agent report quoted: output blocked by content filtering policy.\nfatal: unrelated transport failure\n"
        )

        self.assertFalse(final_diagnostic_has_policy_block(text))

    def test_json_shaped_policy_text_is_not_a_plain_diagnostic(self) -> None:
        text = '{"type":"session.error","data":{"message":"content policy blocked response"}}\n'

        self.assertFalse(final_diagnostic_has_policy_block(text))

    def test_copilot_stats_footer_is_not_scanned_backward(self) -> None:
        text = (
            "HTTP 400: This content was flagged for possible cybersecurity risk.\n\n"
            "Changes    +0 -0\n"
            "Requests   1 Premium (10s)\n"
            "Tokens     ↑ 29.9k (11.0k cached) • ↓ 5\n"
            "Resume this session with: copilot --resume=example\n"
        )

        self.assertFalse(final_diagnostic_has_policy_block(text))

    def test_final_diagnostic_looks_past_request_and_message_ids(self) -> None:
        result = claude_cyber_refusal()["result"]
        assert isinstance(result, str)
        self.assertTrue(result.rstrip().endswith("Message ID: msg_000000000000000000000000"))
        cases = (
            result,
            result + "\n",
            "HTTP 400: This content was flagged for possible cybersecurity risk.\nrequest_id=req_123\n",
            "API Error: Opus 4.8's safeguards flagged this message.\n\nRequest ID: req_1\n\nMessage ID: msg_2\n",
        )
        for text in cases:
            with self.subTest(text=text):
                self.assertTrue(final_diagnostic_has_policy_block(text, claude=True))
                # Other adapters' fallbacks keep the plain final-line rule.
                self.assertFalse(final_diagnostic_has_policy_block(text))

    def test_id_trailers_do_not_reach_past_an_unrelated_final_diagnostic(self) -> None:
        cases = (
            "fatal: unrelated transport failure\n\nRequest ID: req_1\n\nMessage ID: msg_2\n",
            (
                "The agent report quoted: Opus 4.8's safeguards flagged this message.\n"
                "fatal: unrelated transport failure\n"
                "Request ID: req_1\n"
            ),
            "Request ID: req_1\nMessage ID: msg_2\n",
            # A trailer-shaped line with more text is ordinary output.
            "safeguards flagged this message\nRequest ID: req_1 was retried successfully\n",
        )
        for text in cases:
            with self.subTest(text=text):
                self.assertFalse(final_diagnostic_has_policy_block(text, claude=True))
                self.assertFalse(final_diagnostic_has_policy_block(text))

    def test_failed_log_fallback_does_not_skip_id_lines(self) -> None:
        # Copilot's text-mode log is the agent transcript: a quoted diagnostic
        # followed by an ID line must not become a policy block.
        transcripts = (
            "The earlier run said: This content was flagged for possible cybersecurity risk.\nRequest ID: req_1\n",
            "The earlier run said: Opus 4.8's safeguards flagged this message.\nRequest ID: req_1\n",
            str(claude_cyber_refusal()["result"]) + "\n",
        )
        for text in transcripts:
            with self.subTest(text=text), tempfile.TemporaryDirectory() as raw:
                log = Path(raw) / "agent.log"
                log.write_text(text, encoding="utf-8")

                self.assertFalse(failed_log_has_policy_block(log))

    def test_missing_failed_log_is_not_a_policy_block(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            self.assertFalse(failed_log_has_policy_block(Path(raw) / "missing.log"))


def _assistant(text: str) -> dict[str, object]:
    return {"type": "assistant", "message": {"content": [{"type": "text", "text": text}]}}


def _success(text: str) -> dict[str, object]:
    return {
        "type": "result",
        "subtype": "success",
        "is_error": False,
        "stop_reason": "end_turn",
        "terminal_reason": "completed",
        "session_id": "00000000-0000-4000-8000-000000000001",
        "result": text,
    }


class TestClaudeSafeguardStream(unittest.TestCase):
    """Only Claude's failed terminal result may classify a safeguard block."""

    def stream(self, lines: list[object], adapter: str = "claude-code") -> StreamStatus:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            source = [(line if isinstance(line, str) else json.dumps(line)).encode() + b"\n" for line in lines]
            return stream_events(adapter, root / "activity.jsonl", root / "agent.log", source)

    def test_refusal_result_is_a_policy_block(self) -> None:
        status = self.stream([_assistant("Reproducing the race."), claude_cyber_refusal()])

        self.assertIsNotNone(status.policy_block_error)
        self.assertIn("safeguards flagged this message", status.policy_block_error or "")
        self.assertFalse(status.successful_terminal)

    def test_failed_refusal_is_recognized_without_known_wording(self) -> None:
        record = claude_cyber_refusal()
        record["result"] = "API Error: the request could not be completed."

        self.assertIsNotNone(self.stream([record]).policy_block_error)

    def test_assistant_prose_quoting_the_safeguard_is_not_a_policy_block(self) -> None:
        quoted = str(claude_cyber_refusal()["result"])
        report = f"The previous run failed with:\n{quoted}\nThe cyber safeguards were not involved here.\nVERDICT: FALSE POSITIVE"
        cases: tuple[tuple[str, list[object]], ...] = (
            ("assistant-then-success", [_assistant(quoted), _success(report)]),
            ("success-report", [_success(report)]),
            (
                "assistant-then-generic-failure",
                [
                    _assistant(quoted),
                    {
                        "type": "result",
                        "subtype": "success",
                        "is_error": True,
                        "stop_reason": "end_turn",
                        "terminal_reason": "api_error",
                        "api_error_status": 400,
                        "result": "API Error: 400 invalid_request_error",
                    },
                ],
            ),
            # The refusal stop alone never reclassifies a successful envelope.
            ("successful-envelope-refusal", [{**_success(report), "stop_reason": "refusal"}]),
        )
        for name, lines in cases:
            with self.subTest(name):
                status = self.stream(lines)
                self.assertIsNone(status.policy_block_error)
                self.assertIsNone(status.plain_policy_block_error)

    def test_plain_safeguard_diagnostic_with_id_trailers(self) -> None:
        result = str(claude_cyber_refusal()["result"])
        status = self.stream([_assistant("working"), *result.splitlines()])

        self.assertIsNotNone(status.plain_policy_block_error)
        self.assertIn("safeguards flagged this message", status.plain_policy_block_error or "")

    def test_other_adapters_keep_the_final_plain_line_rule(self) -> None:
        lines: list[object] = [
            "HTTP 400: This content was flagged for possible cybersecurity risk.",
            "Request ID: req_1",
        ]
        for adapter in ("codex", "copilot-json", "opencode", "pi"):
            with self.subTest(adapter=adapter):
                self.assertIsNone(self.stream(lines, adapter).plain_policy_block_error)
        self.assertIsNotNone(self.stream(lines).plain_policy_block_error)

    def test_plain_tail_never_merges_unterminated_lines(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            source = [b"quoted: output blocked by content filtering policy", b"fatal: unrelated failure"]
            status = stream_events("claude-code", root / "activity.jsonl", root / "agent.log", source)

        self.assertIsNone(status.plain_policy_block_error)

    def test_later_json_event_supersedes_plain_safeguard_diagnostic(self) -> None:
        result = str(claude_cyber_refusal()["result"])
        status = self.stream([*result.splitlines(), _assistant("recovered")])

        self.assertIsNone(status.plain_policy_block_error)


if __name__ == "__main__":
    unittest.main()
