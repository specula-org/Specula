"""Boundary tests for provider-policy error classification."""

from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

SRC = Path(__file__).resolve().parents[2] / "src"
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from specula.adapters.utils.policy import (  # noqa: E402
    failed_log_has_policy_block,
    final_diagnostic_has_policy_block,
    looks_policy_blocked,
)


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

    def test_missing_failed_log_is_not_a_policy_block(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            self.assertFalse(failed_log_has_policy_block(Path(raw) / "missing.log"))


if __name__ == "__main__":
    unittest.main()
