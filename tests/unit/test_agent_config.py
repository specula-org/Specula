"""Unit tests for strict agent configuration loading and routing."""

from __future__ import annotations

import hashlib
import json
import tempfile
import unittest
from pathlib import Path

from specula.agent_config import AgentConfigError, AgentSelection, load_agent_routing


def _valid_config() -> dict[str, object]:
    return {
        "version": 1,
        "default_profile": "claude",
        "profiles": {
            "claude": {"agent": "claude-code"},
            "codex": {"agent": "codex", "model": "", "effort": ""},
            "copilot": {"agent": "copilot-cli", "model": "gpt-5-mini", "effort": "low"},
        },
        "phases": {
            "analyze": "codex",
            "validate": "copilot",
        },
    }


class AgentConfigTest(unittest.TestCase):
    def load(self, payload: object) -> object:
        with tempfile.TemporaryDirectory() as raw:
            path = Path(raw) / "agents.json"
            path.write_text(json.dumps(payload), encoding="utf-8")
            return load_agent_routing(path)

    def assert_invalid(self, payload: object, message: str) -> None:
        with self.assertRaisesRegex(AgentConfigError, message):
            self.load(payload)

    def test_resolves_explicit_fallback_and_default_profiles(self) -> None:
        path = self._write(_valid_config())
        routing = load_agent_routing(path)

        self.assertEqual(routing.default, AgentSelection("claude-code"))
        self.assertEqual(routing.resolve("analyze"), AgentSelection("codex", "", ""))
        self.assertEqual(
            routing.resolve("repair", fallback="validate"), AgentSelection("copilot-cli", "gpt-5-mini", "low")
        )
        self.assertEqual(routing.resolve("confirm"), routing.default)
        self.assertEqual(routing.source_sha256, hashlib.sha256(path.read_bytes()).hexdigest())

    def test_phases_are_optional(self) -> None:
        payload = _valid_config()
        del payload["phases"]

        routing = load_agent_routing(self._write(payload))

        self.assertEqual(routing.resolve("analyze"), routing.default)

    def test_reports_read_and_json_errors_with_the_path(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            missing = Path(raw) / "missing.json"
            with self.assertRaisesRegex(AgentConfigError, rf"cannot read agent config {missing}"):
                load_agent_routing(missing)

            invalid = Path(raw) / "invalid.json"
            invalid.write_text("{", encoding="utf-8")
            with self.assertRaisesRegex(AgentConfigError, rf"invalid JSON in agent config {invalid} at line 1"):
                load_agent_routing(invalid)

            invalid_utf8 = Path(raw) / "invalid-utf8.json"
            invalid_utf8.write_bytes(b"\xff")
            with self.assertRaisesRegex(AgentConfigError, rf"cannot read agent config {invalid_utf8}"):
                load_agent_routing(invalid_utf8)

    def test_rejects_invalid_top_level_fields(self) -> None:
        cases: tuple[tuple[object, str], ...] = (
            ([], "agent config must be a JSON object"),
            ({"version": 1}, "default_profile"),
            ({**_valid_config(), "extra": True}, "unknown field 'extra'"),
            ({**_valid_config(), "version": True}, "version"),
            ({**_valid_config(), "version": 2}, "version"),
            ({**_valid_config(), "default_profile": 1}, "default_profile"),
            ({**_valid_config(), "profiles": []}, "profiles.*JSON object"),
        )
        for payload, message in cases:
            with self.subTest(message=message):
                self.assert_invalid(payload, message)

    def test_rejects_invalid_profiles(self) -> None:
        cases: tuple[tuple[object, str], ...] = (
            (
                {
                    **_valid_config(),
                    "profiles": {"claude": {"agent": "claude-code", "extra": True}},
                },
                "profile 'claude'.*unknown field 'extra'",
            ),
            ({**_valid_config(), "profiles": {"claude": []}}, "profile 'claude'.*JSON object"),
            ({**_valid_config(), "profiles": {"claude": {}}}, "agent.*non-empty string"),
            ({**_valid_config(), "profiles": {"claude": {"agent": ""}}}, "agent.*non-empty string"),
            ({**_valid_config(), "profiles": {"claude": {"agent": 1}}}, "agent.*non-empty string"),
            (
                {**_valid_config(), "profiles": {"claude": {"agent": "claude-code", "model": None}}},
                "model.*string",
            ),
            (
                {**_valid_config(), "profiles": {"claude": {"agent": "claude-code", "effort": 1}}},
                "effort.*string",
            ),
            ({**_valid_config(), "default_profile": "missing"}, "default profile 'missing' does not exist"),
        )
        for payload, message in cases:
            with self.subTest(message=message):
                self.assert_invalid(payload, message)

    def test_rejects_invalid_phase_routes(self) -> None:
        cases: tuple[tuple[object, str], ...] = (
            ({**_valid_config(), "phases": []}, "phases.*JSON object"),
            ({**_valid_config(), "phases": {"analysis": "codex"}}, "unknown phase 'analysis'"),
            ({**_valid_config(), "phases": {"analyze": 1}}, "phase 'analyze'.*profile by name"),
            ({**_valid_config(), "phases": {"analyze": "missing"}}, "unknown profile 'missing'"),
        )
        for payload, message in cases:
            with self.subTest(message=message):
                self.assert_invalid(payload, message)

    def _write(self, payload: object) -> Path:
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        path = Path(directory.name) / "agents.json"
        path.write_text(json.dumps(payload), encoding="utf-8")
        return path


if __name__ == "__main__":
    unittest.main()
