"""Tests for the pinned hard-rules block (specula.rules, prompts/rules.md)."""

from __future__ import annotations

import os
import re
import unittest
from unittest import mock

from specula import rules
from specula.prompts import PROMPTS_DIR

RULES_MD = PROMPTS_DIR / "rules.md"


class RulesText(unittest.TestCase):
    def test_rules_file_is_short_and_self_contained(self) -> None:
        text = RULES_MD.read_text(encoding="utf-8")
        self.assertLessEqual(len(text.splitlines()), 40)
        self.assertNotIn("{{", text)  # never a template: no placeholder can go unfilled
        self.assertFalse(text.lstrip().startswith("#"), "the title belongs to rules_block()")

    def test_rules_cover_the_result_invalidating_requirements(self) -> None:
        text = RULES_MD.read_text(encoding="utf-8")
        for required in (
            "Never fabricate",
            "`REPRODUCED`",
            "`ENV_LIMITED`",
            "`MASKED`",
            "model-only",
            "actually execute",
            "background",
            "`BLOCKED.md`",
            "read-only",
            "compaction",
        ):
            with self.subTest(required=required):
                self.assertIn(required, text)

    def test_rules_avoid_process_name_tokens(self) -> None:
        # Some adapters put the text in the CLI argv; an agent's `pkill -f TLC`
        # or `pkill -f java` must never match its own session process.
        text = rules.rules_block()
        for token in ("tlc", "java", "tla2tools", "wait_for_pid"):
            with self.subTest(token=token):
                self.assertNotRegex(text, re.compile(re.escape(token), re.IGNORECASE))


class RulesToggle(unittest.TestCase):
    def setUp(self) -> None:
        patcher = mock.patch.dict(os.environ)
        patcher.start()
        self.addCleanup(patcher.stop)
        os.environ.pop(rules.RULES_ENV, None)

    def test_block_is_titled_rules_text(self) -> None:
        block = rules.rules_block()
        body = RULES_MD.read_text(encoding="utf-8").strip()
        self.assertEqual(block, f"{rules.RULES_TITLE}\n\n{body}\n")

    def test_with_rules_prepends_block_once(self) -> None:
        prompt = "# Task\n\nDo the work.\n"
        pinned = rules.with_rules(prompt)
        self.assertEqual(pinned, rules.rules_block() + rules.RULES_SEPARATOR + prompt)
        self.assertTrue(pinned.endswith(prompt))
        self.assertEqual(pinned.count(rules.RULES_TITLE), 1)

    def test_with_rules_is_idempotent(self) -> None:
        pinned = rules.with_rules("# Task\n")
        self.assertEqual(rules.with_rules(pinned), pinned)
        self.assertEqual(rules.with_rules(rules.with_rules(pinned)).count(rules.RULES_TITLE), 1)
        # A prompt that merely mentions the title elsewhere is still pinned.
        quoted = f"Quote:\n{rules.rules_block()}"
        self.assertEqual(rules.with_rules(quoted), rules.rules_block() + rules.RULES_SEPARATOR + quoted)

    def test_off_values_disable_rules_entirely(self) -> None:
        for value in ("off", "OFF", " off ", "0", "false", "no"):
            with self.subTest(value=value):
                os.environ[rules.RULES_ENV] = value
                self.assertFalse(rules.enabled())
                self.assertEqual(rules.rules_block(), "")
                self.assertEqual(rules.with_rules("exact prompt\n"), "exact prompt\n")
                self.assertEqual(rules.with_rules(""), "")

    def test_identity_is_the_path_free_template_text_and_empty_when_off(self) -> None:
        self.assertEqual(rules.rules_identity(), RULES_MD.read_text(encoding="utf-8"))
        os.environ[rules.RULES_ENV] = "off"
        self.assertEqual(rules.rules_identity(), "")

    def test_other_values_keep_rules_on(self) -> None:
        for value in ("", "on", "1", "yes"):
            with self.subTest(value=value):
                os.environ[rules.RULES_ENV] = value
                self.assertTrue(rules.enabled())
                self.assertTrue(rules.rules_block().startswith(rules.RULES_TITLE))


if __name__ == "__main__":
    unittest.main()
