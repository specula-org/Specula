"""Unit tests for the free working-notes prompt sections (src/specula/notes.py)."""

from __future__ import annotations

import os
import re
import unittest
from pathlib import Path
from unittest import mock

from specula import notes
from specula.prompts import PROMPTS_DIR

WORK = Path("/runs/demo/target/.specula-output")
FINDING = WORK / "confirmation" / "MC-1"


class NotesCase(unittest.TestCase):
    def setUp(self) -> None:
        patcher = mock.patch.dict(os.environ)
        patcher.start()
        self.addCleanup(patcher.stop)
        os.environ[notes.NOTES_ENV] = "on"


class TestNotesSection(NotesCase):
    def test_enabled_sections_append_to_a_prompt(self) -> None:
        self.assertTrue(notes.enabled())
        for first in (True, False):
            with self.subTest(first=first):
                section = notes.notes_section(WORK, first=first)
                self.assertTrue(section.startswith("\n## Working Notes\n\n"))
                self.assertTrue(section.endswith("\n"))
                self.assertIn(f"`{WORK / 'notes'}/`", section)
                self.assertIn("`INDEX.md`", section)
                self.assertNotRegex(section, r"\{\{\w+\}\}")

    def test_first_phase_opens_the_area_and_later_phases_read_the_index_first(self) -> None:
        first = notes.notes_section(WORK, first=True)
        later = notes.notes_section(WORK, first=False)
        self.assertIn("Start notes whenever something is worth keeping", first)
        self.assertIn("earlier attempt in this workspace, read it first and verify", first)
        self.assertNotIn("Earlier phases", first)
        self.assertIn("if `INDEX.md` exists, read it before you begin", later)
        self.assertIn("keep it current", later)
        self.assertNotIn("Start notes", later)
        # Only the opening sentence differs; the guidance itself is shared.
        self.assertEqual(first.split("\n\n", 2)[2], later.split("\n\n", 2)[2])

    def test_guidance_names_what_to_record_without_making_notes_a_deliverable(self) -> None:
        text = re.sub(r"\s+", " ", notes.notes_section(WORK, first=False))
        for topic in (
            "modeling decisions and the evidence behind them",
            "approaches you rejected, and why",
            "coverage ledger of the source files and commits you have reviewed",
            "assumptions you have not verified yet",
            "commands and log paths of long-running jobs",
            "environment and build recipes",
            "Send large outputs (build logs, TLC output) to files and read their tails or summaries",
            "Name and organize notes however you like",
            "not a deliverable",
            "nothing checks them",
            "never replace an output this task requires",
        ):
            self.assertIn(topic, text)

    def test_fragment_stays_short_because_it_is_injected_into_many_prompts(self) -> None:
        for template in ("notes.md", "notes-worker.md"):
            with self.subTest(template=template):
                lines = (PROMPTS_DIR / template).read_text().splitlines()
                self.assertLessEqual(len(lines), 20)

    def test_off_by_default_and_for_any_other_value(self) -> None:
        for value in (None, "", "off", "OFF", " off ", "0", "false", "no", "maybe"):
            with self.subTest(value=value):
                if value is None:
                    os.environ.pop(notes.NOTES_ENV, None)
                else:
                    os.environ[notes.NOTES_ENV] = value
                self.assertFalse(notes.enabled())
                self.assertEqual(notes.notes_section(WORK, first=True), "")
                self.assertEqual(notes.notes_section(WORK, first=False), "")
                self.assertEqual(notes.worker_notes_section(WORK, FINDING), "")
                self.assertEqual(notes.worker_notes_identity(), "")

    def test_on_values_enable_notes(self) -> None:
        for value in ("on", "ON", " on ", "1", "true", "yes"):
            with self.subTest(value=value):
                os.environ[notes.NOTES_ENV] = value
                self.assertTrue(notes.enabled())
                self.assertNotEqual(notes.notes_section(WORK, first=True), "")

    def test_paths(self) -> None:
        self.assertEqual(notes.notes_dir(WORK), WORK / "notes")
        self.assertEqual(notes.index_path(WORK), WORK / "notes" / "INDEX.md")


class TestWorkerNotesSection(NotesCase):
    def test_workers_read_the_shared_index_and_write_only_their_finding_dir(self) -> None:
        section = notes.worker_notes_section(WORK, FINDING)
        text = re.sub(r"\s+", " ", section)
        self.assertTrue(section.startswith("\n## Working Notes\n\n"))
        self.assertIn(f"`{WORK / 'notes'}/`", text)
        self.assertIn("If its `INDEX.md` exists, skim it for environment and build recipes", text)
        self.assertIn("Notes are not evidence", text)
        self.assertIn("unverified lead", text)
        self.assertIn("do not use them to read about other findings", text)
        self.assertIn("Do not edit the shared notes", text)
        self.assertIn(f"keep your own notes in your finding work dir `{FINDING}`", text)
        self.assertNotIn("keep it current", text)
        self.assertNotRegex(section, r"\{\{\w+\}\}")

    def test_identity_is_the_path_free_template(self) -> None:
        identity = notes.worker_notes_identity()
        self.assertEqual(identity, (PROMPTS_DIR / "notes-worker.md").read_text())
        self.assertIn("{{finding_dir}}", identity)
        self.assertNotIn(str(WORK), identity)


if __name__ == "__main__":
    unittest.main()
