"""Delegation guidance for the single-session main session."""

from __future__ import annotations

import re
from pathlib import Path

import pytest

from specula import delegation, notes
from specula.prompts import PROMPTS_DIR, render

WORK = Path("/W")


@pytest.fixture(autouse=True)
def _clean_environment(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.delenv(delegation.DELEGATION_ENV, raising=False)


def test_guidance_is_on_by_default(monkeypatch: pytest.MonkeyPatch) -> None:
    assert delegation.enabled()
    section = delegation.delegation_section(WORK)
    assert section.startswith("\n## Parallel Subagents\n")
    assert section == "\n" + render("single-session/delegation", notes_dir="/W/notes")
    assert "`/W/notes/sub-<topic>.md`" in section and "{{" not in section
    assert delegation.delegation_pointer() == delegation.POINTER
    for value in ("on", "1", "yes", "anything"):
        monkeypatch.setenv(delegation.DELEGATION_ENV, value)
        assert delegation.enabled()


@pytest.mark.parametrize("value", ["off", "OFF", " 0 ", "false", "no"])
def test_off_spellings_remove_section_and_pointer(value: str, monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setenv(delegation.DELEGATION_ENV, value)
    assert not delegation.enabled()
    assert delegation.delegation_section(WORK) == "" and delegation.delegation_pointer() == ""


def test_subagent_notes_path_does_not_depend_on_the_notes_section(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setenv(notes.NOTES_ENV, "off")
    assert "`/W/notes/sub-<topic>.md`" in delegation.delegation_section(WORK)


def test_guidance_is_short_and_covers_when_to_delegate_and_when_not() -> None:
    text = (PROMPTS_DIR / "single-session/delegation.md").read_text()
    assert len(text.splitlines()) <= 20 and set(re.findall(r"\{\{(\w+)\}\}", text)) == {"notes_dir"}
    for expected in (
        "The skills' parallelization guidance applies as written",
        "one subagent per major source file",
        "Only you write the shared artifacts",
        "`file:line` evidence",
        "`{{notes_dir}}/sub-<topic>.md`",
        "appends each result as soon as it has verified it",
        "its final reply is a short summary and that path",
        "Put this in every subagent prompt",
        "missing, truncated, or blocked",
        "re-cover the scope",
        "Subagents may build the system and run probe programs",
        "Case A/B/C triage",
        "challenge them",
        "fidelity against the code",
        "counterexample derivation in progress",
        "Do not start confirmation agents",
        "in the foreground",
        "integrate their results before you end your turn",
    ):
        assert expected in text, expected
    for removed in ("is your decision", "read-only investigations", "reproduction agents"):
        assert removed not in text, removed
