"""Delegation guidance for the continuous main session."""

from __future__ import annotations

import pytest

from specula import delegation
from specula.prompts import PROMPTS_DIR


@pytest.fixture(autouse=True)
def _clean_environment(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.delenv(delegation.DELEGATION_ENV, raising=False)


def test_guidance_is_on_by_default(monkeypatch: pytest.MonkeyPatch) -> None:
    assert delegation.enabled()
    section = delegation.delegation_section()
    assert section.startswith("\n## Parallel Subagents\n")
    assert section == "\n" + (PROMPTS_DIR / "delegation.md").read_text()
    assert delegation.delegation_pointer() == delegation.POINTER
    for value in ("on", "1", "yes", "anything"):
        monkeypatch.setenv(delegation.DELEGATION_ENV, value)
        assert delegation.enabled()


@pytest.mark.parametrize("value", ["off", "OFF", " 0 ", "false", "no"])
def test_off_spellings_remove_section_and_pointer(value: str, monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setenv(delegation.DELEGATION_ENV, value)
    assert not delegation.enabled()
    assert delegation.delegation_section() == "" and delegation.delegation_pointer() == ""


def test_guidance_is_short_and_covers_when_to_delegate_and_when_not() -> None:
    text = (PROMPTS_DIR / "delegation.md").read_text()
    assert len(text.splitlines()) <= 20 and "{{" not in text
    for expected in (
        "is your decision",
        "Only you write the shared artifacts",
        "`file:line` evidence",
        "Case A/B/C triage",
        "challenge them",
        "fidelity against the code",
        "counterexample derivation in progress",
        "Do not start confirmation or reproduction agents",
        "in the foreground",
        "integrate their results before you end your turn",
    ):
        assert expected in text, expected
