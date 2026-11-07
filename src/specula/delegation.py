"""Delegation guidance for the continuous main session.

One continuous session performs every Phase 1-3 stage. The stage skills'
parallelization guidance applies as written; ``prompts/delegation.md`` adds the
main-session rules on top: shared artifacts stay with the main agent, each
subagent records its verified results in its own notes file as it goes (so a
missing or blocked final reply loses nothing), and the main agent re-covers any
scope whose results it did not receive. It is guidance, not a gate: nothing
checks for subagent use.

``SPECULA_DELEGATION=off`` (also ``0``/``false``/``no``) removes the section and
its continuation pointer, so main-session prompts are exactly what they were
before the guidance existed.
"""

from __future__ import annotations

import os
from pathlib import Path

from specula.notes import notes_dir
from specula.prompts import render

DELEGATION_ENV = "SPECULA_DELEGATION"
_DISABLED = frozenset({"0", "false", "no", "off"})
POINTER = (
    "The Parallel Subagents guidance in your original prompt still applies: follow the skills' parallelization "
    "guidance, have each subagent record its results in its own notes file as it goes, re-cover any scope whose "
    "results you did not receive, and write the shared artifacts yourself."
)


def enabled() -> bool:
    """Whether the delegation guidance is on (the default)."""
    return os.environ.get(DELEGATION_ENV, "").strip().lower() not in _DISABLED


def delegation_section(work_dir: Path) -> str:
    """The main-session guidance section for ``work_dir``, starting with a blank line; ``""`` when off.

    Subagent notes files live in the working-notes directory whether or not the
    notes section itself is on: they carry delegated results, not working memory.
    """
    return "\n" + render("delegation", notes_dir=str(notes_dir(work_dir))) if enabled() else ""


def delegation_pointer() -> str:
    """One line for a continuation after compaction; ``""`` when off."""
    return POINTER if enabled() else ""
