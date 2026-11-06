"""Delegation guidance for the continuous main session.

One continuous session performs every Phase 1-3 stage, so heavy independent
reading can crowd its context or run serially. ``prompts/delegation.md`` says
when parallel subagents help and when the main agent should work alone; the
agent decides whether to delegate and how much. It is guidance, not a gate:
nothing checks for subagent use.

``SPECULA_DELEGATION=off`` (also ``0``/``false``/``no``) removes the section and
its continuation pointer, so main-session prompts are exactly what they were
before the guidance existed.
"""

from __future__ import annotations

import os

from specula.prompts import render

DELEGATION_ENV = "SPECULA_DELEGATION"
_DISABLED = frozenset({"0", "false", "no", "off"})
POINTER = (
    "The Parallel Subagents guidance in your original prompt still applies: delegate independent read-only "
    "investigations and clean-context reviews where they help, and write the shared artifacts yourself."
)


def enabled() -> bool:
    """Whether the delegation guidance is on (the default)."""
    return os.environ.get(DELEGATION_ENV, "").strip().lower() not in _DISABLED


def delegation_section() -> str:
    """The main-session guidance section, starting with a blank line; ``""`` when off."""
    return "\n" + render("delegation") if enabled() else ""


def delegation_pointer() -> str:
    """One line for a continuation after compaction; ``""`` when off."""
    return POINTER if enabled() else ""
