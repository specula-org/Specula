"""Free working-notes area for pipeline agents.

Agents may keep working notes under ``<work_dir>/notes/``, listed one line per
entry in ``notes/INDEX.md``. The notes are optional working memory: no phase
gates on them and no pipeline code consumes them; the output index only links
``INDEX.md`` when it exists. This module renders the prompt section that tells
each agent about the area (``prompts/notes.md``; per-finding confirmation
workers get the read-only ``prompts/notes-worker.md``).

``SPECULA_NOTES=off`` (also ``0``/``false``/``no``) disables every section, so
prompts are exactly what they were before the notes area existed.
"""

from __future__ import annotations

import os
from pathlib import Path

from specula.prompts import PROMPTS_DIR, render

NOTES_ENV = "SPECULA_NOTES"
NOTES_DIRNAME = "notes"
INDEX_FILENAME = "INDEX.md"
WORKER_TEMPLATE = "notes-worker"
_DISABLED = frozenset({"0", "false", "no", "off"})

# Phase 1 opens the area. A prior attempt in the same workspace may have left
# notes, so the agent reads (and verifies) rather than blindly trusting them.
_START_FIRST = (
    "Start notes whenever something is worth keeping. If `INDEX.md` already exists from an earlier "
    "attempt in this workspace, read it first and verify what you reuse."
)
_START_LATER = (
    "Earlier phases may have left notes there: if `INDEX.md` exists, read it before you begin, "
    "and keep it current as you add or change notes."
)


def enabled() -> bool:
    """Whether the notes prompt sections are on (the default)."""
    return os.environ.get(NOTES_ENV, "").strip().lower() not in _DISABLED


def notes_dir(work_dir: Path) -> Path:
    return work_dir / NOTES_DIRNAME


def index_path(work_dir: Path) -> Path:
    return notes_dir(work_dir) / INDEX_FILENAME


def notes_section(work_dir: Path, *, first: bool) -> str:
    """Prompt section for a phase agent working in ``work_dir``.

    ``first=True`` is for the phase that opens the area (Phase 1); later phases
    are told to read ``INDEX.md`` first and keep it current. The section starts
    with a blank line so it can be appended to a prompt ending in a newline.
    Returns ``""`` when notes are disabled.
    """
    if not enabled():
        return ""
    return "\n" + render(
        "notes",
        notes_dir=str(notes_dir(work_dir)),
        start=_START_FIRST if first else _START_LATER,
    )


def worker_notes_section(work_dir: Path, finding_dir: Path) -> str:
    """Read-only notes section for one per-finding confirmation turn.

    Workers run in parallel and judge one finding independently, so they may
    read the shared index for practical context but write only under their own
    finding directory. Returns ``""`` when notes are disabled.
    """
    if not enabled():
        return ""
    return "\n" + render(
        WORKER_TEMPLATE,
        notes_dir=str(notes_dir(work_dir)),
        finding_dir=str(finding_dir),
    )


def worker_notes_identity() -> str:
    """Path-free identity of the worker notes guidance, for verdict caching.

    Mirrors how confirmation fingerprints bind prompt templates rather than
    rendered (path-bearing) text; ``""`` when notes are disabled.
    """
    if not enabled():
        return ""
    return (PROMPTS_DIR / f"{WORKER_TEMPLATE}.md").read_text()
