"""The Modeling Brief handoff: ``modeling-brief.md`` and its companion documents.

Code analysis may split a large brief into companion documents named
``modeling-brief-<topic>.md`` beside the brief. Later readers take the whole set.
"""

from __future__ import annotations

from pathlib import Path

BRIEF = "modeling-brief.md"
COMPANIONS = "modeling-brief-*.md"


def companions(work: Path) -> list[Path]:
    """The brief's companion documents in name order."""
    return [path for path in sorted(work.glob(COMPANIONS)) if path.is_file()]


def documents(work: Path) -> list[Path]:
    """The brief, when present, followed by its companion documents."""
    brief = work / BRIEF
    return [brief, *companions(work)] if brief.is_file() else companions(work)


def listing(work: Path) -> str:
    """Backquoted paths of the brief and its companions; the brief path alone when none exists."""
    return ", ".join(f"`{path}`" for path in documents(work) or [work / BRIEF])
