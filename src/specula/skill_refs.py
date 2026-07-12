"""Stable Specula skill identifiers used in agent prompts."""

from __future__ import annotations

CODEX_PLUGIN_NAME = "specula-codex"


def prompt_skill_ids(name: str) -> str:
    """Name one skill portably and make Codex's two installation IDs explicit."""
    return (
        f"**{name}** (Codex: explicitly invoke exactly one ID listed in your Skills — "
        f"prefer ${CODEX_PLUGIN_NAME}:{name} when it is listed; otherwise use ${name}. "
        "Never invoke both or an ID that is not listed)"
    )
