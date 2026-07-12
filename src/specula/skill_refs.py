"""Stable Specula skill identifiers used in agent prompts."""

from __future__ import annotations

CODEX_PLUGIN_NAME = "specula-codex"


def prompt_skill_ids(name: str) -> str:
    """Describe both standalone and Codex plugin-only IDs for one skill."""
    return f"**{name}** (or **{CODEX_PLUGIN_NAME}:{name}** in Codex plugin-only installations)"
