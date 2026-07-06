"""Externalized agent-prompt templates for the Specula phases.

Prompts live as markdown files under this package (e.g. `confirmation/reproduce.md`),
NOT inline in the phase code, so they can be edited and reviewed without touching
Python. Placeholders are `{{name}}`; the double-brace delimiter avoids clashing
with the literal `{`/`}` in JSON examples that `str.format` would choke on. An
unfilled `{{placeholder}}` after substitution is an error — it catches typos and
renamed fields at render time rather than shipping a half-filled prompt.

Templates are addressed by their path under this dir without the extension:
`render("confirmation/reproduce", finding_id=...)` reads `confirmation/reproduce.md`.
"""

from __future__ import annotations

import re
from pathlib import Path

PROMPTS_DIR = Path(__file__).resolve().parent
_PLACEHOLDER = re.compile(r"\{\{(\w+)\}\}")


def render(template: str, **subs: str) -> str:
    """Read `<template>.md` under this package and replace every `{{key}}` with subs[key].

    Raises KeyError if any `{{placeholder}}` is left unfilled after substitution.
    """
    text = (PROMPTS_DIR / f"{template}.md").read_text()
    for k, v in subs.items():
        text = text.replace("{{" + k + "}}", v)
    leftover = sorted(set(_PLACEHOLDER.findall(text)))
    if leftover:
        raise KeyError(f"unfilled placeholder(s) in {template}.md: {leftover}")
    return text
