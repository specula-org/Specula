"""Externalized agent-prompt templates for the Specula phases.

Prompts live as markdown files under this package (e.g. `confirmation/reproduce.md`),
NOT inline in the phase code, so they can be edited and reviewed without touching
Python. Placeholders are `{{name}}`; the double-brace delimiter avoids clashing
with the literal `{`/`}` in JSON examples that `str.format` would choke on. A
placeholder present in the template without a matching substitution is an error;
placeholder-looking text supplied as data remains literal.

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

    Substitutions are performed in one pass.  Placeholder-looking text inside a
    value is data, not another template fragment, and is therefore never
    expanded (or reported as an unfilled template placeholder).

    Raises KeyError if the template contains a placeholder absent from ``subs``.
    """
    text = (PROMPTS_DIR / f"{template}.md").read_text()

    missing = sorted({key for key in _PLACEHOLDER.findall(text) if key not in subs})
    if missing:
        raise KeyError(f"unfilled placeholder(s) in {template}.md: {missing}")
    return _PLACEHOLDER.sub(lambda match: str(subs[match.group(1)]), text)
