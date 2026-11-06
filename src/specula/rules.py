"""Pinned hard rules for every Specula agent session.

Long sessions lose instructions to context compaction, and continuation prompts
(transient/policy/manual resume) carry none of the original phase prompt. The
rules in ``prompts/rules.md`` are the few skill requirements whose violation
invalidates a run's results; they are restated at the start of every prompt the
launcher writes and, where the agent CLI supports it, in its system prompt.

``SPECULA_RULES=off`` (also ``0``/``false``/``no``) disables both, restoring the
exact pre-rules prompts and adapter arguments.

Keep ``rules.md`` short and free of process-name tokens (for example the model
checker's class name or ``java``): some adapters pass the text in the CLI's
argv, where an agent's ``pkill -f <pattern>`` could otherwise match its own
session process.
"""

from __future__ import annotations

import os

from specula.prompts import PROMPTS_DIR

RULES_ENV = "SPECULA_RULES"
RULES_TITLE = "# Specula hard rules"
RULES_SEPARATOR = "\n---\n\n"
_OFF_VALUES = frozenset({"0", "false", "no", "off"})


def enabled() -> bool:
    """Whether rule pinning is on (the default)."""
    return os.environ.get(RULES_ENV, "").strip().lower() not in _OFF_VALUES


def rules_block() -> str:
    """The titled rules block, or ``""`` when ``SPECULA_RULES=off``."""
    if not enabled():
        return ""
    body = (PROMPTS_DIR / "rules.md").read_text(encoding="utf-8").strip()
    return f"{RULES_TITLE}\n\n{body}\n"


def with_rules(prompt: str) -> str:
    """Prepend the rules block to ``prompt``; identity when rules are off."""
    block = rules_block()
    if not block:
        return prompt
    return f"{block}{RULES_SEPARATOR}{prompt}"
