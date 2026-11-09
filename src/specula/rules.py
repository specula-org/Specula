"""Pinned hard rules for every Specula agent session.

Long sessions lose instructions to context compaction, and continuation prompts
(transient/policy/manual resume) carry none of the original phase prompt. The
rules in ``prompts/optional/rules.md`` are the few skill requirements whose violation
invalidates a run's results; they are restated at the start of every prompt the
launcher writes and, where the agent CLI supports it, in its system prompt.

Off by default, so prompts and adapter arguments are exactly what they were
before rule pinning. ``SPECULA_RULES=on`` (also ``1``/``true``/``yes``) enables
it; single-session orchestration turns it on unless the variable is set.

Keep ``rules.md`` short and free of process-name tokens (for example the model
checker's class name or ``java``): some adapters pass the text in the CLI's
argv, where an agent's ``pkill -f <pattern>`` could otherwise match its own
session process.
"""

from __future__ import annotations

import os

from specula.prompts import PROMPTS_DIR

RULES_ENV = "SPECULA_RULES"
RULES_TEMPLATE = "optional/rules.md"
RULES_TITLE = "# Specula hard rules"
RULES_SEPARATOR = "\n---\n\n"
_ON_VALUES = frozenset({"1", "true", "yes", "on"})


def enabled() -> bool:
    """Whether rule pinning is on (``SPECULA_RULES=on``; off by default)."""
    return os.environ.get(RULES_ENV, "").strip().lower() in _ON_VALUES


def rules_block() -> str:
    """The titled rules block, or ``""`` when rule pinning is off."""
    if not enabled():
        return ""
    body = (PROMPTS_DIR / RULES_TEMPLATE).read_text(encoding="utf-8").strip()
    return f"{RULES_TITLE}\n\n{body}\n"


def rules_identity() -> str:
    """Path-free identity of the pinned rules, for confirmation verdict caching.

    The ``rules.md`` template text when rules are on; ``""`` when off, so runs
    without rule pinning keep fingerprints computed before it existed.
    """
    if not enabled():
        return ""
    return (PROMPTS_DIR / RULES_TEMPLATE).read_text(encoding="utf-8")


def with_rules(prompt: str) -> str:
    """Prepend the rules block to ``prompt`` once; identity when rules are off.

    Idempotent: a prompt that already starts with the current block is returned
    unchanged, so layered launch paths never pin the rules twice.
    """
    block = rules_block()
    if not block:
        return prompt
    prefix = f"{block}{RULES_SEPARATOR}"
    if prompt.startswith(prefix):
        return prompt
    return prefix + prompt
