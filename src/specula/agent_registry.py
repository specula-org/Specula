"""Canonical metadata for agent adapters known to the orchestrator."""

from __future__ import annotations

from dataclasses import dataclass
from types import MappingProxyType
from typing import Final


@dataclass(frozen=True)
class AgentSpec:
    model_env: str | None = None
    effort_env: str | None = None
    default_effort: str | None = None


AGENT_SPECS: Final = MappingProxyType(
    {
        "claude-code": AgentSpec(
            model_env="CLAUDE_MODEL",
            effort_env="CLAUDE_EFFORT",
            default_effort="max",
        ),
        "codex": AgentSpec(model_env="CODEX_MODEL", effort_env="CODEX_EFFORT"),
        "copilot-cli": AgentSpec(model_env="COPILOT_MODEL"),
        "opencode": AgentSpec(model_env="OPENCODE_MODEL", effort_env="OPENCODE_EFFORT"),
        "pi": AgentSpec(model_env="PI_MODEL", effort_env="PI_EFFORT"),
    }
)


def agent_spec(name: str) -> AgentSpec | None:
    return AGENT_SPECS.get(name)
