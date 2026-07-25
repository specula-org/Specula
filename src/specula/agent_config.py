"""Strict loading and phase routing for agent configuration files."""

from __future__ import annotations

import json
from collections.abc import Mapping
from dataclasses import dataclass
from pathlib import Path
from types import MappingProxyType
from typing import cast

PHASES = frozenset(
    {
        "analyze",
        "specgen",
        "harness",
        "validate",
        "confirm",
        "repair",
        "classify",
        "review",
    }
)
_TOP_LEVEL_FIELDS = frozenset({"version", "default_profile", "profiles", "phases"})
_PROFILE_FIELDS = frozenset({"agent", "model", "effort"})


class AgentConfigError(Exception):
    """An agent configuration file is unreadable or invalid."""


@dataclass(frozen=True)
class AgentSelection:
    agent: str
    model: str | None = None
    effort: str | None = None


@dataclass(frozen=True)
class AgentRouting:
    default: AgentSelection
    profiles: Mapping[str, AgentSelection]
    phases: Mapping[str, str]

    def resolve(self, phase: str, fallback: str | None = None) -> AgentSelection:
        """Resolve an explicit phase, then a fallback phase, then the default."""
        profile = self.phases.get(phase)
        if profile is None and fallback is not None:
            profile = self.phases.get(fallback)
        if profile is None:
            return self.default
        return self.profiles[profile]


def _as_object(value: object, location: str) -> dict[str, object]:
    if not isinstance(value, dict):
        raise AgentConfigError(f"{location} must be a JSON object")
    return cast(dict[str, object], value)


def _reject_unknown_fields(
    value: Mapping[str, object],
    allowed: frozenset[str],
    location: str,
) -> None:
    unknown = sorted(value.keys() - allowed)
    if unknown:
        raise AgentConfigError(f"{location} contains unknown field '{unknown[0]}'")


def _optional_string(profile: Mapping[str, object], field: str, profile_name: str) -> str | None:
    if field not in profile:
        return None
    value = profile[field]
    if not isinstance(value, str):
        raise AgentConfigError(f"profile '{profile_name}' field '{field}' must be a string")
    return value


def load_agent_routing(path: Path) -> AgentRouting:
    """Read and strictly validate an agent routing JSON file."""
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as exc:
        raise AgentConfigError(f"cannot read agent config {path}: {exc}") from exc
    try:
        loaded: object = json.loads(text)
    except json.JSONDecodeError as exc:
        raise AgentConfigError(
            f"invalid JSON in agent config {path} at line {exc.lineno}, column {exc.colno}: {exc.msg}"
        ) from exc

    document = _as_object(loaded, "agent config")
    _reject_unknown_fields(document, _TOP_LEVEL_FIELDS, "agent config")

    version = document.get("version")
    if not isinstance(version, int) or isinstance(version, bool) or version != 1:
        raise AgentConfigError("agent config field 'version' must be the integer 1")

    default_profile = document.get("default_profile")
    if not isinstance(default_profile, str):
        raise AgentConfigError("agent config field 'default_profile' must be a string")

    raw_profiles = _as_object(document.get("profiles"), "agent config field 'profiles'")
    profiles: dict[str, AgentSelection] = {}
    for name, raw_profile in raw_profiles.items():
        profile = _as_object(raw_profile, f"profile '{name}'")
        _reject_unknown_fields(profile, _PROFILE_FIELDS, f"profile '{name}'")
        agent = profile.get("agent")
        if not isinstance(agent, str) or not agent:
            raise AgentConfigError(f"profile '{name}' field 'agent' must be a non-empty string")
        profiles[name] = AgentSelection(
            agent=agent,
            model=_optional_string(profile, "model", name),
            effort=_optional_string(profile, "effort", name),
        )

    if default_profile not in profiles:
        raise AgentConfigError(f"default profile '{default_profile}' does not exist")

    raw_phases_value = document.get("phases", {})
    raw_phases = _as_object(raw_phases_value, "agent config field 'phases'")
    phases: dict[str, str] = {}
    for phase, raw_profile_name in raw_phases.items():
        if phase not in PHASES:
            raise AgentConfigError(f"agent config contains unknown phase '{phase}'")
        if not isinstance(raw_profile_name, str):
            raise AgentConfigError(f"phase '{phase}' must reference a profile by name")
        if raw_profile_name not in profiles:
            raise AgentConfigError(f"phase '{phase}' references unknown profile '{raw_profile_name}'")
        phases[phase] = raw_profile_name

    return AgentRouting(
        default=profiles[default_profile],
        profiles=MappingProxyType(profiles),
        phases=MappingProxyType(phases),
    )
