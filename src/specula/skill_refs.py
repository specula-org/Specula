"""Stable Specula skill identifiers used in agent prompts."""

from __future__ import annotations

import functools
import json
import os
import re
import secrets
import shutil
import subprocess
import sys
from pathlib import Path

CODEX_PLUGIN_NAME = "specula-codex"
_SKILL_NAME = re.compile(r"[a-z0-9]+(?:-[a-z0-9]+)*")
_SKILL_REF_PREFIX = f"<!-- specula-skill:{secrets.token_hex(16)}:"
_SKILL_REF = re.compile(rf"{re.escape(_SKILL_REF_PREFIX)}([a-z0-9]+(?:-[a-z0-9]+)*) -->")


def prompt_skill_ids(name: str) -> str:
    """Return a portable skill reference for adapter-boundary materialization."""
    if _SKILL_NAME.fullmatch(name) is None:
        raise ValueError(f"invalid skill name: {name!r}")
    return f"**{name}**{_SKILL_REF_PREFIX}{name} -->"


def _warn_codex_plugin_probe(action: str) -> None:
    print(
        f"WARNING: could not {action} enabled Codex plugins; using standalone Specula skill IDs.",
        file=sys.stderr,
    )


@functools.lru_cache(maxsize=8)
def _probe_codex_plugin(executable: str, home: str, codex_home: str, cwd: str) -> bool:
    """Probe one Codex installation/config tuple for the Specula plugin."""
    env = os.environ.copy()
    if home:
        env["HOME"] = home
    else:
        env.pop("HOME", None)
    if codex_home:
        env["CODEX_HOME"] = codex_home
    else:
        env.pop("CODEX_HOME", None)
    try:
        result = subprocess.run(
            [executable, "plugin", "list", "--json"],
            capture_output=True,
            text=True,
            timeout=5,
            check=False,
            env=env,
            cwd=cwd,
        )
    except (OSError, subprocess.TimeoutExpired):
        _warn_codex_plugin_probe("query")
        return False

    if result.returncode != 0:
        _warn_codex_plugin_probe("query")
        return False
    try:
        payload = json.loads(result.stdout)
    except json.JSONDecodeError:
        _warn_codex_plugin_probe("parse")
        return False

    if not isinstance(payload, dict):
        _warn_codex_plugin_probe("parse")
        return False
    installed = payload.get("installed", [])
    if not isinstance(installed, list):
        _warn_codex_plugin_probe("parse")
        return False
    return any(
        isinstance(plugin, dict)
        and plugin.get("name") == CODEX_PLUGIN_NAME
        and plugin.get("installed", True) is True
        and plugin.get("enabled", True) is True
        for plugin in installed
    )


def _codex_plugin_enabled() -> bool:
    """Whether the active Codex executable/config exposes Specula as a plugin."""
    executable = shutil.which("codex") or "codex"
    return _probe_codex_plugin(
        executable,
        os.environ.get("HOME", ""),
        os.environ.get("CODEX_HOME", ""),
        os.getcwd(),
    )


def materialize_skill_refs(
    prompt: str,
    adapter: str | Path,
    *,
    codex_plugin_enabled: bool | None = None,
) -> str:
    """Resolve portable references to the single ID understood by an adapter."""
    if _SKILL_REF_PREFIX not in prompt:
        return prompt

    if Path(adapter).stem == "codex":
        plugin_enabled = _codex_plugin_enabled() if codex_plugin_enabled is None else codex_plugin_enabled
        prefix = f"{CODEX_PLUGIN_NAME}:" if plugin_enabled else ""
        resolved = _SKILL_REF.sub(lambda match: f" (${prefix}{match.group(1)})", prompt)
    else:
        resolved = _SKILL_REF.sub("", prompt)

    if _SKILL_REF_PREFIX in resolved:
        raise ValueError("unresolved Specula skill reference")
    return resolved
