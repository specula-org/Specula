"""Refuse to run with settings from before the Specula → Specular rename.

Specular no longer reads the ``SPECULA_*`` variables or the ``.specula/sandbox.json``
files that Specula used. Ignoring them silently would change behavior without
notice (for example, running without the requested sandbox, or with a default
sandbox policy instead of the user's tightened one), so entry points stop and
say what to rename. Only variable names Specula actually used are checked:
agent-written scripts may define other ``SPECULA_*`` variables of their own.
"""

from __future__ import annotations

import os
import shlex
import sys
from collections.abc import Mapping
from pathlib import Path

LEGACY_NAMES = frozenset(
    {
        "SPECULA_ACTIVITY_LOG",
        "SPECULA_AGENT",
        "SPECULA_BYOM_PATH",
        "SPECULA_CI_BORROW_LEASE",
        "SPECULA_CI_BRANCH",
        "SPECULA_CI_CONFIRMATION",
        "SPECULA_CI_DIR",
        "SPECULA_CI_ENVIRONMENT",
        "SPECULA_CI_EVENT_LOCK_FD",
        "SPECULA_CI_LOCK_FD",
        "SPECULA_CI_RECEIPT",
        "SPECULA_CLAUDE_ALIAS",
        "SPECULA_CONTEXT",
        "SPECULA_CONTEXT_AGENT",
        "SPECULA_CONTEXT_CODEX_CONFIG",
        "SPECULA_CONTEXT_MCP_CONFIG",
        "SPECULA_CONTEXT_MCP_JSON",
        "SPECULA_CONTEXT_PYTHON",
        "SPECULA_CONTEXT_REQUEST",
        "SPECULA_CONTEXT_TOKEN",
        "SPECULA_COPY_ARTIFACT",
        "SPECULA_DELEGATION",
        "SPECULA_EFFORT",
        "SPECULA_FRESH_CONTEXT",
        "SPECULA_INVOCATION_ID",
        "SPECULA_LITE_CACHE",
        "SPECULA_LITE_JAVA",
        "SPECULA_MANUAL_RESUME",
        "SPECULA_MODEL",
        "SPECULA_NOTES",
        "SPECULA_PHASE",
        "SPECULA_PIPELINE_LOG",
        "SPECULA_PROGRESS",
        "SPECULA_QUOTA_5H",
        "SPECULA_QUOTA_7D",
        "SPECULA_QUOTA_MAX_WAITS",
        "SPECULA_RATE_LIMIT_REACTIVE",
        "SPECULA_RATE_LIMIT_RETRIES",
        "SPECULA_RESOURCE_INVOCATION",
        "SPECULA_RESOURCE_PHASE",
        "SPECULA_RESOURCE_ROOT",
        "SPECULA_RESUME_EFFORT",
        "SPECULA_RESUME_MODEL",
        "SPECULA_RESUME_STATE",
        "SPECULA_ROOT",
        "SPECULA_RULES",
        "SPECULA_RUN_DIR",
        "SPECULA_RUN_LOCK_FD",
        "SPECULA_SANDBOX",
        "SPECULA_SANDBOX_BACKEND",
        "SPECULA_SANDBOX_CAPABILITY",
        "SPECULA_SANDBOX_CONFIG",
        "SPECULA_SANDBOX_EXTRA_WRITE",
        "SPECULA_SKILLS",
        "SPECULA_SOURCE_SNAPSHOT",
        "SPECULA_SRC",
        "SPECULA_STOP_GATE",
        "SPECULA_STOP_GATE_CAP",
        "SPECULA_STOP_GATE_WORK_DIR",
        "SPECULA_STRICT_OUTPUTS",
        "SPECULA_TARGET_REPO_DIR",
        "SPECULA_TLC_ADMISSION_STATUS",
        "SPECULA_TLC_AUTO_WORKERS",
        "SPECULA_TLC_MEMORY_LIMIT",
        "SPECULA_TLC_RESOURCE_DIR",
        "SPECULA_TLC_SCOPE",
        "SPECULA_TLC_TOOL",
        "SPECULA_TLC_TOOL_CODEX",
        "SPECULA_TLC_TOOL_CONFIG",
        "SPECULA_TLC_TOOL_EXTENSION",
        "SPECULA_TLC_TOOL_JSON",
        "SPECULA_TLC_TOOL_LIFELINE_FD",
        "SPECULA_TLC_TOOL_OWNER",
        "SPECULA_TLC_TOOL_PARENT",
        "SPECULA_TLC_TOOL_PARENT_LOCK",
        "SPECULA_TLC_TOOL_PYTHON",
        "SPECULA_TLC_TOOL_STOP_FILE",
        "SPECULA_TLC_TOOL_WORKER_LOCK",
        "SPECULA_TLC_WORKER_LIMIT",
        "SPECULA_WORK_DIR",
    }
)


def legacy_variables(environ: Mapping[str, str] | None = None) -> list[str]:
    env = os.environ if environ is None else environ
    return sorted(name for name in env if name in LEGACY_NAMES)


def legacy_message(names: list[str]) -> str:
    lines = ["Specula has been renamed to Specular. Rename these environment variables, then rerun:"]
    lines += [f"  {name} -> SPECULAR_{name.removeprefix('SPECULA_')}" for name in names]
    lines.append('See "Switching from Specula" in docs/Usage.md.')
    return "\n".join(lines) + "\n"


def legacy_sandbox_configs(
    environ: Mapping[str, str] | None = None, cwd: Path | None = None, home: Path | None = None
) -> list[Path]:
    """Pre-rename sandbox configs that a sandboxed run would now silently skip."""
    env = os.environ if environ is None else environ
    if env.get("SPECULAR_SANDBOX", "").lower() != "on" or env.get("SPECULAR_SANDBOX_CONFIG"):
        return []
    # Follow the resolution order (launch directory, then home): the first
    # config found wins, so a legacy file behind a current one is never read.
    for base in dict.fromkeys((Path.cwd() if cwd is None else cwd, Path.home() if home is None else home)):
        if (base / ".specular" / "sandbox.json").exists():
            return []
        if (base / ".specula" / "sandbox.json").is_file():
            return [base / ".specula" / "sandbox.json"]
    return []


def legacy_sandbox_message(configs: list[Path]) -> str:
    lines = ["Specula has been renamed to Specular. Move your sandbox configuration, then rerun:"]
    for config in configs:
        target = config.parent.with_name(".specular")
        lines.append(
            f"  mkdir -p {shlex.quote(str(target))} && mv {shlex.quote(str(config))} {shlex.quote(str(target))}/"
        )
    lines.append('See "Switching from Specula" in docs/Usage.md.')
    return "\n".join(lines) + "\n"


def exit_on_legacy_settings(environ: Mapping[str, str] | None = None) -> None:
    names = legacy_variables(environ)
    if names:
        sys.stderr.write(legacy_message(names))
        raise SystemExit(1)
    configs = legacy_sandbox_configs(environ)
    if configs:
        sys.stderr.write(legacy_sandbox_message(configs))
        raise SystemExit(1)
