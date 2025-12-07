"""
Minimal Codex CLI adapter.

Supports two permission profiles:
    - sandbox: Codex default sandbox (workspace-write, restricted network)
    - full_access: no sandbox, no approvals (dangerous; only in trusted envs)

Uses `codex exec` for single-turn calls. A multi-turn placeholder can be added
later when the interactive flow is needed.
"""

from dataclasses import dataclass
from typing import Dict, List, Literal, Optional
import shlex
import subprocess

PermissionMode = Literal["sandbox", "full_access"]


@dataclass
class CodexConfig:
    """Configuration for running the Codex CLI."""

    codex_binary: str = "codex"
    workdir: Optional[str] = None
    env: Optional[Dict[str, str]] = None


class CodexClient:
    """
    Small helper to run Codex with selectable permission mode.

    TODO: add multi-turn/interactive mode support when needed; current
    implementation is single-turn via `codex exec`.
    """

    def __init__(self, config: Optional[CodexConfig] = None) -> None:
        self.config = config or CodexConfig()

    def build_command(self, permission_mode: PermissionMode, prompt: str) -> List[str]:
        """Build the Codex CLI command for the requested permission mode."""
        cmd = [self.config.codex_binary, "exec"]

        if permission_mode == "full_access":
            # Request no sandbox and no approvals. Only use if you trust the environment.
            cmd.extend(["--dangerously-bypass-approvals-and-sandbox"])
        elif permission_mode == "sandbox":
            # Default sandboxed execution (no extra flags required).
            pass
        else:
            raise ValueError(f"Unknown permission_mode: {permission_mode}")

        cmd.append(prompt)
        return cmd

    def run(self, prompt: str, permission_mode: PermissionMode = "sandbox") -> subprocess.CompletedProcess[str]:
        """
        Invoke Codex with the given prompt and permission mode.

        Args:
            prompt: The task/question to pass to Codex.
            permission_mode: 'sandbox' or 'full_access'.
        Returns:
            subprocess.CompletedProcess with stdout/stderr/returncode populated.
        """
        cmd = self.build_command(permission_mode, prompt)
        return self._run(cmd)

    def format_command(self, permission_mode: PermissionMode, prompt: str = "<prompt>") -> str:
        """Return a shell-escaped string of the command for logging."""
        return " ".join(shlex.quote(part) for part in self.build_command(permission_mode, prompt))

    def _run(self, cmd: List[str]) -> subprocess.CompletedProcess[str]:
        """Run Codex non-interactively and capture output."""
        proc = subprocess.run(
            cmd,
            text=True,
            capture_output=True,
            cwd=self.config.workdir,
            env=self.config.env,
            check=False,
        )
        return proc
