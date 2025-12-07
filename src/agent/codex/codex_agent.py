"""
Minimal Codex CLI adapter.

This is a lightweight scaffold to invoke the Codex CLI with two permission
profiles:
    - sandbox: default Codex sandbox (workspace-write, restricted network)
    - full_access: dangerous mode with full filesystem + network + no approvals

`run` shells out to the Codex binary via the non-interactive `exec` command for
single-turn calls. Multi-turn support can be added later using the interactive
mode; see the TODO in CodexClient.
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

    TODO: add multi-turn/interactive mode support (e.g., using the interactive
    Codex session or `resume`) when needed; current implementation is single-turn.
    """

    def __init__(self, config: Optional[CodexConfig] = None) -> None:
        self.config = config or CodexConfig()

    def build_command(self, permission_mode: PermissionMode) -> List[str]:
        """Build the Codex CLI command for the requested permission mode."""
        cmd = [self.config.codex_binary]

        # Optional: supply a Codex config profile if provided.
        if self.config.profile:
            cmd.extend(["--profile", self.config.profile])

        if permission_mode == "full_access":
            # Request no sandbox and no approvals. Only use if you trust the environment.
            cmd.extend(["--danger-full-access", "--network-enabled", "--approval", "never"])
        elif permission_mode == "sandbox":
            # Default; rely on Codex's sandbox defaults (no extra flags needed).
            pass
        else:
            raise ValueError(f"Unknown permission_mode: {permission_mode}")

        return cmd

    def run(self, prompt: str, permission_mode: PermissionMode = "sandbox") -> subprocess.CompletedProcess[str]:
        """
        Invoke Codex with the given prompt and permission mode.

        Args:
            prompt: The task/question to pass to Codex (stdin).
            permission_mode: 'sandbox' or 'full_access'.
        Returns:
            subprocess.CompletedProcess with stdout/stderr/returncode populated.
        """
        cmd = self.build_command(permission_mode, prompt)
        return self._run(cmd)

    def format_command(self, permission_mode: PermissionMode, prompt: str = "<prompt>") -> str:
        """Return a shell-escaped string of the command for logging."""
        return " ".join(shlex.quote(part) for part in self.build_command(permission_mode, prompt))

    def build_command(self, permission_mode: PermissionMode, prompt: str) -> List[str]:
        """Build the Codex CLI command for the requested permission mode."""
        cmd = [self.config.codex_binary, "exec"]

        if permission_mode == "full_access":
            # Request no sandbox and no approvals. Only use if you trust the environment.
            cmd.extend(
                [
                    "--dangerously-bypass-approvals-and-sandbox",
                    # Alternatively: "--sandbox", "danger-full-access", "--ask-for-approval", "never",
                ]
            )
        elif permission_mode == "sandbox":
            # Default sandboxed execution. Adjust if you prefer explicit flags.
            # Example explicit flags:
            # cmd.extend(["--sandbox", "workspace-write", "--ask-for-approval", "on-request"])
            pass
        else:
            raise ValueError(f"Unknown permission_mode: {permission_mode}")

        cmd.append(prompt)
        return cmd

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
