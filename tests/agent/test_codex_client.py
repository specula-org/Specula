#!/usr/bin/env python3
"""
Minimal smoke test for CodexClient (single-turn `codex exec`).

Usage (from repo root):
    CODEX_BIN=codex python tests/agent/test_codex_client.py
"""

import os
import shutil
import sys
from pathlib import Path

# Ensure repository root is on sys.path
ROOT = Path(__file__).resolve().parent.parent.parent
sys.path.insert(0, str(ROOT))

from src.agent.codex import CodexClient, CodexConfig


def main() -> None:
    prompt = 'HI, please say "Hi!"'
    codex_bin = os.getenv("CODEX_BIN", "codex")
    if shutil.which(codex_bin) is None:
        print(f"Codex binary '{codex_bin}' not found in PATH; skipping smoke test.")
        sys.exit(0)

    client = CodexClient(CodexConfig(codex_binary=codex_bin, workdir=str(ROOT)))
    result = client.run(prompt=prompt, permission_mode="sandbox")

    print("Command:", client.format_command("sandbox", prompt))
    print("Return code:", result.returncode)
    print("Stdout:\n", result.stdout)
    if result.stderr:
        print("Stderr:\n", result.stderr, file=sys.stderr)

    sys.exit(result.returncode)


if __name__ == "__main__":
    main()
