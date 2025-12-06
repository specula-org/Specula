#!/usr/bin/env python3
"""
Minimal smoke test for ClaudeAgentSDKClient.

Usage (from repo root):
    export ANTHROPIC_API_KEY=...
    SPECULA_CONFIG_PATH=./config.yaml python tests/agent/test_claude_agent_sdk.py
"""

import sys
from pathlib import Path

# Ensure repository root is on sys.path
ROOT = Path(__file__).resolve().parent.parent.parent
sys.path.insert(0, str(ROOT))

from src.agent import ClaudeAgentSDKClient


def main() -> None:
    prompt = 'HI, please say "Hi!"'
    client = ClaudeAgentSDKClient()
    response = client.run(prompt)
    print("Model response:\n", response)


if __name__ == "__main__":
    main()
