#!/usr/bin/env python3
"""Expose the CI context request without taking ownership of the native session."""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from mcp.server.fastmcp import FastMCP

from specula.context_control import TOOL_DESCRIPTION, request_compaction

server = FastMCP("specula_context")


@server.tool(description=TOOL_DESCRIPTION)
def request_context_compaction(handoff_path: str) -> dict[str, str]:
    return request_compaction(handoff_path)


if __name__ == "__main__":
    server.run()
