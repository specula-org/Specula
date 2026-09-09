#!/usr/bin/env python3
"""TLC startup and blocking waits for Specula Agent clients."""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from mcp.server.fastmcp import FastMCP

from specula.tlc_tasks import START_DESCRIPTION, WAIT_DESCRIPTION, start_tlc, wait_tlc

server = FastMCP("specula_tlc")
server.tool(description=START_DESCRIPTION)(start_tlc)
server.tool(description=WAIT_DESCRIPTION)(wait_tlc)

if __name__ == "__main__":
    server.run()
