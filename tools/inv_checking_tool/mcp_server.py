#!/usr/bin/env python3
"""TLC Output Reader MCP Server - Entry point.

This script starts the MCP server that exposes TLC output analysis
capabilities to AI agents via the Model Context Protocol.

Usage:
    python mcp_server.py

    or add to your MCP client config:
    {
      "mcpServers": {
        "tlc-output-reader": {
          "command": "python",
          "args": ["/path/to/tools/inv_checking_tool/mcp_server.py"],
          "env": {}
        }
      }
    }

Available tools:
    1. get_tlc_summary - Get overview of TLC model checking results
    2. get_tlc_state - Get specific states and variable values
    3. compare_tlc_states - Compare states and track variable changes
"""

import asyncio
import sys
import os

# Add package to path
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from src.mcp import TLCOutputReaderMCPServer


async def main():
    """Main entry point."""
    server = TLCOutputReaderMCPServer()

    try:
        await server.run()
    except KeyboardInterrupt:
        print("Server stopped by user", file=sys.stderr)
    except Exception as e:
        print(f"Server error: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    asyncio.run(main())
