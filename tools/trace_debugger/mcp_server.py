#!/usr/bin/env python3
"""TLA+ Trace Debugger MCP Server - Entry point.

This script starts the MCP server that exposes TLA+ trace debugging
capabilities to AI agents via the Model Context Protocol.

Usage:
    python mcp_server.py [--log-level LEVEL]

    or add to your MCP client config:
    {
      "mcpServers": {
        "tla-debugger": {
          "command": "python",
          "args": ["/path/to/mcp_server.py"],
          "env": {}
        }
      }
    }
"""

import asyncio
import argparse
import sys
import os

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'src'))

from tla_mcp import TLADebuggerMCPServer
from tla_mcp.utils.logger import logger


def parse_args():
    """Parse command line arguments."""
    parser = argparse.ArgumentParser(
        description="TLA+ Trace Debugger MCP Server",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Start server with INFO logging
  python mcp_server.py

  # Start server with DEBUG logging
  python mcp_server.py --log-level DEBUG

  # Use in MCP client config (Claude Desktop, Cline, etc.)
  {
    "mcpServers": {
      "tla-debugger": {
        "command": "python",
        "args": ["/absolute/path/to/mcp_server.py"]
      }
    }
  }
        """
    )
    parser.add_argument(
        "--log-level",
        choices=["DEBUG", "INFO", "WARNING", "ERROR"],
        default="INFO",
        help="Logging level (default: INFO)"
    )
    return parser.parse_args()


async def main():
    """Main entry point."""
    args = parse_args()

    # Configure logging
    logger.setLevel(args.log_level)

    # Create and run server
    logger.info("=" * 60)
    logger.info("TLA+ Trace Debugger MCP Server")
    logger.info("=" * 60)
    logger.info(f"Log level: {args.log_level}")
    logger.info(f"Working directory: {os.getcwd()}")
    logger.info(f"Python: {sys.version}")
    logger.info("=" * 60)

    server = TLADebuggerMCPServer()

    try:
        await server.run()
    except KeyboardInterrupt:
        logger.info("Server stopped by user")
    except Exception as e:
        logger.error(f"Server error: {e}", exc_info=True)
        sys.exit(1)


if __name__ == "__main__":
    asyncio.run(main())
