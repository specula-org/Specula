"""Logging utilities for MCP server."""

import logging
import sys

# Configure logger
logging.basicConfig(
    level=logging.INFO,
    format='[%(asctime)s] [%(levelname)s] %(message)s',
    handlers=[
        logging.StreamHandler(sys.stderr)
    ]
)

logger = logging.getLogger("tla-debugger-mcp")
