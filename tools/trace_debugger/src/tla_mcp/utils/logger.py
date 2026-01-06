"""Logging utilities for MCP server."""

import logging
import sys
import os

# Create log directory if needed
log_dir = "/tmp/tla_debugger_mcp_logs"
os.makedirs(log_dir, exist_ok=True)
log_file = os.path.join(log_dir, "mcp_server.log")

# Configure logger with both file and stderr
# Force immediate flush to see logs in real-time
file_handler = logging.FileHandler(log_file, mode='a')
file_handler.setLevel(logging.INFO)

stderr_handler = logging.StreamHandler(sys.stderr)
stderr_handler.setLevel(logging.INFO)

logging.basicConfig(
    level=logging.INFO,
    format='[%(asctime)s] [%(levelname)s] %(message)s',
    handlers=[stderr_handler, file_handler],
    force=True
)

# Force flush after every log
for handler in logging.root.handlers:
    handler.flush()

logger = logging.getLogger("tla-debugger-mcp")
logger.info(f"Logging to {log_file}")
