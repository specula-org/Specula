"""Logging utilities for MCP server.

This module provides centralized logging configuration, ensuring that:
1. Logs are persisted to files with rotation.
2. No logs leak to stdout (which corrupts MCP protocol).
3. Logs are formatted consistently with timestamps and context.
"""

import logging
import logging.handlers
import sys
import os

# Default log directory
DEFAULT_LOG_DIR = os.path.join(os.path.expanduser("~"), ".specula", "logs", "spec_analyzer")


def setup_logging(
    name: str = "spec-analyzer-mcp",
    log_dir: str = DEFAULT_LOG_DIR,
    level: int = logging.INFO
) -> logging.Logger:
    """Configure and return the root logger.

    Args:
        name: Logger name.
        log_dir: Directory to store log files.
        level: Logging level.

    Returns:
        Configured logger instance.
    """
    # Create log directory
    os.makedirs(log_dir, exist_ok=True)
    log_file = os.path.join(log_dir, "mcp_server.log")

    # Get root logger
    root_logger = logging.getLogger()
    root_logger.setLevel(level)

    # Remove existing handlers to avoid duplication
    if root_logger.hasHandlers():
        root_logger.handlers.clear()

    # Formatter
    formatter = logging.Formatter(
        '[%(asctime)s] [%(levelname)s] [%(name)s] [%(threadName)s] %(message)s'
    )

    # 1. Rotating File Handler
    # Max size 10MB, keep 5 backups
    file_handler = logging.handlers.RotatingFileHandler(
        log_file, maxBytes=10*1024*1024, backupCount=5, encoding='utf-8'
    )
    file_handler.setFormatter(formatter)
    file_handler.setLevel(level)
    root_logger.addHandler(file_handler)

    # 2. Stderr Handler
    # Strictly use stderr to avoid polluting stdout (MCP channel)
    stderr_handler = logging.StreamHandler(sys.stderr)
    stderr_handler.setFormatter(formatter)
    stderr_handler.setLevel(level)
    root_logger.addHandler(stderr_handler)

    # Log startup info
    log = logging.getLogger(name)
    log.info(f"Logging initialized. Writing to {log_file}")
    log.info(f"Log level: {logging.getLevelName(level)}")

    return log


# Initialize a default logger instance for modules that import 'logger' directly
logger = logging.getLogger("spec-analyzer-mcp")
