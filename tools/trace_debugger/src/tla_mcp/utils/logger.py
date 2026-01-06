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
from pathlib import Path

# Default log directory
DEFAULT_LOG_DIR = os.path.join(os.path.expanduser("~"), ".specula", "logs", "trace_debugger")

def setup_logging(
    name: str = "tla-debugger-mcp",
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
    logger = logging.getLogger(name)
    logger.info(f"Logging initialized. Writing to {log_file}")
    logger.info(f"Log level: {logging.getLevelName(level)}")
    
    return logger

class StdoutGuard:
    """Context manager to guard against accidental stdout writes."""
    
    class DevNull:
        def write(self, msg): pass
        def flush(self): pass

    def __enter__(self):
        self.original_stdout = sys.stdout
        # We can't actually replace stdout if we want the MCP server to work, 
        # because the MCP server WRITES to stdout.
        # So this guard is tricky. 
        # Instead of replacing it globally, we rely on the fact that 
        # the MCP library writes to the original stdout.
        # If we redirect sys.stdout to stderr, then 'print()' calls will go to stderr,
        # which is safe.
        # BUT we must ensure the MCP writer still has access to the real stdout.
        # Since we are using the 'mcp' library, we need to check how it writes.
        
        # Strategy: Redirect sys.stdout to sys.stderr so that 'print()' is safe.
        # We assume the MCP server explicitly uses the transport's output stream,
        # or we might break it if it relies on sys.stdout directly.
        
        # Let's check mcp_server.py first before implementing this aggressively.
        pass

    def __exit__(self, exc_type, exc_val, exc_tb):
        pass

# Initialize a default logger instance for modules that import 'logger' directly
# This ensures they have something to use even if setup_logging isn't called yet
logger = logging.getLogger("tla-debugger-mcp")