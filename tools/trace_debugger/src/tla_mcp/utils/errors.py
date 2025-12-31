"""Custom exceptions for MCP server."""


class MCPError(Exception):
    """Base exception for MCP errors."""
    pass


class ValidationError(MCPError):
    """Argument validation error."""
    pass


class ExecutionError(MCPError):
    """Tool execution error."""

    def __init__(self, message: str, details: dict = None):
        super().__init__(message)
        self.details = details or {}
