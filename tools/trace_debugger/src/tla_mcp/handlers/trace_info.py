"""Handler for get_trace_info tool."""

from typing import Dict, Any

from .base import BaseHandler


class TraceInfoHandler(BaseHandler):
    """Handler for get_trace_info tool.

    This is a stub implementation for Phase 1 testing.
    Full implementation will be done in Phase 2.
    """

    @property
    def tool_name(self) -> str:
        return "get_trace_info"

    @property
    def argument_schema(self) -> Dict[str, Any]:
        return {
            "type": "object",
            "properties": {
                "trace_file": {"type": "string"}
            },
            "required": ["trace_file"]
        }

    async def execute(self, arguments: Dict[str, Any]) -> Dict[str, Any]:
        """Get trace info (stub implementation).

        Args:
            arguments: Validated arguments

        Returns:
            Stub result
        """
        # Phase 1: Return stub result
        return {
            "message": "Stub implementation - Phase 2 will implement full functionality",
            "trace_file": arguments["trace_file"]
        }
