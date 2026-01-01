"""Handler for get_trace_info tool."""

import os
from typing import Dict, Any

from .base import BaseHandler
from ..utils.errors import ExecutionError


class TraceInfoHandler(BaseHandler):
    """Handler for get_trace_info tool.

    This tool reads basic information about a trace file without
    running TLC. Useful for quickly checking trace size and content.
    """

    @property
    def tool_name(self) -> str:
        return "get_trace_info"

    @property
    def argument_schema(self) -> Dict[str, Any]:
        return {
            "type": "object",
            "properties": {
                "trace_file": {
                    "type": "string",
                    "description": "Path to trace file (absolute or relative)"
                }
            },
            "required": ["trace_file"]
        }

    async def execute(self, arguments: Dict[str, Any]) -> Dict[str, Any]:
        """Get trace file information.

        Args:
            arguments: Validated arguments with trace_file

        Returns:
            Dict with trace file information:
            - line_count: Number of lines in trace
            - file_size_bytes: File size in bytes
            - first_lines: First 5 lines
            - last_lines: Last 5 lines

        Raises:
            ExecutionError: If file doesn't exist or can't be read
        """
        trace_file = arguments["trace_file"]

        # Check if file exists
        if not os.path.exists(trace_file):
            raise ExecutionError(
                f"Trace file not found: {trace_file}",
                details={"trace_file": trace_file, "exists": False}
            )

        # Check if it's a file (not directory)
        if not os.path.isfile(trace_file):
            raise ExecutionError(
                f"Path is not a file: {trace_file}",
                details={"trace_file": trace_file, "is_file": False}
            )

        try:
            # Read file
            with open(trace_file, 'r', encoding='utf-8') as f:
                lines = f.readlines()

            # Get file size
            file_size = os.path.getsize(trace_file)

            # Prepare sample lines
            num_lines = len(lines)
            first_lines = [line.strip() for line in lines[:5]]
            last_lines = [line.strip() for line in lines[-5:]] if num_lines > 5 else []

            return {
                "line_count": num_lines,
                "file_size_bytes": file_size,
                "first_lines": first_lines,
                "last_lines": last_lines,
                "trace_file": trace_file
            }

        except UnicodeDecodeError as e:
            raise ExecutionError(
                f"Failed to read trace file (encoding error): {e}",
                details={"trace_file": trace_file, "error": str(e)}
            )
        except IOError as e:
            raise ExecutionError(
                f"Failed to read trace file: {e}",
                details={"trace_file": trace_file, "error": str(e)}
            )
