"""
Write Tool - Write content to existing files

Only modifies existing files for safety.
Use CreateTool to create new files.
"""

from pathlib import Path
from .base import BaseTool
from ..utils.result_types import ToolResult


class WriteTool(BaseTool):
    """
    Write content to an EXISTING file

    Safety features:
    - Only writes to files that already exist
    - Prevents accidental file creation from typos
    - Suggests using ReadTool first to verify path

    Example:
        tool = WriteTool()

        # First, read to verify path
        read_result = read_tool.run(file_path="spec.tla")

        # Then write
        result = tool.run(
            file_path="spec.tla",
            content="new content"
        )
    """

    @property
    def name(self) -> str:
        return "write"

    @property
    def description(self) -> str:
        return """Write content to an EXISTING file.

IMPORTANT: Cannot create new files - file must already exist.
Use CreateTool to create new files.

Safety: Will fail if file doesn't exist to prevent path errors."""

    def run(self, file_path: str, content: str) -> ToolResult:
        """
        Write content to an existing file

        Args:
            file_path: Path to the file (must exist)
            content: Content to write

        Returns:
            ToolResult with success status and metadata
        """
        path = Path(file_path)

        # Check if file exists
        if not path.exists():
            return ToolResult(
                success=False,
                error=f"File not found: {file_path}",
                suggestions=[
                    "File must exist to use WriteTool",
                    "Use ReadTool first to verify the path is correct",
                    "Use CreateTool if you want to create a new file"
                ]
            )

        # Check if it's a file (not a directory)
        if not path.is_file():
            return ToolResult(
                success=False,
                error=f"Path is not a file: {file_path}",
                suggestions=[
                    "Ensure the path points to a file, not a directory"
                ]
            )

        # Get old size for comparison
        old_size = path.stat().st_size
        old_lines = len(path.read_text(encoding='utf-8').splitlines())

        # Try to write
        try:
            path.write_text(content, encoding='utf-8')
        except PermissionError:
            return ToolResult(
                success=False,
                error=f"Permission denied: {file_path}",
                suggestions=[
                    "Check file permissions",
                    "Ensure you have write access to this file"
                ]
            )
        except Exception as e:
            return ToolResult(
                success=False,
                error=f"Unexpected error writing file: {str(e)}",
                suggestions=[
                    "Check the error message for details"
                ]
            )

        # Success - calculate statistics
        new_size = path.stat().st_size
        new_lines = len(content.splitlines())

        return ToolResult(
            success=True,
            data=f"File written successfully: {file_path}",
            suggestions=[
                f"Written {new_lines} lines ({new_size} bytes)",
                f"Previous: {old_lines} lines ({old_size} bytes)"
            ],
            metadata={
                "file_path": str(path.absolute()),
                "bytes_written": new_size,
                "lines_written": new_lines,
                "old_bytes": old_size,
                "old_lines": old_lines
            }
        )


# Convenience function
def write_file(file_path: str, content: str) -> ToolResult:
    """
    Convenience function to write to a file

    Args:
        file_path: Path to the file (must exist)
        content: Content to write

    Returns:
        ToolResult with success status
    """
    tool = WriteTool()
    return tool.run(file_path=file_path, content=content)
