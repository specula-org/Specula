"""
Create Tool - Create new files

Only creates new files for safety.
Use WriteTool to modify existing files.
"""

from pathlib import Path
from .base import BaseTool
from ..utils.result_types import ToolResult


class CreateTool(BaseTool):
    """
    Create a NEW file with content

    Safety features:
    - Only creates files that don't exist
    - Prevents accidental overwrites
    - Automatically creates parent directories

    Example:
        tool = CreateTool()
        result = tool.run(
            file_path="src/tools/new_tool.py",
            content="# New tool implementation"
        )
    """

    @property
    def name(self) -> str:
        return "create"

    @property
    def description(self) -> str:
        return """Create a NEW file with content.

IMPORTANT: Only for creating NEW files - will fail if file exists.
Use WriteTool to modify existing files.

Safety: Will fail if file already exists to prevent accidental overwrites."""

    def run(self, file_path: str, content: str) -> ToolResult:
        """
        Create a new file with content

        Args:
            file_path: Path to the new file (must not exist)
            content: Content to write

        Returns:
            ToolResult with success status and metadata
        """
        path = Path(file_path)

        # Check if file already exists
        if path.exists():
            return ToolResult(
                success=False,
                error=f"File already exists: {file_path}",
                suggestions=[
                    "File already exists - cannot create",
                    "Use WriteTool to modify existing files",
                    "Use ReadTool to view current content"
                ]
            )

        # Create parent directories if needed
        try:
            path.parent.mkdir(parents=True, exist_ok=True)
        except PermissionError:
            return ToolResult(
                success=False,
                error=f"Permission denied creating directory: {path.parent}",
                suggestions=[
                    "Check directory permissions",
                    "Ensure you have write access to the parent directory"
                ]
            )
        except Exception as e:
            return ToolResult(
                success=False,
                error=f"Error creating directory: {str(e)}",
                suggestions=[
                    "Check the error message for details"
                ]
            )

        # Try to create and write the file
        try:
            path.write_text(content, encoding='utf-8')
        except PermissionError:
            return ToolResult(
                success=False,
                error=f"Permission denied: {file_path}",
                suggestions=[
                    "Check directory permissions",
                    "Ensure you have write access to this location"
                ]
            )
        except Exception as e:
            return ToolResult(
                success=False,
                error=f"Unexpected error creating file: {str(e)}",
                suggestions=[
                    "Check the error message for details"
                ]
            )

        # Success - calculate statistics
        file_size = path.stat().st_size
        num_lines = len(content.splitlines())

        return ToolResult(
            success=True,
            data=f"File created successfully: {file_path}",
            suggestions=[
                f"Created with {num_lines} lines ({file_size} bytes)"
            ],
            metadata={
                "file_path": str(path.absolute()),
                "bytes_written": file_size,
                "lines_written": num_lines,
                "parent_dir": str(path.parent.absolute())
            }
        )


# Convenience function
def create_file(file_path: str, content: str) -> ToolResult:
    """
    Convenience function to create a file

    Args:
        file_path: Path to the new file (must not exist)
        content: Content to write

    Returns:
        ToolResult with success status
    """
    tool = CreateTool()
    return tool.run(file_path=file_path, content=content)
