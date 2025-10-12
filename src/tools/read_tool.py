"""
Read Tool - Read file content

Simple tool to read any file and return its content.
"""

from pathlib import Path
from .base import BaseTool
from ..utils.result_types import ToolResult


class ReadTool(BaseTool):
    """
    Read a file and return its content

    Simple and general-purpose tool that can read any text file.
    Let the LLM understand and parse the content.

    Example:
        tool = ReadTool()
        result = tool.run(file_path="spec.tla")
        if result.success:
            print(result.data)  # file content
    """

    @property
    def name(self) -> str:
        return "read"

    @property
    def description(self) -> str:
        return "Read a file and return its content"

    def run(self, file_path: str) -> ToolResult:
        """
        Read a file

        Args:
            file_path: Path to the file to read

        Returns:
            ToolResult with file content or error
        """
        # Convert to Path object
        path = Path(file_path)

        # Check if file exists
        if not path.exists():
            return ToolResult(
                success=False,
                error=f"File not found: {file_path}",
                suggestions=[
                    "Check if the file path is correct",
                    "Use an absolute path if needed"
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

        # Try to read the file
        try:
            content = path.read_text(encoding='utf-8')
        except UnicodeDecodeError:
            return ToolResult(
                success=False,
                error=f"Cannot read file (not a text file): {file_path}",
                suggestions=[
                    "Ensure the file is a text file (not binary)"
                ]
            )
        except PermissionError:
            return ToolResult(
                success=False,
                error=f"Permission denied: {file_path}",
                suggestions=[
                    "Check file permissions"
                ]
            )
        except Exception as e:
            return ToolResult(
                success=False,
                error=f"Unexpected error reading file: {str(e)}",
                suggestions=[
                    "Check the error message for details"
                ]
            )

        # Success - return content
        num_lines = len(content.splitlines())
        num_chars = len(content)

        return ToolResult(
            success=True,
            data=content,
            suggestions=[
                f"File has {num_lines} lines and {num_chars} characters"
            ],
            metadata={
                "file_path": str(path.absolute()),
                "num_lines": num_lines,
                "num_chars": num_chars,
                "file_size_bytes": path.stat().st_size
            }
        )


# Convenience function for quick usage
def read_file(file_path: str) -> ToolResult:
    """
    Convenience function to read a file

    Args:
        file_path: Path to the file

    Returns:
        ToolResult with file content
    """
    tool = ReadTool()
    return tool.run(file_path=file_path)
