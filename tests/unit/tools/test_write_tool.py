"""
Unit tests for WriteTool

Tests writing to existing files with safety checks.
"""

import pytest
from pathlib import Path

from src.tools.write_tool import WriteTool, write_file


class TestWriteTool:
    """Test cases for WriteTool"""

    def test_write_to_existing_file(self, temp_file):
        """Test writing to an existing file"""
        # Create a file with initial content
        file_path = temp_file("Initial content")

        # Write new content
        tool = WriteTool()
        result = tool.run(
            file_path=file_path,
            content="New content"
        )

        # Verify success
        assert result.success is True
        assert "successfully" in result.data.lower()

        # Verify file was actually updated
        new_content = Path(file_path).read_text()
        assert new_content == "New content"

    def test_write_to_nonexistent_file(self):
        """Test that writing to non-existent file fails"""
        tool = WriteTool()
        result = tool.run(
            file_path="/tmp/nonexistent_file_12345.txt",
            content="content"
        )

        # Should fail
        assert result.success is False
        assert "not found" in result.error.lower()
        assert len(result.suggestions) > 0
        assert any("CreateTool" in s for s in result.suggestions)

    def test_write_to_directory(self, temp_dir):
        """Test that writing to a directory fails"""
        tool = WriteTool()
        result = tool.run(
            file_path=str(temp_dir),
            content="content"
        )

        # Should fail
        assert result.success is False
        assert "not a file" in result.error.lower()

    def test_convenience_function(self, temp_file):
        """Test the convenience function"""
        file_path = temp_file("old content")

        # Use convenience function
        result = write_file(file_path, "new content")

        # Verify
        assert result.success is True
        assert Path(file_path).read_text() == "new content"

    def test_metadata_populated(self, temp_file):
        """Test that metadata includes old and new statistics"""
        file_path = temp_file("Line 1\nLine 2")

        result = write_file(file_path, "Line 1\nLine 2\nLine 3")

        # Check metadata
        assert 'lines_written' in result.metadata
        assert 'bytes_written' in result.metadata
        assert 'old_lines' in result.metadata
        assert 'old_bytes' in result.metadata
        assert result.metadata['lines_written'] == 3
        assert result.metadata['old_lines'] == 2

    def test_tool_properties(self):
        """Test that tool has correct name and description"""
        tool = WriteTool()

        assert tool.name == "write"
        assert "EXISTING" in tool.description
        assert "CreateTool" in tool.description

    def test_overwrite_preserves_nothing(self, temp_file):
        """Test that write completely replaces content"""
        file_path = temp_file("Old content\nMultiple lines\nHere")

        result = write_file(file_path, "Just one line")

        assert result.success is True
        assert Path(file_path).read_text() == "Just one line"

    def test_write_empty_content(self, temp_file):
        """Test writing empty content"""
        file_path = temp_file("Some content")

        result = write_file(file_path, "")

        assert result.success is True
        assert Path(file_path).read_text() == ""
        assert result.metadata['lines_written'] == 0


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
