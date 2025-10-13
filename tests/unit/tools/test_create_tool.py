"""
Unit tests for CreateTool

Tests creating new files with safety checks.
"""

import pytest
from pathlib import Path

from src.tools.create_tool import CreateTool, create_file


class TestCreateTool:
    """Test cases for CreateTool"""

    def test_create_new_file(self, temp_dir):
        """Test creating a new file"""
        file_path = temp_dir / "new_file.txt"

        # Create the file
        tool = CreateTool()
        result = tool.run(
            file_path=str(file_path),
            content="New file content"
        )

        # Verify success
        assert result.success is True
        assert "successfully" in result.data.lower()

        # Verify file was created
        assert file_path.exists()
        assert file_path.read_text() == "New file content"

    def test_create_file_with_nested_directory(self, temp_dir):
        """Test that parent directories are created automatically"""
        file_path = temp_dir / "subdir1" / "subdir2" / "file.txt"

        tool = CreateTool()
        result = tool.run(
            file_path=str(file_path),
            content="content"
        )

        # Should succeed and create directories
        assert result.success is True
        assert file_path.exists()
        assert file_path.parent.exists()

    def test_create_existing_file_fails(self, temp_file):
        """Test that creating an existing file fails"""
        file_path = temp_file("existing content")

        tool = CreateTool()
        result = tool.run(
            file_path=file_path,
            content="new content"
        )

        # Should fail
        assert result.success is False
        assert "already exists" in result.error.lower()
        assert any("WriteTool" in s for s in result.suggestions)

        # Original content should be preserved
        assert Path(file_path).read_text() == "existing content"

    def test_convenience_function(self, temp_dir):
        """Test the convenience function"""
        file_path = temp_dir / "test.txt"

        # Use convenience function
        result = create_file(str(file_path), "content")

        # Verify
        assert result.success is True
        assert file_path.exists()
        assert file_path.read_text() == "content"

    def test_metadata_populated(self, temp_dir):
        """Test that metadata is populated correctly"""
        file_path = temp_dir / "test.txt"

        result = create_file(str(file_path), "Line 1\nLine 2\nLine 3")

        # Check metadata
        assert 'lines_written' in result.metadata
        assert 'bytes_written' in result.metadata
        assert 'file_path' in result.metadata
        assert 'parent_dir' in result.metadata
        assert result.metadata['lines_written'] == 3

    def test_tool_properties(self):
        """Test that tool has correct name and description"""
        tool = CreateTool()

        assert tool.name == "create"
        assert "NEW" in tool.description
        assert "WriteTool" in tool.description

    def test_create_empty_file(self, temp_dir):
        """Test creating an empty file"""
        file_path = temp_dir / "empty.txt"

        result = create_file(str(file_path), "")

        assert result.success is True
        assert file_path.exists()
        assert file_path.read_text() == ""
        assert result.metadata['lines_written'] == 0

    def test_create_spec_file(self, temp_dir):
        """Test creating a TLA+ spec file"""
        spec_content = """---- MODULE Test ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
===="""
        file_path = temp_dir / "Test.tla"

        result = create_file(str(file_path), spec_content)

        assert result.success is True
        assert file_path.exists()
        assert "MODULE Test" in file_path.read_text()


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
