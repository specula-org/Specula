"""
Unit tests for ReadTool

Tests the basic functionality of reading files.
"""

import pytest
from pathlib import Path

from src.tools.read_tool import ReadTool, read_file


class TestReadTool:
    """Test cases for ReadTool"""

    def test_read_existing_file(self, temp_file):
        """Test reading an existing file"""
        # Use shared fixture to create temp file
        file_path = temp_file("Hello, Specula!\nThis is a test file.")

        # Read the file
        tool = ReadTool()
        result = tool.run(file_path=file_path)

        # Verify
        assert result.success is True
        assert "Hello, Specula!" in result.data
        assert result.error is None
        assert result.metadata['num_lines'] == 2

    def test_read_nonexistent_file(self):
        """Test reading a file that doesn't exist"""
        tool = ReadTool()
        result = tool.run(file_path="/nonexistent/file.txt")

        # Should fail with clear error
        assert result.success is False
        assert result.error is not None
        assert "not found" in result.error.lower()
        assert len(result.suggestions) > 0

    def test_read_directory(self, temp_dir):
        """Test reading a directory (should fail gracefully)"""
        tool = ReadTool()
        result = tool.run(file_path=str(temp_dir))

        # Should fail with clear message
        assert result.success is False
        assert "not a file" in result.error.lower()

    def test_convenience_function(self, temp_file):
        """Test the convenience function"""
        file_path = temp_file("Test content")

        # Use convenience function
        result = read_file(file_path)

        # Verify
        assert result.success is True
        assert result.data == "Test content"

    def test_metadata_populated(self, temp_file):
        """Test that metadata is populated correctly"""
        file_path = temp_file("Line 1\nLine 2\nLine 3")

        result = read_file(file_path)

        # Check metadata fields
        assert 'num_lines' in result.metadata
        assert 'num_chars' in result.metadata
        assert 'file_path' in result.metadata
        assert 'file_size_bytes' in result.metadata
        assert result.metadata['num_lines'] == 3

    def test_read_spec_file(self, fixtures_dir):
        """Test reading a TLA+ spec file"""
        # Use actual fixture file
        spec_file = fixtures_dir / "sample_specs" / "simple.tla"

        result = read_file(str(spec_file))

        # Verify
        assert result.success is True
        assert "MODULE simple" in result.data
        assert "EXTENDS Naturals" in result.data
        assert result.metadata['num_lines'] > 0

    def test_tool_properties(self):
        """Test that tool has correct name and description"""
        tool = ReadTool()

        assert tool.name == "read"
        assert len(tool.description) > 0
        assert "read" in tool.description.lower()

    def test_error_suggestions_helpful(self):
        """Test that error messages include helpful suggestions"""
        tool = ReadTool()
        result = tool.run(file_path="/nonexistent.txt")

        # Should have suggestions
        assert len(result.suggestions) > 0
        assert any("path" in s.lower() for s in result.suggestions)

    def test_handle_permission_error(self, temp_dir):
        """Test handling of permission errors"""
        # Create a file with no read permissions
        test_file = temp_dir / "noperm.txt"
        test_file.write_text("test")
        test_file.chmod(0o000)  # No permissions

        try:
            tool = ReadTool()
            result = tool.run(file_path=str(test_file))

            # Should fail gracefully
            assert result.success is False
            assert "permission" in result.error.lower()
        finally:
            # Restore permissions for cleanup
            test_file.chmod(0o644)


if __name__ == "__main__":
    # Run tests if executed directly
    pytest.main([__file__, "-v"])
