"""
pytest configuration and shared fixtures

This file provides minimal, essential fixtures used across tests.
Only add fixtures that are actually used by multiple tests.
"""

import pytest
import tempfile
import os
from pathlib import Path


@pytest.fixture
def fixtures_dir():
    """
    Path to the fixtures directory

    Usage:
        def test_read_spec(fixtures_dir):
            spec_file = fixtures_dir / "sample_specs" / "simple.tla"
            content = spec_file.read_text()
    """
    return Path(__file__).parent / "fixtures"


@pytest.fixture
def temp_file():
    """
    Create temporary files that are automatically cleaned up

    Usage:
        def test_something(temp_file):
            file_path = temp_file("test content")
            # file_path is a string path to the temp file
    """
    created_files = []

    def _create_temp_file(content: str, suffix: str = '.txt'):
        fd, path = tempfile.mkstemp(suffix=suffix, text=True)
        os.write(fd, content.encode('utf-8'))
        os.close(fd)
        created_files.append(path)
        return path

    yield _create_temp_file

    # Cleanup
    for path in created_files:
        try:
            os.unlink(path)
        except:
            pass


@pytest.fixture
def temp_dir():
    """
    Create a temporary directory that is automatically cleaned up

    Usage:
        def test_something(temp_dir):
            # temp_dir is a Path object
            test_file = temp_dir / "test.txt"
            test_file.write_text("content")
    """
    with tempfile.TemporaryDirectory() as tmpdir:
        yield Path(tmpdir)
