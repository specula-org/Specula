"""Tests for MCP handlers.

Run with:
    python -m pytest tools/inv_checking_tool/tests/test_mcp_handlers.py -v
"""

import json
import os
import sys
import tempfile
import pytest
from pathlib import Path

# Add parent directories to path for imports
current_dir = Path(__file__).parent
package_dir = current_dir.parent
tools_dir = package_dir.parent
sys.path.insert(0, str(tools_dir))

from inv_checking_tool.src.mcp.handlers import SummaryHandler, StateHandler, CompareHandler


# Path to test data
TEST_DATA_DIR = Path(__file__).parent.parent.parent.parent / "data"
SAMPLE_OUTPUT_FILE = TEST_DATA_DIR / "workloads/etcdraft/scenarios/snapshot/spec/nohup.out"


@pytest.mark.skipif(not SAMPLE_OUTPUT_FILE.exists(), reason="Sample file not found")
class TestSummaryHandler:
    """Tests for SummaryHandler."""

    @pytest.fixture
    def handler(self):
        return SummaryHandler()

    @pytest.mark.asyncio
    async def test_get_summary(self, handler):
        """Test getting summary."""
        result = await handler.handle({"file_path": str(SAMPLE_OUTPUT_FILE)})
        data = json.loads(result)

        assert data["success"] is True
        assert data["violation_name"] == "QuorumLogInv"
        assert data["trace_length"] == 76
        assert "actions" in data
        assert "statistics" in data
        assert "variables" in data

    @pytest.mark.asyncio
    async def test_missing_file_path(self, handler):
        """Test error when file_path is missing."""
        result = await handler.handle({})
        data = json.loads(result)

        assert data["success"] is False
        assert "error" in data

    @pytest.mark.asyncio
    async def test_file_not_found(self, handler):
        """Test error when file doesn't exist."""
        result = await handler.handle({"file_path": "/nonexistent/file.log"})
        data = json.loads(result)

        assert data["success"] is False
        assert data["error"]["type"] == "FileNotFoundError"


@pytest.mark.skipif(not SAMPLE_OUTPUT_FILE.exists(), reason="Sample file not found")
class TestStateHandler:
    """Tests for StateHandler."""

    @pytest.fixture
    def handler(self):
        return StateHandler()

    @pytest.mark.asyncio
    async def test_get_single_state(self, handler):
        """Test getting a single state."""
        result = await handler.handle({
            "file_path": str(SAMPLE_OUTPUT_FILE),
            "index": 1
        })
        data = json.loads(result)

        assert data["success"] is True
        assert data["index"] == 1
        assert data["action"] == "MCInit"
        assert "variables" in data

    @pytest.mark.asyncio
    async def test_get_last_state(self, handler):
        """Test getting the last state."""
        result = await handler.handle({
            "file_path": str(SAMPLE_OUTPUT_FILE),
            "index": -1
        })
        data = json.loads(result)

        assert data["success"] is True
        assert data["index"] == 76

    @pytest.mark.asyncio
    async def test_get_state_with_path(self, handler):
        """Test querying a nested path."""
        result = await handler.handle({
            "file_path": str(SAMPLE_OUTPUT_FILE),
            "index": 1,
            "path": "currentTerm.s1"
        })
        data = json.loads(result)

        assert data["success"] is True
        assert data["path"] == "currentTerm.s1"
        assert data["value"] == 1

    @pytest.mark.asyncio
    async def test_get_multiple_states(self, handler):
        """Test getting multiple states."""
        result = await handler.handle({
            "file_path": str(SAMPLE_OUTPUT_FILE),
            "indices": "1:3"
        })
        data = json.loads(result)

        assert data["success"] is True
        assert data["count"] == 3
        assert len(data["states"]) == 3

    @pytest.mark.asyncio
    async def test_get_states_from_end(self, handler):
        """Test getting last N states."""
        result = await handler.handle({
            "file_path": str(SAMPLE_OUTPUT_FILE),
            "indices": "-3:"
        })
        data = json.loads(result)

        assert data["success"] is True
        assert data["count"] == 3
        assert data["states"][0]["index"] == 74
        assert data["states"][2]["index"] == 76

    @pytest.mark.asyncio
    async def test_get_state_with_variables(self, handler):
        """Test filtering to specific variables."""
        result = await handler.handle({
            "file_path": str(SAMPLE_OUTPUT_FILE),
            "index": 1,
            "variables": ["currentTerm", "state"]
        })
        data = json.loads(result)

        assert data["success"] is True
        assert "currentTerm" in data["variables"]
        assert "state" in data["variables"]
        assert len(data["variables"]) == 2

    @pytest.mark.asyncio
    async def test_missing_index(self, handler):
        """Test error when neither index nor indices provided."""
        result = await handler.handle({
            "file_path": str(SAMPLE_OUTPUT_FILE)
        })
        data = json.loads(result)

        assert data["success"] is False


@pytest.mark.skipif(not SAMPLE_OUTPUT_FILE.exists(), reason="Sample file not found")
class TestCompareHandler:
    """Tests for CompareHandler."""

    @pytest.fixture
    def handler(self):
        return CompareHandler()

    @pytest.mark.asyncio
    async def test_compare_states(self, handler):
        """Test comparing two states."""
        result = await handler.handle({
            "file_path": str(SAMPLE_OUTPUT_FILE),
            "index1": -2,
            "index2": -1
        })
        data = json.loads(result)

        assert data["success"] is True
        assert data["mode"] == "compare"
        assert data["state1_index"] == 75
        assert data["state2_index"] == 76
        assert "changed_variables" in data
        assert "changes" in data

    @pytest.mark.asyncio
    async def test_track_variable(self, handler):
        """Test tracking variable changes."""
        result = await handler.handle({
            "file_path": str(SAMPLE_OUTPUT_FILE),
            "track_variable": "currentTerm"
        })
        data = json.loads(result)

        assert data["success"] is True
        assert data["mode"] == "track"
        assert data["variable"] == "currentTerm"
        assert "total_changes" in data
        assert "changes" in data

    @pytest.mark.asyncio
    async def test_track_variable_with_path(self, handler):
        """Test tracking variable with sub-path."""
        result = await handler.handle({
            "file_path": str(SAMPLE_OUTPUT_FILE),
            "track_variable": "state",
            "track_path": "s1"
        })
        data = json.loads(result)

        assert data["success"] is True
        assert data["variable"] == "state.s1"

    @pytest.mark.asyncio
    async def test_missing_mode_params(self, handler):
        """Test error when neither compare nor track params provided."""
        result = await handler.handle({
            "file_path": str(SAMPLE_OUTPUT_FILE)
        })
        data = json.loads(result)

        assert data["success"] is False


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
