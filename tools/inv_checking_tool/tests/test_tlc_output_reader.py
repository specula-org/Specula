"""Comprehensive tests for TLCOutputReader.

Run with:
    python -m pytest tools/inv_checking_tool/tests/test_tlc_output_reader.py -v

Or run directly:
    python tools/inv_checking_tool/tests/test_tlc_output_reader.py
"""

import os
import sys
import json
import tempfile
import pytest
from pathlib import Path

# Add parent directories to path for imports
current_dir = Path(__file__).parent
package_dir = current_dir.parent
tools_dir = package_dir.parent
sys.path.insert(0, str(tools_dir))

from inv_checking_tool import TLCOutputReader
from inv_checking_tool.src.utils.path_parser import (
    parse_variable_path,
    get_value_at_path,
    PathParseError,
    PathAccessError,
)
from inv_checking_tool.src.utils.preprocessing import (
    strip_ansi_codes,
    extract_violation_info,
)


# Path to test data
TEST_DATA_DIR = Path(__file__).parent.parent.parent.parent / "data"
SAMPLE_OUTPUT_FILE = TEST_DATA_DIR / "workloads/etcdraft/scenarios/snapshot/spec/nohup.out"


class TestPathParser:
    """Tests for path parsing utilities."""

    def test_simple_path(self):
        """Test parsing a simple variable name."""
        result = parse_variable_path("currentTerm")
        assert result == ["currentTerm"]

    def test_dotted_path(self):
        """Test parsing a dot-separated path."""
        result = parse_variable_path("log.s1.entries")
        assert result == ["log", "s1", "entries"]

    def test_path_with_index(self):
        """Test parsing a path with array index."""
        result = parse_variable_path("log.s1.entries[0]")
        assert result == ["log", "s1", "entries", 0]

    def test_path_with_multiple_indices(self):
        """Test parsing a path with multiple indices."""
        result = parse_variable_path("data[0][1]")
        assert result == ["data", 0, 1]

    def test_path_with_string_index(self):
        """Test parsing a path with string index."""
        result = parse_variable_path("config[s1]")
        assert result == ["config", "s1"]

    def test_complex_path(self):
        """Test parsing a complex nested path."""
        result = parse_variable_path("log.s1.entries[0].term")
        assert result == ["log", "s1", "entries", 0, "term"]

    def test_empty_path_raises_error(self):
        """Test that empty path raises PathParseError."""
        with pytest.raises(PathParseError):
            parse_variable_path("")

    def test_get_value_simple(self):
        """Test getting a simple value."""
        data = {"a": 1, "b": 2}
        assert get_value_at_path(data, "a") == 1

    def test_get_value_nested(self):
        """Test getting a nested value."""
        data = {"log": {"s1": {"entries": [{"term": 1}]}}}
        assert get_value_at_path(data, "log.s1.entries[0].term") == 1

    def test_get_value_missing_key(self):
        """Test that missing key raises PathAccessError."""
        data = {"a": 1}
        with pytest.raises(PathAccessError):
            get_value_at_path(data, "b")

    def test_get_value_index_out_of_range(self):
        """Test that out of range index raises PathAccessError."""
        data = {"arr": [1, 2, 3]}
        with pytest.raises(PathAccessError):
            get_value_at_path(data, "arr[10]")


class TestPreprocessing:
    """Tests for preprocessing utilities."""

    def test_strip_ansi_codes(self):
        """Test stripping ANSI escape codes."""
        text = "\x1b[0;32mHello\x1b[0m World"
        result = strip_ansi_codes(text)
        assert result == "Hello World"

    def test_strip_ansi_codes_empty(self):
        """Test stripping from text without ANSI codes."""
        text = "Hello World"
        result = strip_ansi_codes(text)
        assert result == "Hello World"

    def test_extract_invariant_violation(self):
        """Test extracting invariant violation info."""
        content = "Error: Invariant QuorumLogInv is violated."
        vtype, vname = extract_violation_info(content)
        assert vtype == "invariant"
        assert vname == "QuorumLogInv"

    def test_extract_property_violation(self):
        """Test extracting temporal property violation info."""
        content = "Error: Temporal property Liveness is violated."
        vtype, vname = extract_violation_info(content)
        assert vtype == "property"
        assert vname == "Liveness"

    def test_extract_no_violation(self):
        """Test when there's no violation."""
        content = "TLC finished successfully."
        vtype, vname = extract_violation_info(content)
        assert vtype is None
        assert vname is None


@pytest.mark.skipif(not SAMPLE_OUTPUT_FILE.exists(), reason="Sample file not found")
class TestTLCOutputReader:
    """Tests for TLCOutputReader class."""

    @pytest.fixture
    def reader(self):
        """Create a reader for the sample file."""
        return TLCOutputReader(str(SAMPLE_OUTPUT_FILE))

    def test_load_file(self, reader):
        """Test that file loads successfully."""
        assert reader is not None
        assert reader.trace_length > 0

    def test_trace_length(self, reader):
        """Test trace length is correct."""
        assert reader.trace_length == 76

    def test_get_summary(self, reader):
        """Test getting trace summary."""
        summary = reader.get_summary()
        assert summary.violation_type == "invariant"
        assert summary.violation_name == "QuorumLogInv"
        assert summary.trace_length == 76
        assert len(summary.actions) == 76

    def test_get_summary_statistics(self, reader):
        """Test that summary includes statistics."""
        summary = reader.get_summary()
        assert "states_generated" in summary.statistics
        assert summary.statistics["states_generated"] == 148265621

    def test_get_state_first(self, reader):
        """Test getting first state by index."""
        state = reader.get_state(1)
        assert state.index == 1
        assert state.action == "MCInit"

    def test_get_state_last(self, reader):
        """Test getting last state by 'last' keyword."""
        state = reader.get_state("last")
        assert state.index == 76

    def test_get_state_negative_index(self, reader):
        """Test getting state by negative index."""
        state = reader.get_state(-1)
        assert state.index == 76

        state2 = reader.get_state(-2)
        assert state2.index == 75

    def test_get_state_first_keyword(self, reader):
        """Test getting first state by 'first' keyword."""
        state = reader.get_state("first")
        assert state.index == 1

    def test_get_state_with_variables(self, reader):
        """Test getting state with filtered variables."""
        state = reader.get_state(1, variables=["currentTerm", "state"])
        assert "currentTerm" in state.variables
        assert "state" in state.variables
        assert len(state.variables) == 2

    def test_get_state_invalid_index(self, reader):
        """Test that invalid index raises error."""
        with pytest.raises(IndexError):
            reader.get_state(1000)

    def test_get_state_zero_index(self, reader):
        """Test that zero index raises error (1-indexed)."""
        with pytest.raises(ValueError):
            reader.get_state(0)

    def test_get_states_list(self, reader):
        """Test getting multiple states by list."""
        states = reader.get_states([1, 5, 10])
        assert len(states) == 3
        assert states[0].index == 1
        assert states[1].index == 5
        assert states[2].index == 10

    def test_get_states_range(self, reader):
        """Test getting states by range string."""
        states = reader.get_states("1:5")
        assert len(states) == 5
        assert [s.index for s in states] == [1, 2, 3, 4, 5]

    def test_get_states_from_end(self, reader):
        """Test getting last N states."""
        states = reader.get_states("-3:")
        assert len(states) == 3
        assert [s.index for s in states] == [74, 75, 76]

    def test_get_states_first_n(self, reader):
        """Test getting first N states."""
        states = reader.get_states(":3")
        assert len(states) == 3
        assert [s.index for s in states] == [1, 2, 3]

    def test_get_variable(self, reader):
        """Test getting a specific variable."""
        term = reader.get_variable(1, "currentTerm")
        assert isinstance(term, dict)
        assert "s1" in term

    def test_get_variable_not_found(self, reader):
        """Test that missing variable raises KeyError."""
        with pytest.raises(KeyError):
            reader.get_variable(1, "nonexistent")

    def test_get_variable_at_path(self, reader):
        """Test getting nested variable value."""
        term = reader.get_variable_at_path(1, "currentTerm.s1")
        assert term == 1

    def test_get_variable_at_path_deep(self, reader):
        """Test getting deeply nested value."""
        # log.s1 has structure: {offset, entries, snapshotIndex, snapshotTerm}
        offset = reader.get_variable_at_path(1, "log.s1.offset")
        assert offset == 1

    def test_get_variable_at_path_with_index(self, reader):
        """Test getting value with array index."""
        # entries is a list
        entry = reader.get_variable_at_path(1, "log.s1.entries[0]")
        assert isinstance(entry, dict)
        assert "term" in entry

    def test_get_variable_at_path_invalid(self, reader):
        """Test that invalid path raises PathAccessError."""
        with pytest.raises(PathAccessError):
            reader.get_variable_at_path(1, "nonexistent.path")

    def test_get_all_variables(self, reader):
        """Test getting list of all variables."""
        variables = reader.get_all_variables()
        assert "currentTerm" in variables
        assert "state" in variables
        assert "log" in variables

    def test_get_actions_list(self, reader):
        """Test getting action sequence."""
        actions = reader.get_actions_list()
        assert len(actions) == 76
        assert actions[0]["action"] == "MCInit"
        assert actions[0]["index"] == 1

    def test_compare_states(self, reader):
        """Test comparing two states."""
        diff = reader.compare_states(1, 2)
        assert "changed_variables" in diff
        assert "changes" in diff
        assert diff["state1_index"] == 1
        assert diff["state2_index"] == 2

    def test_compare_states_last_two(self, reader):
        """Test comparing last two states."""
        diff = reader.compare_states(-2, -1)
        assert diff["state1_index"] == 75
        assert diff["state2_index"] == 76

    def test_find_variable_changes(self, reader):
        """Test finding where a variable changes."""
        changes = reader.find_variable_changes("currentTerm")
        assert isinstance(changes, list)
        # Should have at least some changes
        for change in changes:
            assert "from_state" in change
            assert "to_state" in change
            assert "before" in change
            assert "after" in change

    def test_find_variable_changes_with_path(self, reader):
        """Test finding changes for a nested path."""
        changes = reader.find_variable_changes("state", "s1")
        assert isinstance(changes, list)

    def test_search_states(self, reader):
        """Test searching states with predicate."""
        # Find states where s1 is Leader
        leader_states = reader.search_states(
            lambda s: s.get("state", {}).get("s1") == "Leader"
        )
        assert isinstance(leader_states, list)
        assert all(isinstance(i, int) for i in leader_states)

    def test_format_state(self, reader):
        """Test formatting a state for display."""
        formatted = reader.format_state(1)
        assert "State 1" in formatted
        assert "MCInit" in formatted

    def test_format_summary(self, reader):
        """Test formatting summary for display."""
        formatted = reader.format_summary()
        assert "QuorumLogInv" in formatted
        assert "76 states" in formatted

    def test_repr(self, reader):
        """Test string representation."""
        repr_str = repr(reader)
        assert "TLCOutputReader" in repr_str
        assert "76" in repr_str


class TestTLCOutputReaderEdgeCases:
    """Edge case tests for TLCOutputReader."""

    def test_file_not_found(self):
        """Test that FileNotFoundError is raised for missing file."""
        with pytest.raises(FileNotFoundError):
            TLCOutputReader("/nonexistent/path/to/file.log")

    def test_create_minimal_trace_file(self):
        """Test loading a minimal valid trace file."""
        content = """Error: Invariant TestInv is violated.
Error: The behavior up to this point is:
State 1: <Init line 1, col 1 to line 1, col 10 of module Test>
/\\ x = 1
/\\ y = 2

State 2: <Next line 2, col 1 to line 2, col 10 of module Test>
/\\ x = 2
/\\ y = 3

The number of states generated: 100
"""
        with tempfile.NamedTemporaryFile(mode='w', suffix='.log', delete=False) as f:
            f.write(content)
            f.flush()

            try:
                reader = TLCOutputReader(f.name)
                assert reader.trace_length == 2
                summary = reader.get_summary()
                assert summary.violation_name == "TestInv"

                state1 = reader.get_state(1)
                assert state1.variables["x"] == 1
                assert state1.variables["y"] == 2

                state2 = reader.get_state(2)
                assert state2.variables["x"] == 2
                assert state2.variables["y"] == 3
            finally:
                os.unlink(f.name)

    def test_trace_with_nested_structures(self):
        """Test loading trace with complex nested structures."""
        content = """Error: Invariant TestInv is violated.
Error: The behavior up to this point is:
State 1: <Init line 1, col 1 to line 1, col 10 of module Test>
/\\ config = (s1 :> [a |-> 1, b |-> 2] @@ s2 :> [a |-> 3, b |-> 4])
/\\ log = <<[term |-> 1, value |-> "x"], [term |-> 2, value |-> "y"]>>

The number of states generated: 100
"""
        with tempfile.NamedTemporaryFile(mode='w', suffix='.log', delete=False) as f:
            f.write(content)
            f.flush()

            try:
                reader = TLCOutputReader(f.name)

                # Test nested dict access
                val = reader.get_variable_at_path(1, "config.s1.a")
                assert val == 1

                # Test array access
                val = reader.get_variable_at_path(1, "log[0].term")
                assert val == 1

                val = reader.get_variable_at_path(1, "log[1].value")
                assert val == "y"
            finally:
                os.unlink(f.name)


def run_tests():
    """Run tests without pytest."""
    import traceback

    test_classes = [
        TestPathParser,
        TestPreprocessing,
        TestTLCOutputReader,
        TestTLCOutputReaderEdgeCases,
    ]

    passed = 0
    failed = 0
    skipped = 0

    for test_class in test_classes:
        print(f"\n{'='*60}")
        print(f"Running {test_class.__name__}")
        print('='*60)

        # Check for skip condition
        if hasattr(test_class, 'pytestmark'):
            for mark in test_class.pytestmark:
                if mark.name == 'skipif' and mark.args[0]:
                    print(f"  SKIPPED: {mark.kwargs.get('reason', 'No reason')}")
                    skipped += 1
                    continue

        instance = test_class()

        # Get fixture if needed
        fixture = None
        if hasattr(instance, 'reader'):
            try:
                if SAMPLE_OUTPUT_FILE.exists():
                    fixture = TLCOutputReader(str(SAMPLE_OUTPUT_FILE))
            except Exception as e:
                print(f"  Failed to create fixture: {e}")
                continue

        for name in dir(instance):
            if name.startswith('test_'):
                method = getattr(instance, name)
                try:
                    # Inject fixture if method accepts it
                    import inspect
                    sig = inspect.signature(method)
                    if 'reader' in sig.parameters and fixture:
                        method(fixture)
                    else:
                        method()
                    print(f"  PASS: {name}")
                    passed += 1
                except pytest.skip.Exception as e:
                    print(f"  SKIP: {name} - {e}")
                    skipped += 1
                except AssertionError as e:
                    print(f"  FAIL: {name}")
                    print(f"        {e}")
                    failed += 1
                except Exception as e:
                    # Check if it's an expected exception
                    if "pytest.raises" in str(type(method)):
                        print(f"  PASS: {name}")
                        passed += 1
                    else:
                        print(f"  ERROR: {name}")
                        print(f"        {type(e).__name__}: {e}")
                        traceback.print_exc()
                        failed += 1

    print(f"\n{'='*60}")
    print(f"Results: {passed} passed, {failed} failed, {skipped} skipped")
    print('='*60)

    return failed == 0


if __name__ == "__main__":
    # Try pytest first, fall back to manual runner
    try:
        sys.exit(pytest.main([__file__, "-v"]))
    except Exception:
        success = run_tests()
        sys.exit(0 if success else 1)
