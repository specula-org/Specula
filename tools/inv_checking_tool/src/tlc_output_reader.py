"""TLC Output Reader - Agent-friendly interface for TLC model checking results.

This module provides the TLCOutputReader class, which offers a convenient
interface for reading and analyzing TLC model checker output, particularly
for debugging invariant violations.

Example usage:
    reader = TLCOutputReader("path/to/tlc_output.log")

    # Get summary
    summary = reader.get_summary()
    print(f"Violated: {summary['violation_name']}")
    print(f"Trace length: {summary['trace_length']}")

    # Get specific states
    first_state = reader.get_state(1)      # First state (1-indexed)
    last_state = reader.get_state(-1)      # Last state
    last_state = reader.get_state("last")  # Also last state

    # Get variable at path
    term = reader.get_variable_at_path(1, "currentTerm.s1")

    # Compare states
    diff = reader.compare_states(-2, -1)  # Compare last two states
"""

import io
import json
from typing import Any, Dict, List, Optional, Union
from dataclasses import dataclass, field
from pathlib import Path

from .utils.preprocessing import (
    ERROR_BEHAVIOR_MARKER,
    convert_to_trace_format,
    extract_counterexample_path,
    extract_statistics,
    extract_violation_info,
    preprocess_tlc_output,
    strip_ansi_codes,
)
from .utils.path_parser import get_value_at_path, format_value, PathAccessError
from .trace_reader import TraceReader


@dataclass
class StateInfo:
    """Information about a single state in the trace."""
    index: int  # 1-indexed state number
    action: Optional[str]  # Action name (e.g., "MCInit", "HandleRequestVoteRequest")
    action_detail: Optional[str]  # Full action string with location
    variables: Dict[str, Any]  # State variables


@dataclass
class TraceSummary:
    """Summary information about the TLC trace."""
    violation_type: Optional[str]  # "invariant" or "property"
    violation_name: Optional[str]  # Name of the violated invariant/property
    trace_length: int  # Number of states in the trace
    actions: List[str]  # List of action names
    statistics: Dict[str, Any] = field(default_factory=dict)  # TLC statistics


class TLCOutputReader:
    """Agent-friendly interface for reading TLC model checking output.

    This class provides methods to:
    - Get summary information about invariant violations
    - Access individual states by index (supports negative indexing)
    - Access nested variables using path syntax
    - Compare states to find differences
    - Search for states where specific variables change

    Attributes:
        file_path: Path to the TLC output file.
        states: List of parsed states.
        metadata: Metadata extracted from the output (violation info, stats).
    """

    def __init__(self, file_path: str, save_action_name: bool = True, mode: str = "auto"):
        """Initialize the reader with a TLC output file.

        Args:
            file_path: Path to the TLC output file.
            save_action_name: Whether to extract action names from states.
            mode: Parsing mode. One of:
                - "auto": Auto-detect format. Tries JSON first, falls back to text.
                - "json": Force JSON mode (requires -dumptrace json output).
                - "text": Force text mode (parses raw TLC output directly).

        Raises:
            FileNotFoundError: If the file does not exist.
            ValueError: If the file does not contain a valid TLC trace.
        """
        if mode not in ("auto", "json", "text"):
            raise ValueError(f"Invalid mode: {mode!r}. Must be 'auto', 'json', or 'text'.")

        self.file_path = file_path
        self.mode = mode
        self._states: List[Dict[str, Any]] = []
        self._metadata: Dict[str, Any] = {}
        self._action_details: List[str] = []

        self._load_and_parse(save_action_name)

    def _load_and_parse(self, save_action_name: bool) -> None:
        """Load and parse the TLC output file.

        Auto-detection logic:
        1. If a counterexample JSON path is found in the output, use JSON mode.
        2. Otherwise, if the error behavior marker is present, use text mode.
        3. Otherwise, raise ValueError.

        Args:
            save_action_name: Whether to save action names.
        """
        content = Path(self.file_path).read_text(encoding="utf-8", errors="replace")
        content = strip_ansi_codes(content)

        violation_type, violation_name = extract_violation_info(content)
        self._metadata = {"statistics": extract_statistics(content)}
        if violation_name:
            self._metadata["violation_type"] = violation_type
            self._metadata["violation_name"] = violation_name

        counterexample_path = extract_counterexample_path(content)
        has_error_trace = ERROR_BEHAVIOR_MARKER in content

        # Determine effective mode
        if self.mode == "json":
            effective_mode = "json"
        elif self.mode == "text":
            effective_mode = "text"
        else:  # auto
            if counterexample_path:
                effective_mode = "json"
            elif has_error_trace:
                effective_mode = "text"
            else:
                raise ValueError(
                    "Could not auto-detect trace format. "
                    "No JSON counterexample path or text error trace found in TLC output."
                )

        self._metadata["parse_mode"] = effective_mode

        if effective_mode == "json":
            self._load_json(counterexample_path, save_action_name)
        else:
            self._load_text(content, save_action_name)

    def _load_json(self, counterexample_path: Optional[str], save_action_name: bool) -> None:
        """Load trace from a JSON counterexample file."""
        if not counterexample_path:
            raise ValueError(
                "JSON mode requires a counterexample path in TLC output. "
                "Expected 'CounterExample written: <file>'."
            )

        trace_path = Path(counterexample_path)
        if not trace_path.is_absolute():
            trace_path = Path(self.file_path).parent / trace_path
        self._metadata["counterexample_path"] = str(trace_path)

        with trace_path.open(encoding="utf-8", errors="replace") as f:
            trace = json.load(f)

        # -dumpTrace json wraps data under "counterexample" key; unwrap if present.
        if "counterexample" in trace and isinstance(trace["counterexample"], dict):
            trace = trace["counterexample"]

        self._states, self._action_details = self._parse_trace(trace, save_action_name)

    def _load_text(self, content: str, save_action_name: bool) -> None:
        """Load trace by parsing raw TLC text output using TraceReader."""
        if ERROR_BEHAVIOR_MARKER not in content:
            raise ValueError(
                "Text mode requires an error trace in TLC output. "
                f"Expected '{ERROR_BEHAVIOR_MARKER}' marker."
            )

        trace_content = convert_to_trace_format(content)

        tr = TraceReader(save_action_name=save_action_name)
        f = io.StringIO(trace_content)

        for state, state_str in tr.trace_reader_with_state_str(f):
            self._states.append(state)

            action_detail = None
            for line in state_str.split('\n'):
                if line.startswith('\\*') and '<' in line:
                    action_detail = line.strip()[2:].strip()
                    break
            self._action_details.append(action_detail)

        if not self._states:
            raise ValueError("No states found in TLC text output.")

    def _parse_trace(
        self,
        trace: Dict[str, Any],
        save_action_name: bool,
    ) -> tuple[List[Dict[str, Any]], List[Optional[str]]]:
        action_by_state = {}
        detail_by_state = {}
        for entry in trace.get("action", []):
            if not isinstance(entry, list) or len(entry) < 3:
                continue
            action = entry[1]
            to_state = entry[2]
            if not isinstance(action, dict) or not isinstance(to_state, list) or not to_state:
                continue
            state_id = to_state[0]
            name = action.get("name")
            if name:
                action_by_state[state_id] = name
            detail_by_state[state_id] = self._format_action_detail(action)

        states = []
        details = []
        for entry in trace.get("state", []):
            if not isinstance(entry, list) or len(entry) < 2:
                continue
            state_id, variables = entry[0], entry[1] or {}
            state = dict(variables)
            if save_action_name:
                state["_action"] = action_by_state.get(state_id, "Unknown")
            states.append(state)
            details.append(detail_by_state.get(state_id))

        if not states:
            raise ValueError("No states found in trace JSON.")

        return states, details

    @staticmethod
    def _format_action_detail(action: Dict[str, Any]) -> Optional[str]:
        name = action.get("name")
        if not name:
            return None
        location = action.get("location") or {}
        if location:
            return (
                f"<{name} line {location.get('beginLine')}, col {location.get('beginColumn')} "
                f"to line {location.get('endLine')}, col {location.get('endColumn')} "
                f"of module {location.get('module')}>"
            )
        return f"<{name}>"

    @property
    def trace_length(self) -> int:
        """Return the number of states in the trace."""
        return len(self._states)

    def _normalize_index(self, index: Union[int, str]) -> int:
        """Convert various index formats to a 0-based index.

        Args:
            index: State index. Can be:
                - Positive int: 1-indexed (TLC convention)
                - Negative int: From end (-1 = last)
                - "first": First state
                - "last": Last state

        Returns:
            0-based index into self._states.

        Raises:
            ValueError: If the index is invalid.
            IndexError: If the index is out of range.
        """
        if isinstance(index, str):
            index_lower = index.lower()
            if index_lower == "first":
                return 0
            elif index_lower == "last":
                return len(self._states) - 1
            else:
                try:
                    index = int(index)
                except ValueError:
                    raise ValueError(
                        f"Invalid index: {index}. Use positive int, negative int, 'first', or 'last'."
                    )

        if not self._states:
            raise IndexError("Trace is empty")

        # Convert 1-indexed to 0-indexed for positive numbers
        if index > 0:
            idx = index - 1
        elif index < 0:
            idx = len(self._states) + index
        else:
            raise ValueError("State index must be non-zero (1-indexed)")

        if idx < 0 or idx >= len(self._states):
            raise IndexError(
                f"State index {index} out of range. "
                f"Valid range: 1 to {len(self._states)} or -1 to -{len(self._states)}"
            )

        return idx

    def _parse_range(self, range_str: str) -> List[int]:
        """Parse a range string into a list of 0-based indices.

        Args:
            range_str: Range string like "1:5", "-3:", ":5", "1,5,10"

        Returns:
            List of 0-based indices.
        """
        range_str = range_str.strip()

        # Handle comma-separated list
        if ',' in range_str:
            indices = []
            for part in range_str.split(','):
                idx = self._normalize_index(part.strip())
                indices.append(idx)
            return indices

        # Handle range with colon
        if ':' not in range_str:
            return [self._normalize_index(range_str)]

        parts = range_str.split(':')
        if len(parts) != 2:
            raise ValueError(f"Invalid range format: {range_str}")

        start_str, end_str = parts

        # Parse start
        if start_str.strip() == '':
            start = 0
        else:
            start = self._normalize_index(start_str.strip())

        # Parse end
        if end_str.strip() == '':
            end = len(self._states)
        else:
            # End is inclusive in our API
            end = self._normalize_index(end_str.strip()) + 1

        return list(range(start, end))

    def get_summary(self) -> TraceSummary:
        """Get a summary of the TLC trace.

        Returns:
            TraceSummary object containing:
            - violation_type: Type of violation ("invariant" or "property")
            - violation_name: Name of the violated invariant/property
            - trace_length: Number of states
            - actions: List of action names in order
            - statistics: TLC statistics (states generated, etc.)
        """
        actions = []
        for state in self._states:
            action = state.get('_action', 'Unknown')
            actions.append(action)

        return TraceSummary(
            violation_type=self._metadata.get('violation_type'),
            violation_name=self._metadata.get('violation_name'),
            trace_length=len(self._states),
            actions=actions,
            statistics=self._metadata.get('statistics', {}),
        )

    def get_state(
        self,
        index: Union[int, str],
        variables: Optional[List[str]] = None,
    ) -> StateInfo:
        """Get a single state by index.

        Args:
            index: State index. Supports:
                - Positive int: 1-indexed (State 1, State 2, etc.)
                - Negative int: From end (-1 = last state)
                - "first" or "last"
            variables: Optional list of variable names to include.
                      If None, includes all variables.

        Returns:
            StateInfo object with state data.

        Examples:
            >>> reader.get_state(1)        # First state
            >>> reader.get_state(-1)       # Last state
            >>> reader.get_state("last")   # Also last state
            >>> reader.get_state(5, variables=["currentTerm", "state"])
        """
        idx = self._normalize_index(index)
        state = self._states[idx]
        action_detail = self._action_details[idx] if idx < len(self._action_details) else None

        # Filter variables if specified
        if variables is not None:
            filtered = {}
            for var in variables:
                if var in state:
                    filtered[var] = state[var]
                elif not var.startswith('_'):
                    # Try to find case-insensitive match
                    for k, v in state.items():
                        if k.lower() == var.lower():
                            filtered[var] = v
                            break
            vars_dict = filtered
        else:
            # Exclude internal keys
            vars_dict = {k: v for k, v in state.items() if not k.startswith('_')}

        return StateInfo(
            index=idx + 1,  # Return 1-indexed
            action=state.get('_action'),
            action_detail=action_detail,
            variables=vars_dict,
        )

    def get_states(
        self,
        indices: Union[str, List[Union[int, str]]],
        variables: Optional[List[str]] = None,
    ) -> List[StateInfo]:
        """Get multiple states.

        Args:
            indices: Can be:
                - List of indices: [1, 5, 10] or [1, -1]
                - Range string: "1:5" (states 1-5), "-3:" (last 3), ":5" (first 5)
                - Comma-separated: "1,5,10"
            variables: Optional list of variable names to include.

        Returns:
            List of StateInfo objects.

        Examples:
            >>> reader.get_states([1, -1])           # First and last
            >>> reader.get_states("1:5")             # States 1-5
            >>> reader.get_states("-3:")             # Last 3 states
            >>> reader.get_states("1,5,10")          # States 1, 5, 10
        """
        if isinstance(indices, str):
            idx_list = self._parse_range(indices)
        else:
            idx_list = [self._normalize_index(i) for i in indices]

        return [self.get_state(idx + 1, variables) for idx in idx_list]

    def get_variable(
        self,
        state_index: Union[int, str],
        variable_name: str,
    ) -> Any:
        """Get a specific variable from a state.

        Args:
            state_index: State index (1-indexed, negative, or "first"/"last").
            variable_name: Name of the variable.

        Returns:
            The variable's value.

        Raises:
            KeyError: If the variable is not found.
        """
        idx = self._normalize_index(state_index)
        state = self._states[idx]

        if variable_name in state:
            return state[variable_name]

        # Try case-insensitive match
        for k, v in state.items():
            if k.lower() == variable_name.lower():
                return v

        raise KeyError(
            f"Variable '{variable_name}' not found in state {state_index}. "
            f"Available: {[k for k in state.keys() if not k.startswith('_')]}"
        )

    def get_variable_at_path(
        self,
        state_index: Union[int, str],
        path: str,
    ) -> Any:
        """Get a nested variable value using path syntax.

        Args:
            state_index: State index (1-indexed, negative, or "first"/"last").
            path: Dot-separated path to the value.
                  Supports array indexing: "log.s1.entries[0].term"

        Returns:
            The value at the specified path.

        Raises:
            PathAccessError: If the path cannot be traversed.

        Examples:
            >>> reader.get_variable_at_path(1, "currentTerm.s1")
            1
            >>> reader.get_variable_at_path(-1, "log.s1.entries[0].term")
            1
        """
        idx = self._normalize_index(state_index)
        state = self._states[idx]

        # Remove internal keys for cleaner access
        clean_state = {k: v for k, v in state.items() if not k.startswith('_')}

        return get_value_at_path(clean_state, path)

    def get_all_variables(self) -> List[str]:
        """Get list of all variable names in the trace.

        Returns:
            Sorted list of variable names (excluding internal _-prefixed keys).
        """
        if not self._states:
            return []

        # Get from first state (all states should have same variables)
        return sorted([k for k in self._states[0].keys() if not k.startswith('_')])

    def get_actions_list(self) -> List[Dict[str, Any]]:
        """Get the sequence of actions in the trace.

        Returns:
            List of dicts with index, action name, and action detail.

        Example:
            [
                {"index": 1, "action": "MCInit", "detail": "<MCInit line 250...>"},
                {"index": 2, "action": "MCRestart", "detail": "<MCRestart(s1) ...>"},
                ...
            ]
        """
        result = []
        for i, state in enumerate(self._states):
            result.append({
                "index": i + 1,
                "action": state.get('_action', 'Unknown'),
                "detail": self._action_details[i] if i < len(self._action_details) else None,
            })
        return result

    def compare_states(
        self,
        index1: Union[int, str],
        index2: Union[int, str],
        ignore_vars: Optional[List[str]] = None,
    ) -> Dict[str, Any]:
        """Compare two states and find differences.

        Args:
            index1: First state index.
            index2: Second state index.
            ignore_vars: Variables to ignore in comparison.

        Returns:
            Dict with:
            - changed_variables: List of variable names that changed
            - changes: Dict mapping variable name to {before, after}
            - state1_index: 1-indexed state number
            - state2_index: 1-indexed state number
            - state1_action: Action of first state
            - state2_action: Action of second state

        Examples:
            >>> diff = reader.compare_states(-2, -1)
            >>> print(diff["changed_variables"])
            ["currentTerm", "state"]
        """
        idx1 = self._normalize_index(index1)
        idx2 = self._normalize_index(index2)
        state1 = self._states[idx1]
        state2 = self._states[idx2]

        ignore_vars = set(ignore_vars or [])
        ignore_vars.add('_action')  # Always ignore internal keys

        changed_variables = []
        changes = {}

        # Compare all variables
        all_keys = set(state1.keys()) | set(state2.keys())
        for key in sorted(all_keys):
            if key.startswith('_') or key in ignore_vars:
                continue

            val1 = state1.get(key)
            val2 = state2.get(key)

            if val1 != val2:
                changed_variables.append(key)
                changes[key] = {
                    "before": val1,
                    "after": val2,
                }

        return {
            "changed_variables": changed_variables,
            "changes": changes,
            "state1_index": idx1 + 1,
            "state2_index": idx2 + 1,
            "state1_action": state1.get('_action'),
            "state2_action": state2.get('_action'),
        }

    def find_variable_changes(
        self,
        variable_name: str,
        path: Optional[str] = None,
    ) -> List[Dict[str, Any]]:
        """Find all states where a variable changes.

        Args:
            variable_name: Name of the variable to track.
            path: Optional path within the variable (e.g., "s1" for "currentTerm.s1").

        Returns:
            List of change records:
            [
                {
                    "from_state": 5,
                    "to_state": 6,
                    "action": "HandleRequestVote",
                    "before": ...,
                    "after": ...
                },
                ...
            ]
        """
        if not self._states:
            return []

        changes = []
        full_path = f"{variable_name}.{path}" if path else variable_name

        prev_value = None
        for i, state in enumerate(self._states):
            try:
                if path:
                    current_value = get_value_at_path(
                        {k: v for k, v in state.items() if not k.startswith('_')},
                        full_path
                    )
                else:
                    current_value = state.get(variable_name)
            except PathAccessError:
                current_value = None

            if i > 0 and current_value != prev_value:
                changes.append({
                    "from_state": i,  # 1-indexed
                    "to_state": i + 1,
                    "action": state.get('_action'),
                    "before": prev_value,
                    "after": current_value,
                })

            prev_value = current_value

        return changes

    def search_states(
        self,
        predicate: callable,
    ) -> List[int]:
        """Search for states matching a predicate.

        Args:
            predicate: A function that takes a state dict and returns bool.

        Returns:
            List of 1-indexed state numbers matching the predicate.

        Examples:
            >>> # Find states where s1 is Leader
            >>> reader.search_states(lambda s: s.get("state", {}).get("s1") == "Leader")
            [5, 6, 7]
        """
        matching = []
        for i, state in enumerate(self._states):
            # Create clean state without internal keys
            clean_state = {k: v for k, v in state.items() if not k.startswith('_')}
            if predicate(clean_state):
                matching.append(i + 1)
        return matching

    def format_state(
        self,
        index: Union[int, str],
        variables: Optional[List[str]] = None,
        max_depth: int = 4,
    ) -> str:
        """Format a state for display.

        Args:
            index: State index.
            variables: Optional list of variables to include.
            max_depth: Maximum nesting depth for formatting.

        Returns:
            Formatted string representation of the state.
        """
        state_info = self.get_state(index, variables)

        lines = [
            f"State {state_info.index}: <{state_info.action}>",
        ]

        if state_info.action_detail:
            lines.append(f"  Detail: {state_info.action_detail}")

        lines.append("")

        for var_name, var_value in sorted(state_info.variables.items()):
            formatted = format_value(var_value, max_depth=max_depth)
            # Indent multi-line values
            if '\n' in formatted:
                formatted = formatted.replace('\n', '\n    ')
            lines.append(f"  {var_name} = {formatted}")

        return '\n'.join(lines)

    def format_summary(self) -> str:
        """Format the trace summary for display.

        Returns:
            Formatted string with summary information.
        """
        summary = self.get_summary()

        lines = [
            "=" * 60,
            "TLC Trace Summary",
            "=" * 60,
            "",
        ]

        if summary.violation_name:
            lines.append(f"Violation Type: {summary.violation_type}")
            lines.append(f"Violated: {summary.violation_name}")
            lines.append("")

        lines.append(f"Trace Length: {summary.trace_length} states")
        lines.append("")

        if summary.statistics:
            lines.append("Statistics:")
            for key, value in summary.statistics.items():
                lines.append(f"  {key}: {value}")
            lines.append("")

        # Show action sequence (condensed)
        lines.append("Action Sequence:")
        action_counts = {}
        for action in summary.actions:
            action_counts[action] = action_counts.get(action, 0) + 1

        for i, action in enumerate(summary.actions[:10], 1):
            lines.append(f"  {i}. {action}")

        if len(summary.actions) > 10:
            lines.append(f"  ... ({len(summary.actions) - 10} more)")

        lines.append("")
        lines.append("Action Frequency:")
        for action, count in sorted(action_counts.items(), key=lambda x: -x[1]):
            lines.append(f"  {action}: {count}")

        lines.append("")
        lines.append("=" * 60)

        return '\n'.join(lines)

    def __repr__(self) -> str:
        """Return string representation."""
        return (
            f"TLCOutputReader(file='{self.file_path}', "
            f"states={len(self._states)}, "
            f"violation={self._metadata.get('violation_name', 'None')})"
        )
