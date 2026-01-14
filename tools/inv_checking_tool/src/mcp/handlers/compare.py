"""Handler for compare_tlc_states tool."""

from typing import Any, Dict, List, Optional, Union

from .base import BaseHandler, ValidationError, ExecutionError
from ...tlc_output_reader import TLCOutputReader


class CompareHandler(BaseHandler):
    """Handler for compare_tlc_states tool.

    This tool compares states and tracks variable changes. It supports:
    - Comparing two states to find differences
    - Tracking changes to a specific variable across the trace
    """

    @property
    def tool_name(self) -> str:
        return "compare_tlc_states"

    async def execute(self, arguments: Dict[str, Any]) -> Dict[str, Any]:
        """Execute the compare_tlc_states tool.

        Args:
            arguments: Must contain:
                - file_path: Path to TLC output file

            For comparison mode (compare two states):
                - index1: First state index
                - index2: Second state index

            For tracking mode (track variable changes):
                - track_variable: Variable name to track
                - track_path: (optional) Sub-path within the variable

        Returns:
            For comparison mode:
                - state1_index, state2_index: State numbers
                - state1_action, state2_action: Action names
                - changed_variables: List of variable names that changed
                - changes: Dict mapping variable name to {before, after}

            For tracking mode:
                - variable: Variable being tracked
                - total_changes: Number of changes found
                - changes: List of {from_state, to_state, action, before, after}
        """
        # Validate required arguments
        file_path = arguments.get("file_path")
        if not file_path:
            raise ValidationError("Missing required argument: file_path")

        index1 = arguments.get("index1")
        index2 = arguments.get("index2")
        track_variable = arguments.get("track_variable")

        # Determine mode
        if track_variable:
            return await self._track_variable(arguments)
        elif index1 is not None and index2 is not None:
            return await self._compare_states(arguments)
        else:
            raise ValidationError(
                "Must provide either:\n"
                "  - 'index1' and 'index2' to compare two states\n"
                "  - 'track_variable' to track variable changes"
            )

    async def _compare_states(self, arguments: Dict[str, Any]) -> Dict[str, Any]:
        """Compare two states."""
        file_path = arguments["file_path"]
        index1 = arguments["index1"]
        index2 = arguments["index2"]

        try:
            reader = TLCOutputReader(file_path)
            diff = reader.compare_states(index1, index2)

            return {
                "mode": "compare",
                "state1_index": diff["state1_index"],
                "state2_index": diff["state2_index"],
                "state1_action": diff["state1_action"],
                "state2_action": diff["state2_action"],
                "changed_variables": diff["changed_variables"],
                "num_changes": len(diff["changed_variables"]),
                "changes": diff["changes"],
            }

        except FileNotFoundError:
            raise
        except (IndexError, ValueError) as e:
            raise ExecutionError(f"Invalid index: {e}")
        except Exception as e:
            raise ExecutionError(f"Error comparing states: {e}")

    async def _track_variable(self, arguments: Dict[str, Any]) -> Dict[str, Any]:
        """Track changes to a variable."""
        file_path = arguments["file_path"]
        variable = arguments["track_variable"]
        path = arguments.get("track_path")

        try:
            reader = TLCOutputReader(file_path)
            changes = reader.find_variable_changes(variable, path)

            full_path = f"{variable}.{path}" if path else variable

            return {
                "mode": "track",
                "variable": full_path,
                "total_changes": len(changes),
                "changes": changes,
            }

        except FileNotFoundError:
            raise
        except Exception as e:
            raise ExecutionError(f"Error tracking variable: {e}")
