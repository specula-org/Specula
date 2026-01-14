"""Handler for get_tlc_state tool."""

from typing import Any, Dict, List, Optional, Union

from .base import BaseHandler, ValidationError, ExecutionError
from ...tlc_output_reader import TLCOutputReader
from ...utils.path_parser import PathAccessError


class StateHandler(BaseHandler):
    """Handler for get_tlc_state tool.

    This tool retrieves state information from a TLC trace. It supports:
    - Getting a single state by index
    - Getting multiple states by range
    - Filtering to specific variables
    - Querying nested values via path syntax
    """

    @property
    def tool_name(self) -> str:
        return "get_tlc_state"

    async def execute(self, arguments: Dict[str, Any]) -> Dict[str, Any]:
        """Execute the get_tlc_state tool.

        Args:
            arguments: Must contain:
                - file_path: Path to TLC output file
                - index: State index (1-indexed, negative, "first", "last")
                    OR
                - indices: Range string ("1:5", "-3:", "1,5,10") or list [1, 5, 10]

            Optional:
                - variables: List of variable names to include
                - path: Dot-separated path to query nested value (e.g., "log.s1.entries[0]")

        Returns:
            If querying single state:
                - index: State number
                - action: Action name
                - variables: State variables (filtered if specified)

            If querying path:
                - index: State number
                - path: The queried path
                - value: Value at the path

            If querying multiple states:
                - states: List of state objects
        """
        # Validate required arguments
        file_path = arguments.get("file_path")
        if not file_path:
            raise ValidationError("Missing required argument: file_path")

        index = arguments.get("index")
        indices = arguments.get("indices")
        variables = arguments.get("variables")
        path = arguments.get("path")

        if index is None and indices is None:
            raise ValidationError(
                "Must provide either 'index' (single state) or 'indices' (multiple states)"
            )

        try:
            reader = TLCOutputReader(file_path)

            # Case 1: Query path on a single state
            if path and index is not None:
                return self._query_path(reader, index, path)

            # Case 2: Get single state
            if index is not None:
                return self._get_single_state(reader, index, variables)

            # Case 3: Get multiple states
            return self._get_multiple_states(reader, indices, variables)

        except FileNotFoundError:
            raise
        except PathAccessError as e:
            raise ExecutionError(f"Path access error: {e}")
        except (IndexError, ValueError) as e:
            raise ExecutionError(f"Invalid index: {e}")
        except Exception as e:
            raise ExecutionError(f"Error reading state: {e}")

    def _query_path(
        self,
        reader: TLCOutputReader,
        index: Union[int, str],
        path: str
    ) -> Dict[str, Any]:
        """Query a nested value at a path."""
        value = reader.get_variable_at_path(index, path)
        state = reader.get_state(index)

        return {
            "index": state.index,
            "action": state.action,
            "path": path,
            "value": value,
        }

    def _get_single_state(
        self,
        reader: TLCOutputReader,
        index: Union[int, str],
        variables: Optional[List[str]]
    ) -> Dict[str, Any]:
        """Get a single state."""
        state = reader.get_state(index, variables)

        return {
            "index": state.index,
            "action": state.action,
            "action_detail": state.action_detail,
            "variables": state.variables,
        }

    def _get_multiple_states(
        self,
        reader: TLCOutputReader,
        indices: Union[str, List],
        variables: Optional[List[str]]
    ) -> Dict[str, Any]:
        """Get multiple states."""
        states = reader.get_states(indices, variables)

        return {
            "count": len(states),
            "states": [
                {
                    "index": s.index,
                    "action": s.action,
                    "variables": s.variables,
                }
                for s in states
            ],
        }
