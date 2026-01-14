"""Handler for get_tlc_summary tool."""

from typing import Any, Dict

from .base import BaseHandler, ValidationError, ExecutionError
from ...tlc_output_reader import TLCOutputReader


class SummaryHandler(BaseHandler):
    """Handler for get_tlc_summary tool.

    This tool provides a high-level overview of TLC model checking results,
    including the violated invariant, trace length, action sequence, and
    execution statistics.
    """

    @property
    def tool_name(self) -> str:
        return "get_tlc_summary"

    async def execute(self, arguments: Dict[str, Any]) -> Dict[str, Any]:
        """Execute the get_tlc_summary tool.

        Args:
            arguments: Must contain:
                - file_path: Path to TLC output file

        Returns:
            Summary information including:
            - violation_type: "invariant" or "property"
            - violation_name: Name of violated invariant/property
            - trace_length: Number of states in the trace
            - actions: List of action names in order
            - action_frequency: Count of each action type
            - statistics: TLC execution statistics
        """
        # Validate required arguments
        file_path = arguments.get("file_path")
        if not file_path:
            raise ValidationError("Missing required argument: file_path")

        try:
            reader = TLCOutputReader(file_path)
            summary = reader.get_summary()

            # Calculate action frequency
            action_freq = {}
            for action in summary.actions:
                action_freq[action] = action_freq.get(action, 0) + 1

            return {
                "violation_type": summary.violation_type,
                "violation_name": summary.violation_name,
                "trace_length": summary.trace_length,
                "actions": summary.actions,
                "action_frequency": action_freq,
                "statistics": summary.statistics,
                "variables": reader.get_all_variables(),
            }

        except FileNotFoundError:
            raise
        except ValueError as e:
            raise ExecutionError(f"Failed to parse TLC output: {e}")
        except Exception as e:
            raise ExecutionError(f"Error reading TLC output: {e}")
