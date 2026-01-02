"""Utility functions for advanced debugging scenarios."""

import os
import sys
import time
import logging
from typing import List, Dict, Any, Optional

# Add parent directory to path for imports
_src_dir = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if _src_dir not in sys.path:
    sys.path.insert(0, _src_dir)

from debugger.session import DebugSession
from debugger.breakpoint import Breakpoint

logger = logging.getLogger(__name__)


def collect_variable_values(
    session: DebugSession,
    breakpoint_line: int,
    condition: str,
    variables: List[str],
    max_samples: int = 10,
    breakpoint_file: Optional[str] = None
) -> List[Dict[str, Any]]:
    """Collect variable values across multiple breakpoint hits.

    This is useful for understanding why a condition fails by examining
    the actual values at that location across multiple executions.

    Args:
        session: Debug session (must be started but not yet running)
        breakpoint_line: Line number for breakpoint
        condition: Breakpoint condition (TLA+ expression)
        variables: List of variable names or expressions to collect
        max_samples: Maximum samples to collect
        breakpoint_file: File name (None = use session's spec_file)

    Returns:
        List of dicts, each containing variable values for one hit

    Example:
        >>> session = DebugSession(...)
        >>> session.start()
        >>> values = collect_variable_values(
        ...     session,
        ...     breakpoint_line=438,
        ...     condition='TLCGet("level") = 29',
        ...     variables=["i", "j", "GetConfig(i)"],
        ...     max_samples=10
        ... )
        >>> for v in values:
        ...     print(f"i={v['i']}, j={v['j']}, GetConfig(i)={v['GetConfig(i)']}")
        >>> session.close()
    """
    samples = []

    # Set the breakpoint
    bp = Breakpoint(
        line=breakpoint_line,
        file=breakpoint_file,
        condition=condition,
        description=f"Collecting variables: {', '.join(variables)}"
    )
    session.set_breakpoints([bp])

    # Start execution
    session.client.request("configurationDone", {})
    session.client.request("continue", {})

    while len(samples) < max_samples:
        event = session.client.get_event()
        if not event:
            time.sleep(0.01)
            continue

        event_type = event.get("event")

        if event_type == "stopped":
            reason = event.get("body", {}).get("reason", "")

            if reason == "breakpoint":
                # Get stack frame
                stack_resp = session.client.request("stackTrace", {"threadId": 0})
                if not stack_resp or not stack_resp.get("success"):
                    session.client.request("continue", {})
                    continue

                frames = stack_resp["body"].get("stackFrames", [])
                if not frames:
                    session.client.request("continue", {})
                    continue

                frame_id = frames[0]["id"]

                # Collect variable values
                sample = {}
                for var in variables:
                    # Try to get as variable first
                    var_values = session.get_variables_at_breakpoint([var], frame_id)
                    if var in var_values:
                        sample[var] = var_values[var]
                    else:
                        # Try to evaluate as expression
                        result = session.evaluate_at_breakpoint(var, frame_id)
                        sample[var] = result if result else "N/A"

                samples.append(sample)
                logger.info(f"Collected sample {len(samples)}/{max_samples}")

                # Continue to next hit
                session.client.request("continue", {})

        elif event_type == "terminated":
            logger.info(f"TLC terminated after collecting {len(samples)} samples")
            break

    return samples


def check_conditions_at_breakpoint(
    session: DebugSession,
    conditions: Dict[str, str]
) -> Dict[str, Any]:
    """Check multiple conditions at current breakpoint.

    This assumes the debugger is already stopped at a breakpoint.
    Useful for inspecting why certain conditions fail.

    Args:
        session: Debug session (must be at a stopped state)
        conditions: Dictionary mapping description to TLA+ expression
                   Example: {"i != j": "i /= j", "Leader check": "state[i] = Leader"}

    Returns:
        Dictionary mapping description to evaluation result

    Example:
        >>> # Assume we're stopped at a breakpoint
        >>> results = check_conditions_at_breakpoint(session, {
        ...     "i != j": "i /= j",
        ...     "range valid": "range[1] <= range[2]",
        ...     "is leader": "state[i] = Leader"
        ... })
        >>> for desc, result in results.items():
        ...     print(f"{desc}: {result}")
    """
    # Get current stack frame
    stack_resp = session.client.request("stackTrace", {"threadId": 0})
    if not stack_resp or not stack_resp.get("success"):
        logger.error("Failed to get stack trace")
        return {}

    frames = stack_resp["body"].get("stackFrames", [])
    if not frames:
        logger.error("No stack frames available")
        return {}

    frame_id = frames[0]["id"]

    # Evaluate each condition
    results = {}
    for description, expression in conditions.items():
        result = session.evaluate_at_breakpoint(expression, frame_id)
        results[description] = result

    return results
