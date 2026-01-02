"""TLA+ Trace Validation Debugger.

This package provides a systematic debugging framework for TLA+ trace validation failures.
It supports agent-driven, layered debugging using breakpoint statistics and variable inspection.

Quick Start:
    >>> from trace_debugger import DebugSession, Breakpoint
    >>>
    >>> session = DebugSession(
    ...     spec_file="Traceetcdraft_progress.tla",
    ...     config_file="Traceetcdraft_progress.cfg",
    ...     trace_file="../traces/confchange_disable_validation.ndjson",
    ...     work_dir="/path/to/spec"
    ... )
    >>>
    >>> session.start()
    >>> session.set_breakpoints([
    ...     Breakpoint(line=522, condition='TLCGet("level") = 29', description="TraceNext entry"),
    ...     Breakpoint(line=489, condition='TLCGet("level") = 29', description="SendAppendEntriesRequest"),
    ... ])
    >>>
    >>> stats = session.run_until_done(timeout=120)
    >>> stats.print_summary()
    >>> session.close()

See Also:
    - docs/background.md: Background knowledge on TLA+ trace validation
    - docs/debugging_guide.md: Systematic debugging methodology
    - docs/TRACE_DEBUGGER_PLAN.md: Implementation design and rationale
    - examples/: Example debugging scripts
"""

import os
import sys

# Add parent directory to path for imports
_src_dir = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if _src_dir not in sys.path:
    sys.path.insert(0, _src_dir)

from debugger.breakpoint import Breakpoint, BreakpointHit, BreakpointStatistics
from debugger.session import DebugSession
from debugger.utils import collect_variable_values, check_conditions_at_breakpoint

__all__ = [
    # Core classes
    "DebugSession",

    # Breakpoint data structures
    "Breakpoint",
    "BreakpointHit",
    "BreakpointStatistics",

    # Utility functions
    "collect_variable_values",
    "check_conditions_at_breakpoint",
]

__version__ = "0.1.0"
