"""Debug session management for TLA+ trace validation."""

import os
import sys
import logging
from typing import List, Dict, Optional

# Add parent directory to path for imports
_src_dir = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if _src_dir not in sys.path:
    sys.path.insert(0, _src_dir)

from client.dap_client import DAPClient
from executor.tlc_process import TLCExecutor
from debugger.breakpoint import Breakpoint, BreakpointStatistics, BreakpointHit

logger = logging.getLogger(__name__)


class DebugSession:
    """Manages a TLA+ trace validation debugging session.

    This class provides a high-level interface for debugging TLA+ trace
    validation failures using the TLC debugger and DAP protocol.

    Example:
        >>> session = DebugSession(
        ...     spec_file="Traceetcdraft_progress.tla",
        ...     config_file="Traceetcdraft_progress.cfg",
        ...     trace_file="../traces/confchange_disable_validation.ndjson",
        ...     work_dir="/path/to/spec"
        ... )
        >>> session.start()
        >>> session.set_breakpoints([
        ...     Breakpoint(line=522, condition='TLCGet("level") = 29', description="TraceNext entry")
        ... ])
        >>> stats = session.run_until_done(timeout=120)
        >>> stats.print_summary()
        >>> session.close()
    """

    def __init__(self, spec_file: str, config_file: str, trace_file: str,
                 work_dir: str, tla_jar: Optional[str] = None,
                 community_jar: Optional[str] = None, port: int = 4712,
                 host: str = '127.0.0.1'):
        """Initialize debug session.

        Args:
            spec_file: TLA+ spec file name (e.g., "Traceetcdraft_progress.tla")
            config_file: TLC config file name
            trace_file: Path to trace file (relative to work_dir or absolute)
            work_dir: Working directory (absolute path)
            tla_jar: Path to tla2tools.jar (optional, uses default if None)
            community_jar: Path to CommunityModules-deps.jar (optional)
            port: DAP server port (default: 4712)
            host: DAP server host (default: '127.0.0.1')
        """
        self.spec_file = spec_file
        self.config_file = config_file
        self.trace_file = trace_file
        self.work_dir = os.path.abspath(work_dir)
        self.port = port
        self.host = host

        # Use default JAR paths if not provided
        # Try to find lib directory relative to this file or use environment variable
        if tla_jar is None or community_jar is None:
            # Try environment variable first
            specula_root = os.environ.get('SPECULA_ROOT')
            if specula_root:
                default_lib = os.path.join(specula_root, 'lib')
            else:
                # Calculate relative to this file: tools/trace_debugger/src/debugger/session.py
                # Go up to specula root: ../../../../lib
                this_file = os.path.abspath(__file__)
                debugger_src_dir = os.path.dirname(this_file)  # .../src/debugger
                src_dir = os.path.dirname(debugger_src_dir)     # .../src
                tool_dir = os.path.dirname(src_dir)             # .../trace_debugger
                tools_dir = os.path.dirname(tool_dir)           # .../tools
                specula_root = os.path.dirname(tools_dir)       # .../specula
                default_lib = os.path.join(specula_root, 'lib')

        self.tla_jar = tla_jar or os.path.join(default_lib, "tla2tools.jar")
        self.community_jar = community_jar or os.path.join(default_lib, "CommunityModules-deps.jar")

        # Initialize components
        self.executor = TLCExecutor(self.tla_jar, self.community_jar)
        self.client = DAPClient(host=host, port=port)

        # Session state
        self.is_running = False
        self.breakpoints: List[Breakpoint] = []
        self.breakpoint_hits: Dict[tuple, BreakpointHit] = {}  # (file, line) -> BreakpointHit

    def start(self) -> bool:
        """Start TLC debugger and establish connection.

        Returns:
            bool: True if successful, False otherwise
        """
        try:
            # Start TLC debugger process
            logger.info("Starting TLC debugger...")
            if not self.executor.start(
                spec_file=self.spec_file,
                config_file=self.config_file,
                trace_file=self.trace_file,
                cwd=self.work_dir,
                port=self.port
            ):
                logger.error("Failed to start TLC executor")
                return False

            # Connect DAP client
            logger.info("Connecting to debugger...")
            if not self.client.connect():
                logger.error("Failed to connect DAP client")
                self.executor.stop()
                return False

            # Initialize DAP session
            self.client.request("initialize", {"adapterID": "tlc"})
            self.is_running = True
            logger.info("Debug session started successfully")
            return True

        except Exception as e:
            logger.error(f"Error starting debug session: {e}")
            return False

    def set_breakpoints(self, breakpoints: List[Breakpoint]):
        """Set breakpoints.

        Args:
            breakpoints: List of breakpoints to set. Each breakpoint contains:
                - line: Line number
                - file: File name (optional, defaults to spec_file)
                - condition: Condition (optional, TLA+ expression)
                - description: Description (for reporting)
        """
        self.breakpoints = breakpoints

        # Group breakpoints by file
        breakpoints_by_file = {}
        for bp in breakpoints:
            file_name = bp.file if bp.file else self.spec_file
            if file_name not in breakpoints_by_file:
                breakpoints_by_file[file_name] = []
            breakpoints_by_file[file_name].append(bp)

        # Set breakpoints for each file
        for file_name, bps in breakpoints_by_file.items():
            file_path = os.path.join(self.work_dir, file_name)

            bp_list = []
            for bp in bps:
                bp_dict = {"line": bp.line}
                if bp.condition:
                    bp_dict["condition"] = bp.condition
                bp_list.append(bp_dict)

            # DEBUG: Log what we're sending
            logger.info(f"DEBUG: Setting breakpoints on file: {file_name}")
            logger.info(f"DEBUG: file_path: {file_path}")
            logger.info(f"DEBUG: breakpoints: {bp_list}")

            self.client.request("setBreakpoints", {
                "source": {"name": file_name, "path": file_path},
                "breakpoints": bp_list
            })

            # Initialize statistics tracking
            for bp in bps:
                key = (file_name, bp.line)
                self.breakpoint_hits[key] = BreakpointHit(
                    file=file_name,
                    line=bp.line,
                    description=bp.description,
                    hit_count=0
                )

        logger.info(f"Set {len(breakpoints)} breakpoint(s) across {len(breakpoints_by_file)} file(s)")

    def run_until_done(self, timeout: Optional[int] = None,
                       on_breakpoint_hit=None) -> BreakpointStatistics:
        """Run until termination or timeout.

        Args:
            timeout: Timeout in seconds (None = no timeout)
            on_breakpoint_hit: Optional callback when breakpoint is hit.
                Signature: on_breakpoint_hit(file_name, line, frame_id) -> None
                Called after updating statistics, before continuing execution.

        Returns:
            BreakpointStatistics: Collected statistics
        """
        # Start execution
        self.client.request("configurationDone", {})
        self.client.request("continue", {})

        total_hits = 0
        import time
        start_time = time.time()

        while True:
            # Check timeout
            if timeout and (time.time() - start_time) > timeout:
                logger.warning(f"Timeout reached after {timeout}s")
                break

            # Get next event
            event = self.client.get_event()
            if not event:
                time.sleep(0.01)
                continue

            event_type = event.get("event")

            # DEBUG: Log all events to understand what TLC sends
            logger.info(f"DEBUG: Received DAP event: {event_type}")
            if event_type not in ["stopped", "terminated"]:
                logger.info(f"DEBUG: Full event data: {event}")

            # Check for TLC completion in output events
            # TLC doesn't send "terminated" event, but sends "Finished in Xs at" message
            if event_type == "output":
                output_text = event.get("body", {}).get("output", "")
                # Look for final completion message (not intermediate "Finished checking")
                if "Finished in" in output_text and " at " in output_text:
                    logger.info(f"TLC execution finished (detected from output)")
                    # Give TLC a moment to send any remaining events
                    time.sleep(0.1)
                    break

            if event_type == "stopped":
                # Get stack frame to find which breakpoint was hit
                stack_resp = self.client.request("stackTrace", {"threadId": 0})
                if stack_resp and stack_resp.get("success"):
                    frames = stack_resp["body"].get("stackFrames", [])
                    if frames:
                        frame = frames[0]
                        frame_id = frame.get("id", 0)
                        file_name = frame.get("source", {}).get("name", self.spec_file)
                        line = frame.get("line")

                        logger.info(f"DEBUG: Stack frame: id={frame_id}, file={file_name}, line={line}")

                        # Update hit count (only for our breakpoints)
                        # Try exact match first, then with .tla extension
                        key = (file_name, line)
                        if key not in self.breakpoint_hits and not file_name.endswith('.tla'):
                            key = (file_name + '.tla', line)

                        if key in self.breakpoint_hits:
                            self.breakpoint_hits[key].hit_count += 1
                            total_hits += 1

                        # Call user callback if provided
                        if on_breakpoint_hit:
                            try:
                                on_breakpoint_hit(file_name, line, frame_id=frame_id)
                            except Exception as e:
                                logger.error(f"Error in breakpoint callback: {e}")

                # Always continue execution after stopped
                self.client.request("continue", {})

            elif event_type == "terminated":
                logger.info("TLC execution terminated")
                break

        # Build statistics
        stats = BreakpointStatistics(
            hits=list(self.breakpoint_hits.values()),
            total_hits=total_hits
        )

        return stats

    def evaluate_at_breakpoint(self, expression: str,
                               frame_id: int = 0) -> Optional[str]:
        """Evaluate expression at current breakpoint.

        Called when breakpoint is hit. Evaluates a TLA+ expression.

        Args:
            expression: TLA+ expression to evaluate
            frame_id: Stack frame ID (default 0 = top frame)

        Returns:
            str: Evaluation result, or None if failed
        """
        resp = self.client.request("evaluate", {
            "expression": expression,
            "frameId": frame_id,
            "context": "watch"
        })

        if resp and resp.get("success"):
            return resp["body"].get("result")
        return None

    def get_variables_at_breakpoint(self, var_names: List[str],
                                    frame_id: int = 0) -> Dict[str, str]:
        """Get variable values at current breakpoint.

        Supports:
        - Simple variables: "l", "pl"
        - Complex variables: "state" (returns string representation)
        - Field access: "data.log" (accesses record field)
        - Index access: "state[i]", "state[\"1\"]" (array/function indexing)

        Args:
            var_names: List of variable names or expressions
            frame_id: Stack frame ID

        Returns:
            Dict mapping variable names to values
        """
        result = {}

        # Separate simple variables from complex expressions
        simple_vars = []
        complex_exprs = []

        # Expressions contain: operators, function calls, field access, indexing
        expression_indicators = ['.', '[', '+', '-', '*', '/', '(', ')', '=', '<', '>', '\\']

        for var_name in var_names:
            # Check if it's a complex expression
            is_expr = any(char in var_name for char in expression_indicators)
            # Also check if it has spaces (likely an expression like "l + 1")
            is_expr = is_expr or ' ' in var_name

            if is_expr:
                complex_exprs.append(var_name)
            else:
                simple_vars.append(var_name)

        # Handle complex expressions using evaluate API
        if complex_exprs:
            logger.info(f"DEBUG: Evaluating complex expressions: {complex_exprs}")
            for expr in complex_exprs:
                value = self.evaluate_at_breakpoint(expr, frame_id)
                if value is not None:
                    result[expr] = value
                    logger.info(f"DEBUG: Evaluated '{expr}' = '{value}'")

        # Handle simple variables using variables API (with one level of nesting)
        if simple_vars:
            logger.info(f"DEBUG: Looking for simple variables: {simple_vars}")
            logger.info(f"DEBUG: Requesting scopes for frameId={frame_id}")

            scopes_resp = self.client.request("scopes", {"frameId": frame_id})

            if not scopes_resp or not scopes_resp.get("success"):
                logger.warning(f"DEBUG: Failed to get scopes or request unsuccessful")
                return result

            logger.info(f"DEBUG: Available scopes: {[s['name'] for s in scopes_resp['body']['scopes']]}")

            # Search through scopes for requested variables
            for scope in scopes_resp["body"]["scopes"]:
                scope_name = scope["name"]
                vref = scope["variablesReference"]
                logger.info(f"DEBUG: Checking scope '{scope_name}' (vref={vref})")

                if vref > 0:
                    vars_resp = self.client.request("variables", {
                        "variablesReference": vref
                    })
                    if vars_resp and vars_resp.get("success"):
                        variables = vars_resp["body"]["variables"]
                        logger.info(f"DEBUG: Scope '{scope_name}' has {len(variables)} variable(s) at first level")

                        for v in variables:
                            var_ref = v.get("variablesReference", 0)

                            # Only query containers (vref > 0), skip leaf nodes
                            if var_ref > 0:
                                logger.info(f"DEBUG:   Querying container '{v['name']}' (vref={var_ref})")
                                nested_resp = self.client.request("variables", {
                                    "variablesReference": var_ref
                                })

                                if nested_resp and nested_resp.get("success"):
                                    nested_vars = nested_resp["body"]["variables"]
                                    logger.info(f"DEBUG:   Container has {len(nested_vars)} nested variable(s)")

                                    for nested_v in nested_vars:
                                        nested_name = nested_v["name"]
                                        nested_value = nested_v.get("value", "")

                                        # Match against simple variable names
                                        if nested_name in simple_vars:
                                            result[nested_name] = nested_value
                                            logger.info(f"DEBUG:   ✓ Found '{nested_name}' = '{nested_value}'")

        logger.info(f"DEBUG: get_variables_at_breakpoint - Found {len(result)} variable(s): {list(result.keys())}")
        return result

    def step_over(self) -> Optional[Dict[str, str]]:
        """Execute next line (step over function calls).

        This executes the current TLA+ expression/statement and stops at the next line,
        without entering any action/function calls.

        Returns:
            Dict with current location after step:
            - file: File name
            - line: Line number (as string)
            - frame_id: Stack frame ID (as string)
            Returns None if timeout or error.

        Example:
            >>> location = session.step_over()
            >>> print(f"Now at {location['file']}:{location['line']}")
        """
        logger.info("Executing step over...")
        self.client.request("next", {"threadId": 0})
        location = self._wait_for_stop_event(timeout=10)
        if location:
            logger.info(f"Stepped to {location['file']}:{location['line']}")
        return location

    def step_into(self) -> Optional[Dict[str, str]]:
        """Step into action/function calls.

        In TLA+, this enters the definition of an action when it's called.
        For example, if the current line calls AppendEntries(i, j, range),
        this will step into the AppendEntries action definition.

        Returns:
            Dict with current location after step:
            - file: File name
            - line: Line number (as string)
            - frame_id: Stack frame ID (as string)
            Returns None if timeout or error.

        Example:
            >>> location = session.step_into()
            >>> print(f"Inside action at {location['file']}:{location['line']}")
        """
        logger.info("Executing step into...")
        self.client.request("stepIn", {"threadId": 0})
        location = self._wait_for_stop_event(timeout=10)
        if location:
            logger.info(f"Stepped into {location['file']}:{location['line']}")
        return location

    def step_out(self) -> Optional[Dict[str, str]]:
        """Step out of current action/function.

        Returns to the caller of the current action. Useful when you've stepped
        into an action and want to return to the calling context.

        Returns:
            Dict with current location after step:
            - file: File name
            - line: Line number (as string)
            - frame_id: Stack frame ID (as string)
            Returns None if timeout or error.

        Example:
            >>> location = session.step_out()
            >>> print(f"Back to caller at {location['file']}:{location['line']}")
        """
        logger.info("Executing step out...")
        self.client.request("stepOut", {"threadId": 0})
        location = self._wait_for_stop_event(timeout=10)
        if location:
            logger.info(f"Stepped out to {location['file']}:{location['line']}")
        return location

    def _wait_for_stop_event(self, timeout: int = 10) -> Optional[Dict[str, str]]:
        """Wait for stopped event and return current location.

        This is a helper method for step operations. After sending a step request
        (next, stepIn, stepOut), we need to wait for TLC to send a "stopped" event.

        Args:
            timeout: Timeout in seconds (default: 10)

        Returns:
            Dict with file, line, frame_id (all as strings), or None if timeout
        """
        import time
        start_time = time.time()

        while (time.time() - start_time) < timeout:
            event = self.client.get_event()
            if not event:
                time.sleep(0.01)
                continue

            event_type = event.get("event")

            # We're waiting for a "stopped" event
            if event_type == "stopped":
                reason = event.get("body", {}).get("reason", "")
                logger.info(f"Stopped event received (reason: {reason})")

                # Get current location from stack trace
                stack_resp = self.client.request("stackTrace", {"threadId": 0})
                if stack_resp and stack_resp.get("success"):
                    frames = stack_resp["body"].get("stackFrames", [])
                    if frames:
                        frame = frames[0]
                        return {
                            "file": frame.get("source", {}).get("name", ""),
                            "line": str(frame.get("line", 0)),
                            "frame_id": str(frame.get("id", 0))
                        }

            # If TLC terminates during stepping, return None
            elif event_type == "terminated":
                logger.warning("TLC terminated during step operation")
                return None

        logger.warning(f"Timeout waiting for stopped event after {timeout}s")
        return None

    def close(self):
        """Close connection and terminate TLC process."""
        try:
            if self.client.connected:
                self.client.request("disconnect", {})
                self.client.disconnect()
        except Exception as e:
            logger.warning(f"Error disconnecting client: {e}")

        try:
            self.executor.stop()
        except Exception as e:
            logger.warning(f"Error stopping executor: {e}")

        self.is_running = False
        logger.info("Debug session closed")
