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
        ...     Breakpoint(line=522, condition="l = 29", description="TraceNext entry")
        ... ])
        >>> stats = session.run_until_done(max_hits=50)
        >>> stats.print_summary()
        >>> session.close()
    """

    def __init__(self, spec_file: str, config_file: str, trace_file: str,
                 work_dir: str, tla_jar: Optional[str] = None,
                 community_jar: Optional[str] = None, port: int = 4712):
        """Initialize debug session.

        Args:
            spec_file: TLA+ spec file name (e.g., "Traceetcdraft_progress.tla")
            config_file: TLC config file name
            trace_file: Path to trace file (relative to work_dir or absolute)
            work_dir: Working directory (absolute path)
            tla_jar: Path to tla2tools.jar (optional, uses default if None)
            community_jar: Path to CommunityModules-deps.jar (optional)
            port: DAP server port (default: 4712)
        """
        self.spec_file = spec_file
        self.config_file = config_file
        self.trace_file = trace_file
        self.work_dir = os.path.abspath(work_dir)
        self.port = port

        # Use default JAR paths if not provided
        default_lib = "/home/ubuntu/specula/lib"
        self.tla_jar = tla_jar or os.path.join(default_lib, "tla2tools.jar")
        self.community_jar = community_jar or os.path.join(default_lib, "CommunityModules-deps.jar")

        # Initialize components
        self.executor = TLCExecutor(self.tla_jar, self.community_jar)
        self.client = DAPClient(port=port)

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

    def run_until_done(self, timeout: Optional[int] = None) -> BreakpointStatistics:
        """Run until termination or timeout.

        Args:
            timeout: Timeout in seconds (None = no timeout)

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

            if event_type == "stopped":
                # Get stack frame to find which breakpoint was hit
                stack_resp = self.client.request("stackTrace", {"threadId": 0})
                if stack_resp and stack_resp.get("success"):
                    frames = stack_resp["body"].get("stackFrames", [])
                    if frames:
                        frame = frames[0]
                        file_name = frame.get("source", {}).get("name", self.spec_file)
                        line = frame.get("line")

                        # Update hit count (only for our breakpoints)
                        # Try exact match first, then with .tla extension
                        key = (file_name, line)
                        if key not in self.breakpoint_hits and not file_name.endswith('.tla'):
                            key = (file_name + '.tla', line)

                        if key in self.breakpoint_hits:
                            self.breakpoint_hits[key].hit_count += 1
                            total_hits += 1

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

        Args:
            var_names: List of variable names
            frame_id: Stack frame ID

        Returns:
            Dict mapping variable names to values
        """
        result = {}

        # Get all scopes
        scopes_resp = self.client.request("scopes", {"frameId": frame_id})
        if not scopes_resp or not scopes_resp.get("success"):
            return result

        # Search through scopes for requested variables
        for scope in scopes_resp["body"]["scopes"]:
            vref = scope["variablesReference"]
            if vref > 0:
                vars_resp = self.client.request("variables", {
                    "variablesReference": vref
                })
                if vars_resp and vars_resp.get("success"):
                    for v in vars_resp["body"]["variables"]:
                        if v["name"] in var_names:
                            result[v["name"]] = v["value"]

        return result

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
