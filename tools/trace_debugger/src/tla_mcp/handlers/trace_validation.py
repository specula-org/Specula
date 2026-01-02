"""Handler for run_trace_validation tool."""

import os
import sys
import time
from typing import Dict, Any, List

from .base import BaseHandler
from ..utils.errors import ExecutionError
from ..utils.logger import logger

# Add debugger to path
_src_dir = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
if _src_dir not in sys.path:
    sys.path.insert(0, _src_dir)

from debugger import DebugSession, Breakpoint


class TraceValidationHandler(BaseHandler):
    """Handler for run_trace_validation tool.

    This is the core tool for TLA+ trace debugging. It runs trace validation
    with breakpoints and collects statistics about which breakpoints were hit.

    Phase 2: Basic functionality (breakpoint statistics only)
    Phase 3: Will add evaluate and collect_variables features
    """

    @property
    def tool_name(self) -> str:
        return "run_trace_validation"

    @property
    def argument_schema(self) -> Dict[str, Any]:
        return {
            "type": "object",
            "properties": {
                "spec_file": {
                    "type": "string",
                    "description": "TLA+ spec file name"
                },
                "config_file": {
                    "type": "string",
                    "description": "TLC config file name"
                },
                "trace_file": {
                    "type": "string",
                    "description": "Trace file path (relative to work_dir or absolute)"
                },
                "work_dir": {
                    "type": "string",
                    "description": "Working directory (absolute path)"
                },
                "breakpoints": {
                    "type": "array",
                    "description": "List of breakpoints to set",
                    "items": {
                        "type": "object",
                        "properties": {
                            "line": {"type": "integer"},
                            "file": {"type": "string"},
                            "condition": {"type": "string"},
                            "description": {"type": "string"}
                        },
                        "required": ["line"]
                    }
                },
                "timeout": {
                    "type": "integer",
                    "default": 300,
                    "description": "Timeout in seconds"
                },
                "tla_jar": {
                    "type": "string",
                    "description": "Path to tla2tools.jar (optional)"
                },
                "community_jar": {
                    "type": "string",
                    "description": "Path to CommunityModules-deps.jar (optional)"
                },
                "host": {
                    "type": "string",
                    "default": "127.0.0.1",
                    "description": "DAP server host"
                },
                "port": {
                    "type": "integer",
                    "default": 4712,
                    "description": "DAP server port"
                },
                # Phase 3: evaluate and collect_variables will be added here
            },
            "required": ["spec_file", "config_file", "trace_file",
                        "work_dir", "breakpoints"]
        }

    async def execute(self, arguments: Dict[str, Any]) -> Dict[str, Any]:
        """Execute trace validation with breakpoints.

        Args:
            arguments: Validated arguments

        Returns:
            Dict with results:
            - statistics: Breakpoint statistics
            - execution_time: Time taken in seconds
            - evaluated_expressions: (if evaluate specified) List of evaluation results
            - collected_variables: (if collect_variables specified) List of variable samples

        Raises:
            ExecutionError: If validation fails
        """
        start_time = time.time()

        # 1. Create DebugSession
        logger.info(f"Creating DebugSession...")
        session = self._create_session(arguments)

        try:
            # 2. Start TLC debugger
            logger.info(f"Starting TLC debugger...")
            if not session.start():
                raise ExecutionError(
                    "Failed to start TLC debugger",
                    details={"spec_file": arguments["spec_file"]}
                )

            # 3. Set breakpoints
            breakpoints = self._parse_breakpoints(arguments["breakpoints"])
            logger.info(f"Setting {len(breakpoints)} breakpoint(s)...")
            session.set_breakpoints(breakpoints)

            # 4. Prepare callback for evaluate/collect_variables (Phase 3)
            evaluated_results = []
            collected_vars = []

            def normalize_filename(name: str) -> str:
                """Normalize filename by removing .tla extension if present.

                This allows flexible matching - users can specify filenames with
                or without .tla extension, and it will match correctly.
                """
                if not name:
                    return name
                return name.replace('.tla', '')

            def files_match(file1: str, file2: str) -> bool:
                """Check if two filenames match, ignoring .tla extension."""
                if file2 is None:
                    return True
                norm1 = normalize_filename(file1)
                norm2 = normalize_filename(file2)
                # Try exact match or endswith match (for cases like "etcdraft_progress" matching "Traceetcdraft_progress")
                return norm1 == norm2 or norm1.endswith(norm2) or norm2.endswith(norm1)

            def on_breakpoint_hit(file_name: str, line: int, frame_id: int):
                """Called when any breakpoint is hit."""
                # Handle evaluate
                if "evaluate" in arguments:
                    eval_config = arguments["evaluate"]
                    target_file = eval_config.get("breakpoint_file")
                    target_line = eval_config["breakpoint_line"]

                    # Check if this is the target breakpoint
                    if line == target_line and files_match(file_name, target_file):
                        logger.info(f"Evaluating expressions at {file_name}:{line}")
                        for expr in eval_config["expressions"]:
                            result = session.evaluate_at_breakpoint(expr, frame_id)
                            evaluated_results.append({
                                "expression": expr,
                                "result": result,
                                "file": file_name,
                                "line": line
                            })

                # Handle collect_variables
                if "collect_variables" in arguments:
                    collect_config = arguments["collect_variables"]
                    target_file = collect_config.get("breakpoint_file")
                    target_line = collect_config["breakpoint_line"]
                    max_samples = collect_config.get("max_samples", 10)

                    # Check if this is the target breakpoint and we haven't collected enough samples
                    if line == target_line and len(collected_vars) < max_samples and files_match(file_name, target_file):
                        logger.info(f"Collecting variables at {file_name}:{line} (sample {len(collected_vars)+1}/{max_samples})")
                        vars_dict = session.get_variables_at_breakpoint(
                            collect_config["variables"],
                            frame_id
                        )
                        collected_vars.append({
                            "sample_index": len(collected_vars),
                            "file": file_name,
                            "line": line,
                            "variables": vars_dict
                        })

            # 5. Run trace validation with callback
            timeout = arguments.get("timeout", 300)
            logger.info(f"Running trace validation (timeout: {timeout}s)...")

            # Only pass callback if evaluate or collect_variables is specified
            if "evaluate" in arguments or "collect_variables" in arguments:
                stats = session.run_until_done(timeout=timeout, on_breakpoint_hit=on_breakpoint_hit)
            else:
                stats = session.run_until_done(timeout=timeout)

            # 6. Build result
            execution_time = time.time() - start_time

            result = {
                "statistics": self._format_statistics(stats),
                "execution_time": execution_time
            }

            # Add Phase 3 results if available
            if evaluated_results:
                result["evaluated_expressions"] = evaluated_results
                logger.info(f"Evaluated {len(evaluated_results)} expression(s)")

            if collected_vars:
                result["collected_variables"] = collected_vars
                logger.info(f"Collected {len(collected_vars)} variable sample(s)")

            logger.info(f"Trace validation completed in {execution_time:.2f}s")
            logger.info(f"Total hits: {stats.total_hits}")

            return result

        finally:
            # Always close session
            logger.info("Closing debug session...")
            session.close()

    def _create_session(self, args: Dict[str, Any]) -> DebugSession:
        """Create DebugSession from arguments."""
        return DebugSession(
            spec_file=args["spec_file"],
            config_file=args["config_file"],
            trace_file=args["trace_file"],
            work_dir=args["work_dir"],
            tla_jar=args.get("tla_jar"),
            community_jar=args.get("community_jar"),
            host=args.get("host", "127.0.0.1"),
            port=args.get("port", 4712)
        )

    def _parse_breakpoints(self, bp_list: List[Dict]) -> List[Breakpoint]:
        """Parse breakpoint list from arguments."""
        breakpoints = []
        for bp in bp_list:
            breakpoints.append(Breakpoint(
                line=bp["line"],
                file=bp.get("file"),
                condition=bp.get("condition"),
                description=bp.get("description", f"Line {bp['line']}")
            ))
        return breakpoints

    def _format_statistics(self, stats) -> Dict[str, Any]:
        """Format BreakpointStatistics to dict."""
        return {
            "total_hits": stats.total_hits,
            "breakpoints": [
                {
                    "file": hit.file,
                    "line": hit.line,
                    "description": hit.description,
                    "hit_count": hit.hit_count,
                    "was_hit": hit.hit_count > 0
                }
                for hit in stats.hits
            ],
            "never_hit": [
                {
                    "file": hit.file,
                    "line": hit.line,
                    "description": hit.description
                }
                for hit in stats.get_never_hit()
            ]
        }
