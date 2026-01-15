"""Handler for run_trace_validation tool.

This tool runs TLC directly (without debugger mode) for simple trace validation.
It provides concise feedback suitable for AI agents.
"""

import asyncio
import os
import re
import subprocess
from typing import Dict, Any, Optional, Tuple

from .base import BaseHandler
from ..utils.errors import ExecutionError
from ..utils.logger import logger


class TraceValidationHandler(BaseHandler):
    """Handler for run_trace_validation tool.

    Runs TLC trace validation directly and provides concise, actionable feedback.
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
                    "description": "TLA+ spec file name (e.g., 'Traceetcdraft.tla')"
                },
                "config_file": {
                    "type": "string",
                    "description": "TLC config file name (e.g., 'Traceetcdraft.cfg')"
                },
                "trace_file": {
                    "type": "string",
                    "description": "Trace file path (relative to work_dir or absolute)"
                },
                "work_dir": {
                    "type": "string",
                    "description": "Working directory (absolute path)"
                },
                "timeout": {
                    "type": "integer",
                    "default": 300,
                    "description": "Timeout in seconds (default: 300)"
                },
                "tla_jar": {
                    "type": "string",
                    "description": "Path to tla2tools.jar (optional)"
                },
                "community_jar": {
                    "type": "string",
                    "description": "Path to CommunityModules-deps.jar (optional)"
                },
                "include_last_state": {
                    "type": "boolean",
                    "default": False,
                    "description": "Include full content of the last matched state (default: false). This state is rarely useful for debugging since it's the last SUCCESSFUL match before failure."
                }
            },
            "required": ["spec_file", "config_file", "trace_file", "work_dir"]
        }

    async def execute(self, arguments: Dict[str, Any]) -> Dict[str, Any]:
        """Execute trace validation.

        Returns:
            Dict with validation result:
            - status: "success" | "trace_mismatch" | "error"
            - For trace_mismatch:
              - last_state_number: The last state number in counterexample
              - failed_trace_line: The l value (trace line that failed)
              - last_state: Content of the last state
              - suggestion: Debugging suggestion
            - For error:
              - raw_output: Full TLC output
        """
        # Get JAR paths
        tla_jar, community_jar = self._get_jar_paths(arguments)

        # Build command
        cmd = self._build_command(arguments, tla_jar, community_jar)

        # Run TLC
        logger.info(f"Running TLC: {' '.join(cmd)}")
        output = await self._run_tlc(cmd, arguments)

        # Parse output
        include_last_state = arguments.get("include_last_state", False)
        return self._parse_output(output, include_last_state)

    def _get_jar_paths(self, args: Dict[str, Any]) -> Tuple[str, str]:
        """Get TLA+ JAR paths."""
        tla_jar = args.get("tla_jar")
        community_jar = args.get("community_jar")

        if tla_jar is None or community_jar is None:
            specula_root = os.environ.get('SPECULA_ROOT')
            if specula_root:
                default_lib = os.path.join(specula_root, 'lib')
            else:
                # Calculate relative to this file
                this_file = os.path.abspath(__file__)
                handlers_dir = os.path.dirname(this_file)
                tla_mcp_dir = os.path.dirname(handlers_dir)
                src_dir = os.path.dirname(tla_mcp_dir)
                tool_dir = os.path.dirname(src_dir)
                tools_dir = os.path.dirname(tool_dir)
                specula_root = os.path.dirname(tools_dir)
                default_lib = os.path.join(specula_root, 'lib')

            tla_jar = tla_jar or os.path.join(default_lib, "tla2tools.jar")
            community_jar = community_jar or os.path.join(default_lib, "CommunityModules-deps.jar")

        return tla_jar, community_jar

    def _build_command(self, args: Dict[str, Any], tla_jar: str, community_jar: str) -> list:
        """Build TLC command."""
        classpath = f"{tla_jar}:{community_jar}"
        metadir = args.get("metadir", "/tmp/tlc_validation")
        return [
            "java", "-XX:+UseParallelGC", "-Xmx4G",
            "-cp", classpath,
            "tlc2.TLC",
            "-config", args["config_file"],
            args["spec_file"],
            "-lncheck", "final",
            "-metadir", metadir,
            "-fpmem", "0.9"
        ]

    async def _run_tlc(self, cmd: list, args: Dict[str, Any]) -> str:
        """Run TLC and return output."""
        env = os.environ.copy()
        env["JSON"] = args["trace_file"]

        timeout = args.get("timeout", 300)

        try:
            process = await asyncio.create_subprocess_exec(
                *cmd,
                cwd=args["work_dir"],
                stdout=asyncio.subprocess.PIPE,
                stderr=asyncio.subprocess.STDOUT,
                env=env
            )

            stdout, _ = await asyncio.wait_for(
                process.communicate(),
                timeout=timeout
            )

            return stdout.decode('utf-8', errors='replace')

        except asyncio.TimeoutError:
            process.kill()
            raise ExecutionError(
                f"TLC timed out after {timeout} seconds",
                details={"timeout": timeout}
            )
        except Exception as e:
            raise ExecutionError(
                f"Failed to run TLC: {e}",
                details={"command": ' '.join(cmd)}
            )

    def _parse_output(self, output: str, include_last_state: bool = False) -> Dict[str, Any]:
        """Parse TLC output and return structured result."""
        # Check for success
        if "Model checking completed. No error has been found." in output:
            # Extract states generated
            states_match = re.search(r'(\d+) states generated', output)
            states = int(states_match.group(1)) if states_match else 0

            return {
                "status": "success",
                "states_generated": states,
                "message": "Trace validation passed"
            }

        # Check for temporal property violation (trace mismatch)
        if "Error: Temporal properties were violated." in output:
            return self._parse_trace_mismatch(output, include_last_state)

        # Other error - return raw output
        return {
            "status": "error",
            "message": "TLC reported an error",
            "raw_output": output
        }

    def _parse_trace_mismatch(self, output: str, include_last_state: bool = False) -> Dict[str, Any]:
        """Parse trace mismatch output."""
        # Find all states with their l values
        # Pattern: "State N: <...>" followed by "/\ l = M"
        state_pattern = re.compile(r'State (\d+):.*?/\\ l = (\d+)', re.DOTALL)
        states = state_pattern.findall(output)

        if not states:
            return {
                "status": "trace_mismatch",
                "message": "Trace validation failed but could not parse state info",
                "raw_output": output
            }

        # Get last state info
        last_state_number = int(states[-1][0])
        failed_trace_line = int(states[-1][1])

        # Extract states generated
        states_match = re.search(r'(\d+) states generated', output)
        states_generated = int(states_match.group(1)) if states_match else last_state_number

        result = {
            "status": "trace_mismatch",
            "last_state_number": last_state_number,
            "failed_trace_line": failed_trace_line,
            "states_generated": states_generated,
            "suggestion": (
                f"Trace validation failed at trace line {failed_trace_line}. "
                f"Use run_trace_debugging with breakpoint condition "
                f"'TLCGet(\"level\") = {last_state_number}' to debug."
            )
        }

        # Only include last_state if explicitly requested
        if include_last_state:
            result["last_state"] = self._extract_last_state(output, last_state_number)

        return result

    def _extract_last_state(self, output: str, state_number: int) -> str:
        """Extract the content of the last state."""
        # Find the start of the last state
        pattern = f"State {state_number}:"
        start_idx = output.rfind(pattern)
        if start_idx == -1:
            return ""

        # Find the end (next State or stats line)
        end_patterns = [
            f"\nState {state_number + 1}:",
            f"\n{state_number} states generated",
            "\nFinished in"
        ]

        end_idx = len(output)
        for end_pattern in end_patterns:
            idx = output.find(end_pattern, start_idx)
            if idx != -1 and idx < end_idx:
                end_idx = idx

        # Also look for any number of "N states generated"
        stats_match = re.search(r'\n\d+ states generated', output[start_idx:])
        if stats_match:
            idx = start_idx + stats_match.start()
            if idx < end_idx:
                end_idx = idx

        return output[start_idx:end_idx].strip()
