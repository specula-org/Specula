"""Handler for Variable Assignment Validation (VAV) tool."""

import os
import re
import subprocess
from typing import Dict, Any, List

from .base import BaseHandler
from ..utils.errors import ExecutionError
from ..utils.logger import logger


class VAVHandler(BaseHandler):
    """Handler for run_vav_analysis tool.

    This tool validates TLA+ specs for variable assignment issues:
    - MISSING: A variable is not assigned in some branch
    - DUPLICATE: A variable is assigned multiple times in the same path
    """

    @property
    def tool_name(self) -> str:
        return "run_vav_analysis"

    @property
    def argument_schema(self) -> Dict[str, Any]:
        return {
            "type": "object",
            "properties": {
                "spec_file": {
                    "type": "string",
                    "description": "Path to TLA+ spec file (absolute path)"
                },
                "timeout": {
                    "type": "integer",
                    "description": "Timeout in seconds (default: 60)",
                    "default": 60
                },
                "debug": {
                    "type": "boolean",
                    "description": "Enable debug output (default: false)",
                    "default": False
                }
            },
            "required": ["spec_file"]
        }

    async def execute(self, arguments: Dict[str, Any]) -> Dict[str, Any]:
        """Run VAV analysis on a TLA+ spec.

        Args:
            arguments: Validated arguments

        Returns:
            Dict with analysis result:
            - issues: List of issues found
            - issue_count: Total number of issues
            - summary: Human-readable summary
            - raw_output: Raw output from the tool

        Raises:
            ExecutionError: If analysis fails to run
        """
        spec_file = arguments["spec_file"]
        timeout = arguments.get("timeout", 60)
        debug = arguments.get("debug", False)

        # Validate spec file exists
        if not os.path.exists(spec_file):
            raise ExecutionError(
                f"Spec file not found: {spec_file}",
                details={"spec_file": spec_file, "exists": False}
            )

        # Find CFA jar
        cfa_jar = self._find_cfa_jar()
        if not cfa_jar:
            raise ExecutionError(
                "CFA tool JAR not found. Please ensure the CFA tool is built.",
                details={"searched_paths": self._get_search_paths()}
            )

        # Find TLA tools jar (needed for SANY parser)
        tla_jar = self._find_tla_jar()
        if not tla_jar:
            raise ExecutionError(
                "TLA+ tools JAR not found.",
                details={"searched_paths": self._get_tla_search_paths()}
            )

        # Build command
        # The CFA tool expects: input.tla output.tla --algorithm vav
        output_file = "/tmp/vav_output.tla"
        cmd = [
            "java",
            "-cp", f"{cfa_jar}:{tla_jar}",
            "CFG.SANYTransformerCli",
            spec_file,
            output_file,
            "--algorithm", "vav"
        ]

        if debug:
            cmd.append("--debug")

        logger.info(f"Running VAV analysis: {' '.join(cmd)}")

        try:
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=timeout
            )

            output = result.stdout + result.stderr
            logger.info(f"VAV output:\n{output}")

            # Parse the output to extract issues
            issues = self._parse_vav_output(output)

            return {
                "issues": issues,
                "issue_count": len(issues),
                "summary": self._generate_summary(issues),
                "raw_output": output,
                "spec_file": spec_file
            }

        except subprocess.TimeoutExpired:
            raise ExecutionError(
                f"VAV analysis timed out after {timeout} seconds",
                details={"spec_file": spec_file, "timeout": timeout}
            )
        except FileNotFoundError:
            raise ExecutionError(
                "Java not found. Please ensure Java is installed and in PATH",
                details={"command": "java"}
            )
        except Exception as e:
            raise ExecutionError(
                f"Failed to run VAV analysis: {e}",
                details={"error": str(e)}
            )

    def _find_cfa_jar(self) -> str:
        """Find the CFA tool JAR file."""
        for path in self._get_search_paths():
            if os.path.exists(path):
                return path
        return None

    def _get_search_paths(self) -> List[str]:
        """Get list of paths to search for CFA JAR."""
        specula_root = os.environ.get('SPECULA_ROOT')
        if not specula_root:
            # Calculate relative to this file
            this_file = os.path.abspath(__file__)
            handlers_dir = os.path.dirname(this_file)
            spec_mcp_dir = os.path.dirname(handlers_dir)
            src_dir = os.path.dirname(spec_mcp_dir)
            tool_dir = os.path.dirname(src_dir)
            tools_dir = os.path.dirname(tool_dir)
            specula_root = os.path.dirname(tools_dir)

        return [
            os.path.join(specula_root, 'tools', 'cfa', 'target',
                        'tlaplus-parser-1.0-SNAPSHOT-jar-with-dependencies.jar'),
            os.path.join(specula_root, 'tools', 'cfa', 'target',
                        'tlaplus-parser-1.0-SNAPSHOT.jar'),
        ]

    def _find_tla_jar(self) -> str:
        """Find the TLA+ tools JAR file."""
        for path in self._get_tla_search_paths():
            if os.path.exists(path):
                return path
        return None

    def _get_tla_search_paths(self) -> List[str]:
        """Get list of paths to search for TLA JAR."""
        specula_root = os.environ.get('SPECULA_ROOT')
        if not specula_root:
            this_file = os.path.abspath(__file__)
            handlers_dir = os.path.dirname(this_file)
            spec_mcp_dir = os.path.dirname(handlers_dir)
            src_dir = os.path.dirname(spec_mcp_dir)
            tool_dir = os.path.dirname(src_dir)
            tools_dir = os.path.dirname(tool_dir)
            specula_root = os.path.dirname(tools_dir)

        return [
            os.path.join(specula_root, 'lib', 'tla2tools.jar'),
        ]

    def _parse_vav_output(self, output: str) -> List[Dict[str, Any]]:
        """Parse VAV output to extract issues.

        Args:
            output: Raw output from VAV tool

        Returns:
            List of issue dictionaries
        """
        issues = []

        # Pattern for MISSING issues
        # [MISSING] FuncName branch N: Variables not assigned: [var1, var2]
        #   Path: ...
        missing_pattern = re.compile(
            r'\[MISSING\]\s+(\w+)(?:\s+branch\s+(\d+))?:\s*'
            r'(?:Variables not assigned|Branch missing variables):\s*\[([^\]]+)\]\s*'
            r'(?:\n\s*Path:\s*(.+))?',
            re.MULTILINE
        )

        for match in missing_pattern.finditer(output):
            func_name = match.group(1)
            branch = match.group(2)
            variables = [v.strip() for v in match.group(3).split(',')]
            path = match.group(4).strip() if match.group(4) else None

            issue = {
                "type": "MISSING",
                "function": func_name,
                "variables": variables,
                "message": f"Variables {variables} not assigned in {func_name}"
            }
            if branch:
                issue["branch"] = int(branch)
                issue["message"] = f"Variables {variables} not assigned in {func_name} branch {branch}"
            if path:
                issue["path"] = path

            issues.append(issue)

        # Pattern for DUPLICATE issues
        # [DUPLICATE] FuncName: Variable 'var' assigned multiple times
        #   First: ...
        #   Second: ...
        duplicate_pattern = re.compile(
            r'\[DUPLICATE\]\s+(\w+):\s*Variable\s+\'(\w+)\'\s+assigned multiple times\s*'
            r'(?:\n\s*First:\s*(.+))?\s*'
            r'(?:\n\s*Second:\s*(.+))?',
            re.MULTILINE
        )

        for match in duplicate_pattern.finditer(output):
            func_name = match.group(1)
            variable = match.group(2)
            first_loc = match.group(3).strip() if match.group(3) else None
            second_loc = match.group(4).strip() if match.group(4) else None

            issue = {
                "type": "DUPLICATE",
                "function": func_name,
                "variable": variable,
                "message": f"Variable '{variable}' assigned multiple times in {func_name}"
            }
            if first_loc:
                issue["first_assignment"] = first_loc
            if second_loc:
                issue["second_assignment"] = second_loc

            issues.append(issue)

        return issues

    def _generate_summary(self, issues: List[Dict[str, Any]]) -> str:
        """Generate a human-readable summary of issues.

        Args:
            issues: List of issues

        Returns:
            Summary string
        """
        if not issues:
            return "No variable assignment issues found. All variables are assigned exactly once in each branch."

        missing_count = sum(1 for i in issues if i["type"] == "MISSING")
        duplicate_count = sum(1 for i in issues if i["type"] == "DUPLICATE")

        parts = []
        if missing_count > 0:
            parts.append(f"{missing_count} MISSING variable(s)")
        if duplicate_count > 0:
            parts.append(f"{duplicate_count} DUPLICATE assignment(s)")

        summary = f"Found {len(issues)} issue(s): " + ", ".join(parts)

        # Add details about affected functions
        affected_funcs = set(i["function"] for i in issues)
        summary += f"\nAffected functions: {', '.join(sorted(affected_funcs))}"

        return summary
