"""Handler for validate_spec_syntax tool."""

import os
import subprocess
from typing import Dict, Any

from .base import BaseHandler
from ..utils.errors import ExecutionError


class SpecValidationHandler(BaseHandler):
    """Handler for validate_spec_syntax tool.

    This tool validates TLA+ spec syntax by running TLC in parse-only mode.
    It's faster than full trace validation and useful for quick syntax checks.
    """

    @property
    def tool_name(self) -> str:
        return "validate_spec_syntax"

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
                "work_dir": {
                    "type": "string",
                    "description": "Working directory (absolute path)"
                },
                "tla_jar": {
                    "type": "string",
                    "description": "Path to tla2tools.jar (optional)"
                }
            },
            "required": ["spec_file", "config_file", "work_dir"]
        }

    async def execute(self, arguments: Dict[str, Any]) -> Dict[str, Any]:
        """Validate TLA+ spec syntax.

        Args:
            arguments: Validated arguments

        Returns:
            Dict with validation result:
            - syntax_valid: Whether syntax is valid
            - output: TLC output
            - errors: List of error messages (if any)

        Raises:
            ExecutionError: If validation fails to run
        """
        spec_file = arguments["spec_file"]
        config_file = arguments["config_file"]
        work_dir = arguments["work_dir"]
        tla_jar = arguments.get("tla_jar")

        # Determine JAR path
        if not tla_jar:
            # Use default path (same logic as DebugSession)
            specula_root = os.environ.get('SPECULA_ROOT')
            if specula_root:
                tla_jar = os.path.join(specula_root, 'lib', 'tla2tools.jar')
            else:
                # Calculate relative to this file
                this_file = os.path.abspath(__file__)
                handlers_dir = os.path.dirname(this_file)
                tla_mcp_dir = os.path.dirname(handlers_dir)
                src_dir = os.path.dirname(tla_mcp_dir)
                tool_dir = os.path.dirname(src_dir)
                tools_dir = os.path.dirname(tool_dir)
                specula_root = os.path.dirname(tools_dir)
                tla_jar = os.path.join(specula_root, 'lib', 'tla2tools.jar')

        # Check if JAR exists
        if not os.path.exists(tla_jar):
            raise ExecutionError(
                f"TLA+ tools JAR not found: {tla_jar}",
                details={"tla_jar": tla_jar, "exists": False}
            )

        # Check if work_dir exists
        if not os.path.isdir(work_dir):
            raise ExecutionError(
                f"Working directory not found: {work_dir}",
                details={"work_dir": work_dir, "exists": False}
            )

        # Build TLC command for syntax check
        # Use -deadlock to avoid state exploration (just parse)
        cmd = [
            "java",
            "-cp", tla_jar,
            "tlc2.TLC",
            "-deadlock",  # Skip deadlock checking
            "-config", config_file,
            spec_file
        ]

        try:
            # Run TLC with short timeout (syntax check should be fast)
            result = subprocess.run(
                cmd,
                cwd=work_dir,
                capture_output=True,
                text=True,
                timeout=30  # 30 seconds should be enough for syntax check
            )

            output = result.stdout + result.stderr
            syntax_valid = result.returncode == 0

            # Extract error messages if validation failed
            errors = []
            if not syntax_valid:
                for line in output.split('\n'):
                    line = line.strip()
                    if 'Error:' in line or 'error' in line.lower():
                        errors.append(line)

            return {
                "syntax_valid": syntax_valid,
                "output": output,
                "errors": errors,
                "spec_file": spec_file,
                "config_file": config_file,
                "work_dir": work_dir
            }

        except subprocess.TimeoutExpired:
            raise ExecutionError(
                "Syntax validation timed out after 30 seconds",
                details={
                    "spec_file": spec_file,
                    "timeout": 30
                }
            )
        except FileNotFoundError:
            raise ExecutionError(
                "Java not found. Please ensure Java is installed and in PATH",
                details={"command": "java"}
            )
        except Exception as e:
            raise ExecutionError(
                f"Failed to run syntax validation: {e}",
                details={"error": str(e)}
            )
