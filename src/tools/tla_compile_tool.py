"""
TLA+ Compilation Check Tool

Checks if a TLA+ specification compiles without syntax errors.
Uses SANY (TLA+ parser) from tla2tools.jar.
"""

import subprocess
import time
from pathlib import Path
from typing import Dict, List, Tuple
from .base import BaseTool
from ..utils.result_types import ToolResult


class TLACompileTool(BaseTool):
    """
    Check if a TLA+ specification compiles without errors

    This tool validates TLA+ specs using SANY (the TLA+ parser).
    It checks for syntax errors and returns structured error information.

    Example:
        tool = TLACompileTool()
        result = tool.run(spec_path="/path/to/spec.tla")
        if result.success:
            print("Spec compiles successfully!")
        else:
            print(f"Found {result.data['error_count']} errors")
            for error in result.data['error_messages']:
                print(f"  - {error}")
    """

    def __init__(self, timeout: int = None):
        """
        Initialize TLA+ compilation checker

        Args:
            timeout: Timeout in seconds (defaults to config value)
        """
        # Load configuration
        from ..utils.config import get_config
        config = get_config()

        # Get TLA tools path from config
        tools_path = config.get('tla_validator.tools_path', 'lib/tla2tools.jar')

        # Convert to absolute path relative to project root
        project_root = Path(__file__).parent.parent.parent
        self.tla_tools_path = (project_root / tools_path).resolve()

        # Get timeout from config or use provided value
        self.timeout = timeout or config.get('tla_validator.timeout', 300)

        # Verify Java is available
        if not self._check_java_available():
            raise RuntimeError(
                "Java not found. TLA+ tools require Java to run. "
                "Please install Java and ensure it's in your PATH."
            )

        # Verify TLA tools exist
        if not self.tla_tools_path.exists():
            raise FileNotFoundError(
                f"TLA+ tools not found at {self.tla_tools_path}. "
                "Please ensure tla2tools.jar is in the correct location."
            )

    @property
    def name(self) -> str:
        return "tla_compile"

    @property
    def description(self) -> str:
        return """Check if a TLA+ specification compiles without syntax errors.

Args:
    spec_path: Path to .tla file

Returns:
    - success: True if compiles, False if syntax errors
    - data: Dict with error_count, error_messages, compilation_time
    - metadata: Additional compilation information

Use this tool to validate TLA+ specs and get detailed error information."""

    def run(self, spec_path: str) -> ToolResult:
        """
        Check if a TLA+ spec compiles

        Args:
            spec_path: Path to the .tla file to check

        Returns:
            ToolResult with compilation status and error details
        """
        # Convert to Path object
        path = Path(spec_path)

        # Validate input
        if not path.exists():
            return ToolResult(
                success=False,
                error=f"File not found: {spec_path}",
                suggestions=[
                    "Check if the file path is correct",
                    "Use an absolute path if needed"
                ]
            )

        if not path.is_file():
            return ToolResult(
                success=False,
                error=f"Path is not a file: {spec_path}",
                suggestions=[
                    "Ensure the path points to a file, not a directory"
                ]
            )

        if path.suffix != '.tla':
            return ToolResult(
                success=False,
                error=f"Not a TLA+ file (must have .tla extension): {spec_path}",
                suggestions=[
                    "Ensure the file has .tla extension"
                ]
            )

        # Run SANY validation
        start_time = time.time()
        success, output, returncode = self._run_sany(str(path.resolve()))
        compilation_time = time.time() - start_time

        # Parse errors from output
        # Don't try to be smart - just give LLM the full output
        if not success:
            error_messages = [output]  # Full output as single error message
            error_count = 1  # Count as 1 error (full compilation failure)
        else:
            error_messages = []
            error_count = 0

        # Build result
        if success:
            return ToolResult(
                success=True,
                data={
                    "error_count": 0,
                    "error_messages": [],
                    "compilation_time": compilation_time
                },
                suggestions=[
                    f"Specification compiled successfully in {compilation_time:.2f}s"
                ],
                metadata={
                    "spec_path": str(path.resolve()),
                    "compilation_time": compilation_time,
                    "returncode": returncode
                }
            )
        else:
            return ToolResult(
                success=False,
                data={
                    "error_count": error_count,
                    "error_messages": error_messages,
                    "compilation_time": compilation_time
                },
                error=f"Compilation failed with {error_count} error(s)",
                suggestions=[
                    f"Found {error_count} compilation error(s)",
                    "Review error messages to understand what needs to be fixed",
                    "Common issues: syntax errors, undefined symbols, type errors"
                ],
                metadata={
                    "spec_path": str(path.resolve()),
                    "compilation_time": compilation_time,
                    "returncode": returncode,
                    "full_output": output[:1000]  # First 1000 chars for debugging
                }
            )

    def _run_sany(self, file_path: str) -> Tuple[bool, str, int]:
        """
        Run SANY validation on a TLA+ file

        Args:
            file_path: Absolute path to .tla file

        Returns:
            Tuple of (success, output, returncode)
        """
        try:
            cmd = [
                "java",
                "-cp", str(self.tla_tools_path),
                "tla2sany.SANY",
                "-error-codes",
                file_path
            ]

            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=self.timeout
            )

            # Combine stdout and stderr
            output = result.stdout + result.stderr

            # SANY returns 0 on success, non-zero on errors
            # Check output for explicit success/error markers
            success = self._check_success(result.returncode, output)

            return success, output, result.returncode

        except subprocess.TimeoutExpired:
            error_msg = f"SANY validation timed out after {self.timeout} seconds"
            return False, error_msg, -1
        except Exception as e:
            error_msg = f"SANY validation failed: {str(e)}"
            return False, error_msg, -1

    def _check_success(self, returncode: int, output: str) -> bool:
        """
        Determine if compilation was successful

        Args:
            returncode: Process return code
            output: Combined stdout/stderr

        Returns:
            True if compilation succeeded, False otherwise
        """
        # Check for explicit error indicators
        error_indicators = [
            "Fatal errors",
            "*** Errors:",
            "Could not parse",
            "Parsing failed",
            "Semantic errors"
        ]

        for indicator in error_indicators:
            if indicator in output:
                return False

        # Check for success indicator
        # SANY typically prints "Semantic processing of module <name>" on success
        if "Semantic processing of module" in output:
            return True

        # Fallback: returncode 0 usually means success
        return returncode == 0

    def _extract_errors(self, output: str) -> List[str]:
        """
        Extract error messages from SANY output

        Args:
            output: SANY output text

        Returns:
            List of error messages
        """
        errors = []

        # SANY error format:
        # - Fatal errors are prefixed with "Fatal errors while parsing TLA+ spec"
        # - Individual errors often have line/column info
        # - Errors start with "***" or specific error codes

        lines = output.split('\n')

        # Strategy: Extract lines that look like errors
        in_error_section = False
        current_error = []

        for line in lines:
            stripped = line.strip()

            # Start of error section
            if any(marker in stripped for marker in ["Fatal errors", "*** Errors:", "Semantic errors"]):
                in_error_section = True
                continue

            # In error section, collect error lines
            if in_error_section:
                # Error lines typically start with specific patterns
                if stripped.startswith("***") or \
                   "line" in stripped.lower() and "column" in stripped.lower() or \
                   stripped.startswith("Unknown") or \
                   stripped.startswith("Could not parse") or \
                   stripped.startswith("Parsing failed"):
                    if current_error:
                        errors.append(" ".join(current_error))
                        current_error = []
                    current_error.append(stripped)
                elif stripped and not stripped.startswith("---"):
                    # Continuation of current error
                    if current_error:
                        current_error.append(stripped)
                elif not stripped:
                    # Empty line might end error
                    if current_error:
                        errors.append(" ".join(current_error))
                        current_error = []

        # Add last error if any
        if current_error:
            errors.append(" ".join(current_error))

        # If no structured errors found but output contains error indicators,
        # return the entire output as one error
        if not errors and any(indicator in output for indicator in ["Fatal errors", "*** Errors:", "Could not parse"]):
            # Try to extract just the relevant error portion
            error_start = output.find("Fatal errors")
            if error_start == -1:
                error_start = output.find("*** Errors:")
            if error_start == -1:
                error_start = output.find("Could not parse")

            if error_start != -1:
                # Get 500 chars from error start
                error_text = output[error_start:error_start+500].strip()
                errors.append(error_text)
            else:
                # Last resort: return first 300 chars of output
                errors.append(output[:300].strip())

        return errors

    def _check_java_available(self) -> bool:
        """Check if Java is available in PATH"""
        try:
            result = subprocess.run(
                ["java", "-version"],
                capture_output=True,
                timeout=5
            )
            return result.returncode == 0
        except (subprocess.SubprocessError, FileNotFoundError):
            return False


# Convenience function
def check_tla_compilation(spec_path: str, timeout: int = None) -> ToolResult:
    """
    Convenience function to check TLA+ spec compilation

    Args:
        spec_path: Path to .tla file
        timeout: Timeout in seconds

    Returns:
        ToolResult with compilation status
    """
    tool = TLACompileTool(timeout=timeout)
    return tool.run(spec_path=spec_path)
