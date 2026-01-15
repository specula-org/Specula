"""Handler for run_trace_validation_parallel tool."""

import asyncio
import os
import shutil
import tempfile
from typing import Dict, Any, List

from .trace_validation import TraceValidationHandler
from ..utils.errors import ExecutionError
from ..utils.logger import logger


class ParallelTraceValidationHandler(TraceValidationHandler):
    """Handler for run_trace_validation_parallel tool.

    Runs TLC trace validation for multiple traces concurrently and returns
    a concise summary.
    """

    @property
    def tool_name(self) -> str:
        return "run_trace_validation_parallel"

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
                "trace_files": {
                    "type": "array",
                    "description": "List of trace file paths (relative to work_dir or absolute)",
                    "items": {"type": "string"}
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
                }
            },
            "required": ["spec_file", "config_file", "trace_files", "work_dir"]
        }

    async def execute(self, arguments: Dict[str, Any]) -> Dict[str, Any]:
        """Execute trace validation for multiple traces in parallel."""
        trace_files = arguments["trace_files"]
        if not trace_files:
            raise ExecutionError(
                "No trace files provided",
                details={"trace_files": trace_files}
            )

        max_parallel = min(len(trace_files), os.cpu_count() or 1)
        semaphore = asyncio.Semaphore(max_parallel)

        logger.info(
            "Running TLC validation for %d trace(s) with parallelism=%d",
            len(trace_files),
            max_parallel
        )

        async def run_one(trace_file: str) -> Dict[str, Any]:
            async with semaphore:
                args = dict(arguments)
                args["trace_file"] = trace_file
                metadir = tempfile.mkdtemp(prefix="tlc_validation_")
                args["metadir"] = metadir

                try:
                    result = await TraceValidationHandler.execute(self, args)
                finally:
                    shutil.rmtree(metadir, ignore_errors=True)

                condensed = self._condense_result(result)
                condensed["trace_file"] = trace_file
                return condensed

        results = await asyncio.gather(
            *[run_one(trace_file) for trace_file in trace_files]
        )

        passed = sum(1 for result in results if result["status"] == "success")
        failed = len(results) - passed

        response = {
            "status": "success" if not failed else "trace_mismatch",
            "passed": passed,
            "failed": failed
        }

        if failed:
            response["failures"] = self._summarize_status(results)

        return response

    def _condense_result(self, result: Dict[str, Any]) -> Dict[str, Any]:
        condensed = {"status": result.get("status", "error")}
        suggestion = result.get("suggestion")
        if suggestion:
            condensed["suggestion"] = suggestion
        return condensed

    def _summarize_status(self, results: List[Dict[str, Any]]) -> Dict[str, str]:
        summary = {}
        for result in results:
            if result["status"] == "success":
                continue
            trace_file = os.path.basename(result["trace_file"])
            summary[trace_file] = result.get(
                "suggestion",
                "Trace validation failed. Run run_trace_validation on this trace for detailed output."
            )
        return summary
