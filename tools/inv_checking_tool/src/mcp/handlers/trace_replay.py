"""Handler for run_trace_replay tool."""

import os
from typing import Any, Dict

from .base import BaseHandler, ValidationError, ExecutionError
from ...trace_replay_tool import TraceReplayer, TraceFormat


class TraceReplayHandler(BaseHandler):
    """Handler for run_trace_replay tool.

    Replays a TLC trace using -loadTrace + -dumpTrace json.
    When ALIAS is defined in the config, the output will contain
    ALIAS-defined expressions instead of raw state variables.
    """

    @property
    def tool_name(self) -> str:
        return "run_trace_replay"

    async def execute(self, arguments: Dict[str, Any]) -> Dict[str, Any]:
        """Execute trace replay.

        Args:
            arguments: Must contain:
                - spec_file: TLA+ spec file name
                - trace_file: Input trace file path
                - work_dir: Working directory
              Optional:
                - config_file: Config file (can contain ALIAS)
                - output_file: Output JSON path (auto-generated if omitted)
                - trace_format: "json" (default) or "tlc"
                - tla_jar: Path to tla2tools.jar
                - community_jar: Path to CommunityModules-deps.jar
                - timeout: Timeout in seconds (default 300)
        """
        # Validate required arguments
        spec_file = arguments.get("spec_file")
        if not spec_file:
            raise ValidationError("Missing required argument: spec_file")

        trace_file = arguments.get("trace_file")
        if not trace_file:
            raise ValidationError("Missing required argument: trace_file")

        work_dir = arguments.get("work_dir")
        if not work_dir:
            raise ValidationError("Missing required argument: work_dir")

        # Optional arguments
        config_file = arguments.get("config_file")
        timeout = arguments.get("timeout", 300)
        tla_jar = arguments.get("tla_jar")
        community_jar = arguments.get("community_jar")

        # Determine trace format
        fmt_str = arguments.get("trace_format", "json")
        try:
            trace_format = TraceFormat(fmt_str)
        except ValueError:
            raise ValidationError(f"Invalid trace_format: {fmt_str}. Must be 'json' or 'tlc'.")

        # Determine output file path
        output_file = arguments.get("output_file")
        if not output_file:
            base = os.path.splitext(os.path.basename(spec_file))[0]
            output_file = os.path.join(work_dir, f"{base}_replay.json")

        try:
            replayer = TraceReplayer(tla_jar=tla_jar, community_jar=community_jar)
            tlc_output_path, json_output_path = await replayer.replay(
                spec_file=spec_file,
                trace_file=trace_file,
                work_dir=work_dir,
                output_file=output_file,
                config_file=config_file,
                trace_format=trace_format,
                timeout=timeout,
            )

            return {
                "output_file": tlc_output_path,
                "json_output_file": json_output_path,
                "message": (
                    f"Trace replay complete. "
                    f"Use get_tlc_summary/get_tlc_state/compare_tlc_states "
                    f"with file_path=\"{tlc_output_path}\" to analyze the result."
                ),
            }

        except RuntimeError as e:
            raise ExecutionError(str(e))
        except Exception as e:
            raise ExecutionError(f"Trace replay failed: {e}")
