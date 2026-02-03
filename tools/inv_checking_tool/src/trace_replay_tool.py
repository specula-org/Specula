"""Trace replay module using TLC's -loadTrace + -dumpTrace json.

This module provides a simple wrapper around TLC for replaying traces.
It runs TLC with -loadTrace to load an existing trace and -dumpTrace json
to output the result as JSON, which can then be parsed by
inv_checking_tool's TLCOutputReader.

Usage with ALIAS:
    ALIAS is a TLC config feature that customizes trace output. When defined,
    TLC replaces state variables with ALIAS-defined expressions in the output.
    This is useful for:
    - Filtering variables: show only a subset of state variables
    - Evaluating expressions: compute derived values at each state
    - Renaming variables: use different names in the output

    To use ALIAS with trace replay:
    1. Define an ALIAS operator in your TLA+ spec:
           MyAlias == [x |-> x, sum |-> x + y, valid |-> x > 0]
    2. Reference it in your config file (.cfg):
           ALIAS
           MyAlias
    3. Call TraceReplayer with that config file.

    The output JSON will contain ALIAS variables instead of spec variables.
    TLCOutputReader parses this correctly without any special handling.

Example:
    from tla_mcp.trace_replay import TraceReplayer

    replayer = TraceReplayer()
    output_path = await replayer.replay(
        spec_file="Spec.tla",
        trace_file="trace.json",
        config_file="Spec.cfg",   # may contain ALIAS
        work_dir="/path/to/spec",
        output_file="/tmp/output.json"
    )

    # Parse with existing TLCOutputReader
    from tlc_output_reader import TLCOutputReader
    reader = TLCOutputReader(output_path, mode="json")
"""

import asyncio
import os
from typing import Optional, List, Tuple
from enum import Enum


class TraceFormat(Enum):
    """Supported trace input formats."""
    TLC = "tlc"    # Binary .bin format
    JSON = "json"  # JSON format


class TraceReplayer:
    """TLC trace replay wrapper.

    Runs TLC with -loadTrace and -dumpTrace json to replay a trace
    and output the result as a JSON file for further processing.
    """

    def __init__(
        self,
        tla_jar: Optional[str] = None,
        community_jar: Optional[str] = None
    ):
        self.tla_jar, self.community_jar = self._resolve_jar_paths(tla_jar, community_jar)

    def _resolve_jar_paths(
        self,
        tla_jar: Optional[str],
        community_jar: Optional[str]
    ) -> Tuple[str, str]:
        """Resolve JAR paths, using defaults if not provided."""
        if tla_jar is None or community_jar is None:
            specula_root = os.environ.get('SPECULA_ROOT')
            if specula_root:
                default_lib = os.path.join(specula_root, 'lib')
            else:
                this_file = os.path.abspath(__file__)
                tla_mcp_dir = os.path.dirname(this_file)
                src_dir = os.path.dirname(tla_mcp_dir)
                tool_dir = os.path.dirname(src_dir)
                tools_dir = os.path.dirname(tool_dir)
                specula_root = os.path.dirname(tools_dir)
                default_lib = os.path.join(specula_root, 'lib')

            tla_jar = tla_jar or os.path.join(default_lib, "tla2tools.jar")
            community_jar = community_jar or os.path.join(default_lib, "CommunityModules-deps.jar")

        return tla_jar, community_jar

    def _build_command(
        self,
        spec_file: str,
        input_trace: str,
        output_trace: str,
        config_file: Optional[str],
        trace_format: TraceFormat,
        java_opts: Optional[List[str]] = None
    ) -> List[str]:
        """Build the TLC command for trace replay."""
        classpath = f"{self.tla_jar}:{self.community_jar}"

        cmd = ["java"]
        cmd.extend(java_opts or ["-XX:+UseParallelGC", "-Xmx4G"])
        cmd.extend(["-cp", classpath, "tlc2.TLC"])

        if config_file:
            cmd.extend(["-config", config_file])

        cmd.extend(["-loadTrace", trace_format.value, input_trace])
        cmd.extend(["-dumpTrace", "json", output_trace])

        cmd.append(spec_file)
        return cmd

    async def replay(
        self,
        spec_file: str,
        trace_file: str,
        work_dir: str,
        output_file: str,
        config_file: Optional[str] = None,
        trace_format: TraceFormat = TraceFormat.JSON,
        java_opts: Optional[List[str]] = None,
        timeout: int = 300
    ) -> str:
        """Replay a trace file and save the result as JSON.

        Args:
            spec_file: TLA+ spec file name (relative to work_dir)
            trace_file: Input trace file path
            work_dir: Working directory containing the spec
            output_file: Path for the output JSON file
            config_file: Optional config file (can contain ALIAS)
            trace_format: Format of input trace file
            java_opts: Additional JVM options
            timeout: Timeout in seconds

        Returns:
            Path to the output JSON file

        Raises:
            RuntimeError: If TLC fails or times out
        """
        cmd = self._build_command(
            spec_file=spec_file,
            input_trace=trace_file,
            output_trace=output_file,
            config_file=config_file,
            trace_format=trace_format,
            java_opts=java_opts
        )

        process = await asyncio.create_subprocess_exec(
            *cmd,
            cwd=work_dir,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.STDOUT
        )

        try:
            stdout, _ = await asyncio.wait_for(
                process.communicate(),
                timeout=timeout
            )
        except asyncio.TimeoutError:
            process.kill()
            raise RuntimeError(f"Trace replay timed out after {timeout}s")

        output = stdout.decode('utf-8', errors='replace')

        if process.returncode != 0 or not os.path.exists(output_file):
            raise RuntimeError(f"TLC trace replay failed (exit {process.returncode}):\n{output}")

        return output_file

    def replay_sync(self, **kwargs) -> str:
        """Synchronous version of replay."""
        return asyncio.run(self.replay(**kwargs))
