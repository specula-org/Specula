"""TLC Output Reader MCP Server."""

import logging
import sys

from mcp.server import Server
from mcp.server.stdio import stdio_server
from mcp import types

from .handlers import SummaryHandler, StateHandler, CompareHandler, TraceReplayHandler

# Setup logging
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
    stream=sys.stderr,
)
logger = logging.getLogger(__name__)


class TLCOutputReaderMCPServer:
    """MCP Server for TLC Output Reader.

    This server exposes 4 tools for analyzing TLC model checking output:
    1. get_tlc_summary - Get high-level overview of the trace
    2. get_tlc_state - Get specific states and variable values
    3. compare_tlc_states - Compare states and track variable changes
    4. run_trace_replay - Replay a trace with optional ALIAS to observe details
    """

    def __init__(self):
        """Initialize the MCP server."""
        self.server = Server("tlc-output-reader")
        self.handlers = {}
        self._register_tools()

    def _register_tools(self):
        """Register all MCP tools."""
        # Initialize handlers
        self.handlers = {
            "get_tlc_summary": SummaryHandler(),
            "get_tlc_state": StateHandler(),
            "compare_tlc_states": CompareHandler(),
            "run_trace_replay": TraceReplayHandler(),
        }

        # Register list_tools handler
        @self.server.list_tools()
        async def list_tools() -> list[types.Tool]:
            """List available tools."""
            return [
                types.Tool(
                    name="get_tlc_summary",
                    description=(
                        "Get a summary of TLC model checking results. "
                        "Use this FIRST to understand what invariant was violated and "
                        "get an overview of the error trace.\n\n"
                        "Returns:\n"
                        "- violation_name: The invariant/property that was violated\n"
                        "- trace_length: Number of states in the error trace\n"
                        "- actions: Sequence of actions leading to the violation\n"
                        "- action_frequency: Count of each action type\n"
                        "- statistics: TLC execution statistics\n"
                        "- variables: List of all state variables"
                    ),
                    inputSchema={
                        "type": "object",
                        "properties": {
                            "file_path": {
                                "type": "string",
                                "description": "Path to TLC output file (e.g., 'nohup.out' or simulation log)"
                            }
                        },
                        "required": ["file_path"]
                    }
                ),
                types.Tool(
                    name="get_tlc_state",
                    description=(
                        "Get state information from a TLC error trace. "
                        "Use this to inspect specific states and variable values.\n\n"
                        "Supports:\n"
                        "- Single state: index=1, index=-1 (last), index='last'\n"
                        "- Multiple states: indices='1:5', indices='-3:', indices=[1,5,10]\n"
                        "- Variable filtering: variables=['currentTerm', 'state']\n"
                        "- Nested path query: path='log.s1.entries[0].term'\n\n"
                        "Examples:\n"
                        "- Get last state: {index: -1}\n"
                        "- Get last 3 states: {indices: '-3:'}\n"
                        "- Get specific value: {index: 'last', path: 'currentTerm.s1'}"
                    ),
                    inputSchema={
                        "type": "object",
                        "properties": {
                            "file_path": {
                                "type": "string",
                                "description": "Path to TLC output file"
                            },
                            "index": {
                                "type": ["integer", "string"],
                                "description": "State index: positive (1-indexed), negative (-1=last), or 'first'/'last'"
                            },
                            "indices": {
                                "type": ["string", "array"],
                                "description": "Multiple states: range '1:5', '-3:', or list [1,5,10]"
                            },
                            "variables": {
                                "type": "array",
                                "items": {"type": "string"},
                                "description": "Filter to these variables only"
                            },
                            "path": {
                                "type": "string",
                                "description": "Dot-separated path for nested access: 'log.s1.entries[0]'"
                            }
                        },
                        "required": ["file_path"]
                    }
                ),
                types.Tool(
                    name="compare_tlc_states",
                    description=(
                        "Compare states or track variable changes in a TLC trace. "
                        "Use this to understand what changed between states.\n\n"
                        "Two modes:\n\n"
                        "1. Compare mode - Find differences between two states:\n"
                        "   {index1: -2, index2: -1} compares last two states\n"
                        "   Returns: changed_variables, before/after values\n\n"
                        "2. Track mode - Find all changes to a variable:\n"
                        "   {track_variable: 'currentTerm'}\n"
                        "   {track_variable: 'state', track_path: 's1'}\n"
                        "   Returns: list of all state transitions where variable changed"
                    ),
                    inputSchema={
                        "type": "object",
                        "properties": {
                            "file_path": {
                                "type": "string",
                                "description": "Path to TLC output file"
                            },
                            "index1": {
                                "type": ["integer", "string"],
                                "description": "First state index (for compare mode)"
                            },
                            "index2": {
                                "type": ["integer", "string"],
                                "description": "Second state index (for compare mode)"
                            },
                            "track_variable": {
                                "type": "string",
                                "description": "Variable name to track (for track mode)"
                            },
                            "track_path": {
                                "type": "string",
                                "description": "Sub-path within variable: 's1' for 'state.s1'"
                            }
                        },
                        "required": ["file_path"]
                    }
                ),
                types.Tool(
                    name="run_trace_replay",
                    description=(
                        "Replay a TLC trace using -loadTrace + -dumpTrace json. "
                        "Returns a JSON file that can be analyzed with "
                        "get_tlc_summary/get_tlc_state/compare_tlc_states.\n\n"
                        "Use this when you need to observe additional details from an "
                        "existing trace. Define an ALIAS operator in the spec to "
                        "filter variables, evaluate expressions, or rename variables "
                        "during replay. Reference the ALIAS in the config file.\n\n"
                        "Example workflow:\n"
                        "1. Define ALIAS in spec: MyAlias == [x |-> x, sum |-> x + y]\n"
                        "2. Add to config: ALIAS\\nMyAlias\n"
                        "3. Call run_trace_replay with that config\n"
                        "4. Use get_tlc_summary on the output to analyze results"
                    ),
                    inputSchema={
                        "type": "object",
                        "properties": {
                            "spec_file": {
                                "type": "string",
                                "description": "TLA+ spec file name (e.g., 'Spec.tla')"
                            },
                            "trace_file": {
                                "type": "string",
                                "description": "Input trace file path (relative to work_dir or absolute)"
                            },
                            "work_dir": {
                                "type": "string",
                                "description": "Working directory containing the spec"
                            },
                            "config_file": {
                                "type": "string",
                                "description": "Config file name (can contain ALIAS definition)"
                            },
                            "output_file": {
                                "type": "string",
                                "description": "Output JSON file path (auto-generated if omitted)"
                            },
                            "trace_format": {
                                "type": "string",
                                "description": "Input trace format: 'json' (default) or 'tlc'",
                                "enum": ["json", "tlc"]
                            },
                            "tla_jar": {
                                "type": "string",
                                "description": "Path to tla2tools.jar (optional)"
                            },
                            "community_jar": {
                                "type": "string",
                                "description": "Path to CommunityModules-deps.jar (optional)"
                            },
                            "timeout": {
                                "type": "integer",
                                "description": "Timeout in seconds (default: 300)"
                            }
                        },
                        "required": ["spec_file", "trace_file", "work_dir"]
                    }
                ),
            ]

        # Register call_tool handler
        @self.server.call_tool()
        async def call_tool(name: str, arguments: dict) -> list[types.TextContent]:
            """Handle tool calls."""
            logger.info(f"Tool called: {name}")

            if name not in self.handlers:
                error_msg = f"Unknown tool: {name}"
                logger.error(error_msg)
                return [types.TextContent(
                    type="text",
                    text=f'{{"success": false, "error": "{error_msg}"}}'
                )]

            handler = self.handlers[name]
            result = await handler.handle(arguments)

            return [types.TextContent(type="text", text=result)]

    async def run(self):
        """Run the MCP server using stdio transport."""
        logger.info("Starting TLC Output Reader MCP Server...")
        logger.info(f"Registered {len(self.handlers)} tools")

        async with stdio_server() as (read_stream, write_stream):
            await self.server.run(
                read_stream,
                write_stream,
                self.server.create_initialization_options()
            )
