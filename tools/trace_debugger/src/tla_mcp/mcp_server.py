"""TLA+ Trace Debugger MCP Server."""

from mcp.server import Server
from mcp.server.stdio import stdio_server
from mcp import types

from .utils.logger import logger


class TLADebuggerMCPServer:
    """MCP Server for TLA+ Trace Debugger.

    This server exposes TLA+ trace debugging capabilities as MCP tools.
    Tools are registered dynamically and handlers are imported lazily
    to avoid circular dependencies.
    """

    def __init__(self):
        """Initialize the MCP server."""
        self.server = Server("tla-trace-debugger")
        self.handlers = {}
        self._register_tools()

    def _register_tools(self):
        """Register all MCP tools.

        Tools are registered using decorators. Handlers are imported
        lazily when needed to avoid import-time dependencies.
        """
        from .handlers.trace_validation import TraceValidationHandler
        from .handlers.trace_info import TraceInfoHandler
        from .handlers.spec_validation import SpecValidationHandler

        # Initialize handlers
        self.handlers = {
            "run_trace_validation": TraceValidationHandler(),
            "get_trace_info": TraceInfoHandler(),
            "validate_spec_syntax": SpecValidationHandler(),
        }

        # Register list_tools handler
        @self.server.list_tools()
        async def list_tools() -> list[types.Tool]:
            """List available tools."""
            return [
                types.Tool(
                    name="run_trace_validation",
                    description=(
                        "Run TLC trace validation with breakpoints and collect statistics. "
                        "Supports optional expression evaluation and variable collection at breakpoints. "
                        "\n\nBasic usage: Set breakpoints and get hit counts to localize issues. "
                        "\n\nAdvanced: Add 'evaluate' to evaluate TLA+ expressions, or 'collect_variables' "
                        "to collect variable values at specific breakpoints."
                    ),
                    inputSchema={
                        "type": "object",
                        "properties": {
                            "spec_file": {
                                "type": "string",
                                "description": "TLA+ spec file name (e.g., 'Raft.tla')"
                            },
                            "config_file": {
                                "type": "string",
                                "description": "TLC config file name (e.g., 'Raft.cfg')"
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
                            "host": {
                                "type": "string",
                                "description": "DAP server host (default: 127.0.0.1)"
                            },
                            "port": {
                                "type": "integer",
                                "description": "DAP server port (default: 4712)"
                            },
                            "evaluate": {
                                "type": "object",
                                "description": "Optional: Evaluate expressions at a breakpoint",
                                "properties": {
                                    "breakpoint_line": {"type": "integer"},
                                    "breakpoint_file": {"type": "string"},
                                    "expressions": {
                                        "type": "array",
                                        "items": {"type": "string"}
                                    }
                                },
                                "required": ["breakpoint_line", "expressions"]
                            },
                            "collect_variables": {
                                "type": "object",
                                "description": "Optional: Collect variable values at a breakpoint",
                                "properties": {
                                    "breakpoint_line": {"type": "integer"},
                                    "breakpoint_file": {"type": "string"},
                                    "variables": {
                                        "type": "array",
                                        "items": {"type": "string"}
                                    },
                                    "max_samples": {"type": "integer"}
                                },
                                "required": ["breakpoint_line", "variables"]
                            }
                        },
                        "required": ["spec_file", "config_file", "trace_file", "work_dir", "breakpoints"]
                    }
                ),
                types.Tool(
                    name="get_trace_info",
                    description="Get basic information about a trace file (line count, size, sample lines)",
                    inputSchema={
                        "type": "object",
                        "properties": {
                            "trace_file": {
                                "type": "string",
                                "description": "Path to trace file"
                            }
                        },
                        "required": ["trace_file"]
                    }
                ),
                types.Tool(
                    name="validate_spec_syntax",
                    description="Validate TLA+ spec syntax without running trace validation (quick syntax check)",
                    inputSchema={
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
                                "description": "Working directory"
                            },
                            "tla_jar": {
                                "type": "string",
                                "description": "Path to tla2tools.jar (optional)"
                            }
                        },
                        "required": ["spec_file", "config_file", "work_dir"]
                    }
                )
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

            # Call the handler
            handler = self.handlers[name]
            result = await handler.handle(arguments)

            return [types.TextContent(type="text", text=result)]

    async def run(self):
        """Run the MCP server using stdio transport."""
        logger.info("Starting TLA+ Trace Debugger MCP Server...")
        logger.info(f"Registered {len(self.handlers)} tools")

        async with stdio_server() as (read_stream, write_stream):
            await self.server.run(
                read_stream,
                write_stream,
                self.server.create_initialization_options()
            )
