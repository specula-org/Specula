"""TLA+ Spec Analyzer MCP Server."""

from mcp.server import Server
from mcp.server.stdio import stdio_server
from mcp import types

from .utils.logger import logger, setup_logging


class SpecAnalyzerMCPServer:
    """MCP Server for TLA+ Spec Analyzer.

    This server exposes TLA+ spec analysis capabilities as MCP tools.
    Currently supports:
    - VAV (Variable Assignment Validation): Check for missing/duplicate variable assignments
    """

    def __init__(self):
        """Initialize the MCP server."""
        # Initialize logging
        setup_logging()

        self.server = Server("tla-spec-analyzer")
        self.handlers = {}
        self._register_tools()

    def _register_tools(self):
        """Register all MCP tools."""
        from .handlers.vav_handler import VAVHandler

        # Initialize handlers
        self.handlers = {
            "run_vav_analysis": VAVHandler(),
        }

        # Register list_tools handler
        @self.server.list_tools()
        async def list_tools() -> list[types.Tool]:
            """List available tools."""
            return [
                types.Tool(
                    name="run_vav_analysis",
                    description=(
                        "Run Variable Assignment Validation (VAV) on a TLA+ spec. "
                        "Checks for two types of issues:\n"
                        "1. MISSING: A variable is not assigned in some branch of an action\n"
                        "2. DUPLICATE: A variable is assigned multiple times in the same execution path\n\n"
                        "Use this tool to validate that TLA+ actions correctly assign all state variables "
                        "exactly once in each branch. This helps catch common spec bugs where variables "
                        "are forgotten in some IF/CASE branches or accidentally assigned twice."
                    ),
                    inputSchema={
                        "type": "object",
                        "properties": {
                            "spec_file": {
                                "type": "string",
                                "description": "Path to TLA+ spec file (absolute path)"
                            },
                            "timeout": {
                                "type": "integer",
                                "description": "Timeout in seconds (default: 60)"
                            },
                            "debug": {
                                "type": "boolean",
                                "description": "Enable debug output (default: false)"
                            }
                        },
                        "required": ["spec_file"]
                    }
                )
            ]

        # Register call_tool handler
        @self.server.call_tool()
        async def call_tool(name: str, arguments: dict) -> list[types.TextContent]:
            """Handle tool calls."""
            logger.info(f"========== MCP TOOL CALLED: {name} ==========")
            logger.info(f"Arguments: {arguments}")

            # Force flush to ensure log is written immediately
            for handler in logger.handlers:
                handler.flush()

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

            logger.info(f"Handler returned result, length: {len(result)} chars")

            # Force flush before return
            for h in logger.handlers:
                h.flush()

            return [types.TextContent(type="text", text=result)]

    async def run(self):
        """Run the MCP server using stdio transport."""
        logger.info("Starting TLA+ Spec Analyzer MCP Server...")
        logger.info(f"Registered {len(self.handlers)} tools")

        async with stdio_server() as (read_stream, write_stream):
            await self.server.run(
                read_stream,
                write_stream,
                self.server.create_initialization_options()
            )
