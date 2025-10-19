"""
GBNF Grammar Tool

Provides the TLA+ token grammar content used during syntax fixing workflows.
"""

from pathlib import Path

from .base import BaseTool
from ..utils.config import get_config
from ..utils.result_types import ToolResult


class GBNFGrammarTool(BaseTool):
    """
    Return the configured GBNF grammar content.

    The tool inspects config.yaml for the `gbnf.minimized` flag to determine
    whether to return the minimized or cleaned grammar variant.
    """

    @property
    def name(self) -> str:
        return "read_gbnf"

    @property
    def description(self) -> str:
        return "Return the configured GBNF grammar content for token validation"

    def run(self, **kwargs) -> ToolResult:
        """
        Load the appropriate grammar file based on configuration.

        Returns:
            ToolResult: Grammar content or error details when loading fails.
        """
        if kwargs:
            return ToolResult(
                success=False,
                error="read_gbnf does not accept any arguments"
            )

        try:
            config = get_config()
        except Exception as exc:
            return ToolResult(
                success=False,
                error=f"Failed to load configuration: {exc}"
            )

        if not bool(config.get("gbnf.enabled", True)):
            return ToolResult(
                success=False,
                error="GBNF grammar tool disabled via configuration"
            )

        minimized = bool(config.get("gbnf.minimized", False))

        tools_dir = Path(__file__).resolve().parent
        grammar_dir = tools_dir / "data" / "gbnf"
        grammar_file = "token_minimized.gbnf" if minimized else "cleaned.gbnf"
        grammar_path = grammar_dir / grammar_file

        if not grammar_path.exists():
            return ToolResult(
                success=False,
                error=f"Grammar file not found: {grammar_path}"
            )

        try:
            content = grammar_path.read_text(encoding="utf-8")
        except Exception as exc:
            return ToolResult(
                success=False,
                error=f"Failed to read grammar file: {exc}"
            )

        return ToolResult(success=True, data=content)
