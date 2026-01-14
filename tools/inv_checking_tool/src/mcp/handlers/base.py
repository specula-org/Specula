"""Base handler for MCP tools."""

import json
import logging
import traceback
from abc import ABC, abstractmethod
from typing import Any, Dict

logger = logging.getLogger(__name__)


class HandlerError(Exception):
    """Base error for handler operations."""

    def __init__(self, message: str, details: Dict[str, Any] = None):
        super().__init__(message)
        self.details = details or {}


class ValidationError(HandlerError):
    """Error during argument validation."""
    pass


class ExecutionError(HandlerError):
    """Error during tool execution."""
    pass


class BaseHandler(ABC):
    """Base class for all tool handlers.

    Subclasses must implement:
    - tool_name: Property returning the tool name
    - execute: Method that implements the tool logic
    """

    @property
    @abstractmethod
    def tool_name(self) -> str:
        """Tool name."""
        pass

    @abstractmethod
    async def execute(self, arguments: Dict[str, Any]) -> Dict[str, Any]:
        """Execute the tool logic.

        Args:
            arguments: Validated arguments

        Returns:
            Tool execution result as a dict.

        Raises:
            ExecutionError: If execution fails
        """
        pass

    def _format_error(
        self,
        error_type: str,
        error_message: str,
        details: Dict[str, Any] = None
    ) -> str:
        """Format an error response as JSON."""
        response = {
            "success": False,
            "error": {
                "type": error_type,
                "message": error_message,
                "tool": self.tool_name,
            }
        }
        if details:
            response["error"]["details"] = details
        return json.dumps(response, indent=2)

    async def handle(self, arguments: Dict[str, Any]) -> str:
        """Handle tool call with error handling.

        Args:
            arguments: Raw arguments from MCP

        Returns:
            JSON string of the result
        """
        try:
            logger.info(f"[{self.tool_name}] Executing with args: {list(arguments.keys())}")
            result = await self.execute(arguments)
            result["success"] = True
            logger.info(f"[{self.tool_name}] Success")
            return json.dumps(result, indent=2, default=str)

        except ValidationError as e:
            logger.error(f"[{self.tool_name}] Validation error: {e}")
            return self._format_error("ValidationError", str(e), e.details)

        except ExecutionError as e:
            logger.error(f"[{self.tool_name}] Execution error: {e}")
            return self._format_error("ExecutionError", str(e), e.details)

        except FileNotFoundError as e:
            logger.error(f"[{self.tool_name}] File not found: {e}")
            return self._format_error("FileNotFoundError", str(e))

        except Exception as e:
            logger.error(f"[{self.tool_name}] Unexpected error: {e}")
            logger.error(traceback.format_exc())
            return self._format_error(
                "UnexpectedError",
                str(e),
                {"traceback": traceback.format_exc()}
            )
