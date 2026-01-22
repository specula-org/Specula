"""Base handler for MCP tools."""

import json
import traceback
from abc import ABC, abstractmethod
from typing import Dict, Any

from ..utils.logger import logger
from ..utils.validators import validate_arguments
from ..utils.formatters import format_error_response
from ..utils.errors import ValidationError, ExecutionError


class BaseHandler(ABC):
    """Base class for all tool handlers.

    Subclasses must implement:
    - tool_name: Property returning the tool name
    - argument_schema: Property returning JSON schema for arguments
    - execute: Method that implements the tool logic
    """

    @property
    @abstractmethod
    def tool_name(self) -> str:
        """Tool name."""
        pass

    @property
    @abstractmethod
    def argument_schema(self) -> Dict[str, Any]:
        """JSON schema for arguments validation."""
        pass

    @abstractmethod
    async def execute(self, arguments: Dict[str, Any]) -> Dict[str, Any]:
        """Execute the tool logic.

        Args:
            arguments: Validated arguments (with defaults applied)

        Returns:
            Tool execution result as a dict.

        Raises:
            ExecutionError: If execution fails
        """
        pass

    async def handle(self, arguments: Dict[str, Any]) -> str:
        """Handle tool call with validation and error handling.

        Args:
            arguments: Raw arguments from MCP

        Returns:
            JSON string of the result
        """
        try:
            # 1. Validate arguments
            logger.info(f"[{self.tool_name}] Validating arguments...")
            validated_args = validate_arguments(
                arguments,
                self.argument_schema
            )

            # 2. Execute tool logic
            logger.info(f"[{self.tool_name}] Executing...")
            result = await self.execute(validated_args)

            # 3. Add success flag and return formatted result
            result["success"] = True
            logger.info(f"[{self.tool_name}] Success")
            return json.dumps(result, indent=2)

        except ValidationError as e:
            logger.error(f"[{self.tool_name}] Validation error: {e}")
            return format_error_response(
                tool_name=self.tool_name,
                error_type="ValidationError",
                error_message=str(e)
            )
        except ExecutionError as e:
            logger.error(f"[{self.tool_name}] Execution error: {e}")
            return format_error_response(
                tool_name=self.tool_name,
                error_type="ExecutionError",
                error_message=str(e),
                details=e.details if hasattr(e, 'details') else None
            )
        except Exception as e:
            logger.error(f"[{self.tool_name}] Unexpected error: {e}")
            logger.error(traceback.format_exc())
            return format_error_response(
                tool_name=self.tool_name,
                error_type="UnexpectedError",
                error_message=str(e),
                traceback=traceback.format_exc()
            )
