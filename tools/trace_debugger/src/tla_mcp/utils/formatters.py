"""Response formatting utilities."""

import json
from typing import Dict, Any, Optional


def format_error_response(tool_name: str, error_type: str,
                          error_message: str, **kwargs) -> str:
    """Format error response as JSON string.

    Args:
        tool_name: Name of the tool that failed
        error_type: Type of error (ValidationError, ExecutionError, etc.)
        error_message: Error message
        **kwargs: Additional fields to include in response

    Returns:
        JSON string of error response
    """
    result = {
        "success": False,
        "tool": tool_name,
        "error_type": error_type,
        "error_message": error_message
    }
    result.update(kwargs)
    return json.dumps(result, indent=2)


def format_success_response(data: Dict[str, Any]) -> str:
    """Format success response as JSON string.

    Args:
        data: Response data

    Returns:
        JSON string of success response
    """
    result = {"success": True}
    result.update(data)
    return json.dumps(result, indent=2)
