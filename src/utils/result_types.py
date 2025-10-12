"""
Common result types for all tools

Provides a unified interface for tool outputs.
"""

from dataclasses import dataclass, field
from typing import Any, Optional, List, Dict


@dataclass
class ToolResult:
    """
    Unified result type for all tools

    All tools should return this type to maintain consistency.

    Attributes:
        success: Whether the tool execution succeeded
        data: The main result data (can be any type)
        error: Error message if failed (None if success)
        suggestions: Helpful suggestions for the agent/user
        metadata: Additional information (e.g., execution time, file size)
    """
    success: bool
    data: Any = None
    error: Optional[str] = None
    suggestions: List[str] = field(default_factory=list)
    metadata: Dict[str, Any] = field(default_factory=dict)

    def __str__(self) -> str:
        """String representation for easy debugging"""
        if self.success:
            return f"✓ Success: {self.data}"
        else:
            return f"✗ Error: {self.error}"
