"""
Base class for all tools

Provides a common interface that all tools should implement.
"""

from abc import ABC, abstractmethod
from ..utils.result_types import ToolResult


class BaseTool(ABC):
    """
    Base class for all tools

    All tools should inherit from this class and implement the run() method.
    """

    @property
    @abstractmethod
    def name(self) -> str:
        """Tool name"""
        pass

    @property
    @abstractmethod
    def description(self) -> str:
        """Tool description for LLM/agent"""
        pass

    @abstractmethod
    def run(self, **kwargs) -> ToolResult:
        """
        Execute the tool

        Args:
            **kwargs: Tool-specific arguments

        Returns:
            ToolResult with success status and data
        """
        pass
