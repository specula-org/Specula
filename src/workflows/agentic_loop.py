"""
AgenticLoop Workflow - Function calling agent with basic tools

This workflow gives the LLM autonomy to use basic tools:
- tla_compile: Check compilation status
- read: Read file content
- write: Write fixed content

The agent decides when and how to use these tools.
Limited only by compilation count (same budget as SimpleLoop).
"""

from typing import List
from .agentic_loop_base import AgenticLoopBase


class AgenticLoop(AgenticLoopBase):
    """
    Agentic workflow with basic tools (compile, read, write)
    """

    def __init__(self, llm_client, max_compilations: int = 3):
        super().__init__(
            llm_client=llm_client,
            max_compilations=max_compilations,
            workflow_name="agentic_loop"
        )

    def _get_available_tools(self) -> List[str]:
        """Basic tool set: compile, read, write"""
        return ['compile', 'read', 'write']
