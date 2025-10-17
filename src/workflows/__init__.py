"""
Workflows for TLA+ specification syntax correction

This package contains different workflow implementations for fixing
TLA+ specification syntax errors.

Available workflows:
- SimpleLoop: Fixed iterative flow (compile → read → LLM → write)
- SimpleLoop_RAG: Fixed iterative flow with automatic RAG support
- AgenticLoop: Agent with basic tools (compile, read, write)
- AgenticLoop_RAG: Agent with RAG support for error pattern search
"""

from .base import BaseWorkflow, WorkflowResult, FixAttempt
from .simple_loop import SimpleLoop
from .simple_loop_rag import SimpleLoop_RAG
from .agentic_loop import AgenticLoop
from .agentic_loop_rag import AgenticLoop_RAG

# Legacy names for backward compatibility
ScriptBasedWorkflow = SimpleLoop
AgenticWorkflow = AgenticLoop

__all__ = [
    # Base classes
    'BaseWorkflow',
    'WorkflowResult',
    'FixAttempt',

    # New workflow names
    'SimpleLoop',
    'SimpleLoop_RAG',
    'AgenticLoop',
    'AgenticLoop_RAG',

    # Legacy names (deprecated)
    'ScriptBasedWorkflow',
    'AgenticWorkflow',
]
