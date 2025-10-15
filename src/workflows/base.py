"""
Base Workflow - Abstract base class for syntax correction workflows

Defines the unified interface and shared functionality for all workflows.
"""

from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from typing import List, Optional, Any, Dict
from pathlib import Path
import time
import shutil
import datetime

from ..tools.read_tool import ReadTool
from ..tools.write_tool import WriteTool
from ..tools.tla_compile_tool import TLACompileTool
from ..utils.result_types import ToolResult


@dataclass
class FixAttempt:
    """
    Record of a single fix attempt in the workflow

    Tracks what was tried and what the outcome was.
    """
    iteration: int
    errors_before: List[str]
    error_count_before: int
    action_description: str  # What was done this iteration
    errors_after: List[str]
    error_count_after: int
    improved: bool  # Did error count decrease?
    compilation_time: float
    timestamp: float = field(default_factory=time.time)


@dataclass
class WorkflowResult:
    """
    Complete result of running a workflow on a spec

    Contains all information about the workflow execution including
    success status, metrics, and detailed history.
    """
    # Basic info
    spec_path: str
    workflow_name: str

    # Outcome
    success: bool  # Did we fix all errors?

    # Resource usage (main metrics for comparison)
    compilations_used: int  # How many times we compiled (main limit)
    iterations: int  # How many workflow iterations
    llm_calls: int  # How many LLM API calls
    tool_calls_total: int  # Total tool invocations

    # Performance
    total_time: float  # Total elapsed time in seconds

    # Detailed history
    attempts: List[FixAttempt] = field(default_factory=list)

    # Token usage (if available)
    total_tokens: int = 0
    prompt_tokens: int = 0
    completion_tokens: int = 0

    # Additional info
    final_error_count: int = 0
    final_errors: List[str] = field(default_factory=list)
    metadata: Dict[str, Any] = field(default_factory=dict)

    def to_dict(self) -> Dict[str, Any]:
        """Convert result to dictionary for JSON serialization"""
        return {
            'spec_path': self.spec_path,
            'workflow_name': self.workflow_name,
            'success': self.success,
            'compilations_used': self.compilations_used,
            'iterations': self.iterations,
            'llm_calls': self.llm_calls,
            'tool_calls_total': self.tool_calls_total,
            'total_time': self.total_time,
            'total_tokens': self.total_tokens,
            'prompt_tokens': self.prompt_tokens,
            'completion_tokens': self.completion_tokens,
            'final_error_count': self.final_error_count,
            'final_errors': self.final_errors,
            'attempts': [
                {
                    'iteration': a.iteration,
                    'error_count_before': a.error_count_before,
                    'error_count_after': a.error_count_after,
                    'improved': a.improved,
                    'action': a.action_description,
                }
                for a in self.attempts
            ],
            'metadata': self.metadata,
        }


class BaseWorkflow(ABC):
    """
    Abstract base class for all syntax correction workflows

    Provides:
    - Unified interface (fix_spec method)
    - Shared tools (read, write, compile)
    - Compilation counting and limiting
    - Common utilities
    - Working copy management (protects original files)
    """

    def __init__(self, llm_client, max_compilations: int = 3, workflow_name: str = "base"):
        """
        Initialize workflow

        Args:
            llm_client: LLM client for making API calls
            max_compilations: Maximum number of compilations allowed (main limit)
            workflow_name: Name of this workflow (for results)
        """
        self.llm = llm_client
        self.max_compilations = max_compilations
        self.workflow_name = workflow_name

        # Counters (reset for each spec)
        self.compilation_count = 0
        self.llm_call_count = 0
        self.tool_call_count = 0

        # Token tracking
        self.total_tokens = 0
        self.prompt_tokens = 0
        self.completion_tokens = 0

        # Tools
        self.read_tool = ReadTool()
        self.write_tool = WriteTool()
        self.compile_tool = TLACompileTool()

    def fix_spec(self, spec_path: str) -> WorkflowResult:
        """
        Attempt to fix all compilation errors in a TLA+ spec

        This method creates a working copy to protect the original file,
        then calls the implementation.

        Args:
            spec_path: Path to the original .tla file

        Returns:
            WorkflowResult with complete execution information
        """
        original_spec = Path(spec_path).resolve()

        # Create working copy
        work_spec = self._create_work_copy(original_spec)
        print(f"Working on copy: {work_spec}")
        print(f"Original file protected: {original_spec}\n")

        # Call implementation on working copy
        result = self._fix_spec_implementation(str(work_spec))

        # Add metadata about files
        result.metadata['original_spec'] = str(original_spec)
        result.metadata['work_spec'] = str(work_spec)

        return result

    @abstractmethod
    def _fix_spec_implementation(self, work_spec_path: str) -> WorkflowResult:
        """
        Implementation of spec fixing logic (subclasses implement this)

        Args:
            work_spec_path: Path to working copy (modify this freely)

        Returns:
            WorkflowResult with complete execution information
        """
        pass

    def _reset_counters(self):
        """Reset all counters (call at start of fix_spec)"""
        self.compilation_count = 0
        self.llm_call_count = 0
        self.tool_call_count = 0
        self.total_tokens = 0
        self.prompt_tokens = 0
        self.completion_tokens = 0

    def compile_with_limit(self, spec_path: str) -> Optional[ToolResult]:
        """
        Compile with counting and limit checking

        Args:
            spec_path: Path to spec file

        Returns:
            ToolResult if within limit, None if limit exceeded
        """
        if self.compilation_count >= self.max_compilations:
            return None

        result = self.compile_tool.run(spec_path)
        self.compilation_count += 1
        self.tool_call_count += 1

        return result

    def read_spec(self, spec_path: str) -> ToolResult:
        """Read spec with counting"""
        result = self.read_tool.run(spec_path)
        self.tool_call_count += 1
        return result

    def write_spec(self, spec_path: str, content: str) -> ToolResult:
        """Write spec with counting"""
        result = self.write_tool.run(spec_path, content)
        self.tool_call_count += 1
        return result

    def _track_llm_call(self):
        """Track LLM call"""
        self.llm_call_count += 1
        # Note: Specula's LLMClient doesn't currently expose token usage
        # Token tracking would need to be added to LLMClient in the future

    def _is_stuck(self, attempts: List[FixAttempt], window: int = 3) -> bool:
        """
        Detect if workflow is stuck in a loop

        Args:
            attempts: List of fix attempts so far
            window: Number of attempts to look back

        Returns:
            True if stuck (same error count for 'window' attempts)
        """
        if len(attempts) < window:
            return False

        recent = attempts[-window:]
        error_counts = [a.error_count_after for a in recent]

        # All same error count = stuck
        return len(set(error_counts)) == 1 and error_counts[0] > 0

    def _extract_module_name(self, spec_path: str) -> str:
        """Extract expected module name from filename"""
        return Path(spec_path).stem

    def _format_errors_for_llm(self, errors: List[str]) -> str:
        """Format error messages for LLM prompt"""
        if not errors:
            return "No errors"

        formatted = []
        for i, error in enumerate(errors, 1):
            formatted.append(f"Error {i}:\n{error}")

        return "\n\n".join(formatted)

    def _create_work_copy(self, original_spec: Path) -> Path:
        """
        Create a working copy of the spec

        The copy preserves the directory structure for organization.

        Args:
            original_spec: Path to original spec file

        Returns:
            Path to working copy
        """
        # Create work directory (use absolute path from project root)
        project_root = Path(__file__).parent.parent.parent
        work_base = project_root / "experiments/syntax_phase/work_copies" / self.workflow_name
        work_base.mkdir(parents=True, exist_ok=True)

        # Extract system and LLM from path for organization
        # Path format: .../dataset/{system}/{llm}/spec_XXX/{name}.tla
        parts = original_spec.parts
        try:
            dataset_idx = parts.index('dataset')
            system = parts[dataset_idx + 1]
            llm = parts[dataset_idx + 2]
            spec_dir = parts[dataset_idx + 3]

            # Create organized structure: work_copies/{workflow}/{system}/{llm}/{spec_dir}/
            work_subdir = work_base / system / llm / spec_dir
            work_subdir.mkdir(parents=True, exist_ok=True)
            work_spec = work_subdir / original_spec.name
        except (ValueError, IndexError):
            # Fallback: simple flat structure with timestamp
            timestamp = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
            work_spec = work_base / f"{original_spec.stem}_{timestamp}{original_spec.suffix}"

        # Copy file to working location
        shutil.copy2(original_spec, work_spec)

        return work_spec
