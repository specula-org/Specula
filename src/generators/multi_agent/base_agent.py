"""Base class for all agents in multi-agent workflow"""

from abc import ABC, abstractmethod
from pathlib import Path
from typing import Any


class BaseAgent(ABC):
    """Base class for all agents"""

    def __init__(self, llm_client, prompts_dir: Path):
        self.llm = llm_client
        self.prompts_dir = prompts_dir

    @abstractmethod
    def run(self, *args, **kwargs) -> Any:
        """Execute agent's task. Each agent implements its own logic."""
        pass

    def _load_prompt(self, prompt_name: str) -> str:
        """Load prompt template from prompts directory"""
        prompt_path = self.prompts_dir / prompt_name
        if prompt_path.exists():
            return prompt_path.read_text()
        return f"Prompt not found: {prompt_name}"
