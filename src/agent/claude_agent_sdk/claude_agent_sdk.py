"""
Minimal Claude Agent SDK-style client for Specula.

This is intentionally light: it wraps a single prompt/response loop using the
Anthropic client so you can start experimenting with the agent SDK patterns
without changing the existing workflows. Tool use is optional; if you provide
MCP-exposed tools, they will be forwarded via the `tools` parameter.
"""

import logging
from typing import Any, Dict, List, Optional

import anthropic

from src.utils.config import get_config

logger = logging.getLogger(__name__)


class ClaudeAgentSDKClient:
    """Thin adapter around the Anthropic client to mimic an agent entrypoint."""

    def __init__(self, config_path: Optional[str] = None):
        cfg = get_config(config_path)
        agent_cfg = cfg.get("agent", {})
        llm_cfg = cfg.get_api_config()

        # Prefer agent config, fall back to llm defaults
        self.model = agent_cfg.get("model") or llm_cfg.get("model", "claude-3-5-sonnet-20241022")
        self.max_tokens = agent_cfg.get("max_tokens") or llm_cfg.get("max_tokens", 8192)
        self.temperature = agent_cfg.get("temperature") or llm_cfg.get("temperature", 0.1)
        self.system_prompt = agent_cfg.get("system_prompt", "You are a helpful agent.")
        self.base_url = agent_cfg.get("base_url") or llm_cfg.get("base_url")
        self.use_streaming = agent_cfg.get("use_streaming", llm_cfg.get("use_streaming", True))
        timeout_ms = agent_cfg.get("timeout") or llm_cfg.get("timeout")
        self.timeout_seconds: Optional[float] = None
        if timeout_ms:
            self.timeout_seconds = timeout_ms / 1000.0

        api_key = agent_cfg.get("api_key") or llm_cfg.get("api_key")
        if not api_key:
            # Minimal env-based lookup to avoid importing the whole LLM client
            api_key = (
                cfg.get_logging_config().get("api_key")  # unlikely, but keep compatibility
                or self._get_api_key_from_env()
            )

        if not api_key:
            raise ValueError("API key not found for Claude Agent SDK client. Set ANTHROPIC_API_KEY or configure api_key.")

        client_kwargs: Dict[str, Any] = {"api_key": api_key}
        if self.base_url:
            client_kwargs["base_url"] = self.base_url

        self.client = anthropic.Anthropic(**client_kwargs)

    def _get_api_key_from_env(self) -> Optional[str]:
        """Get Anthropic API key from common environment variables."""
        import os

        return os.getenv("ANTHROPIC_API_KEY")

    def run(self, prompt: str, tools: Optional[List[Dict[str, Any]]] = None) -> str:
        """
        Execute a basic agent-style turn and return the model text.

        Args:
            prompt: The user/task prompt.
            tools: Optional list of tool schemas (e.g., MCP-exposed tools) to pass through.
        """
        logger.info("Starting Claude agent call (model=%s)", self.model)

        kwargs: Dict[str, Any] = {
            "model": self.model,
            "max_tokens": self.max_tokens,
            "temperature": self.temperature,
            "system": self.system_prompt,
            "messages": [{"role": "user", "content": prompt}],
        }
        if tools:
            kwargs["tools"] = tools
        if self.timeout_seconds:
            kwargs["timeout"] = self.timeout_seconds

        if self.use_streaming:
            parts: List[str] = []
            with self.client.messages.stream(**kwargs) as stream:
                for event in stream:
                    if event.type == "content_block_delta" and getattr(event.delta, "type", "") == "text_delta":
                        parts.append(event.delta.text)
                try:
                    final_msg = stream.get_final_message()
                    logger.debug("Stream finished, id=%s", getattr(final_msg, "id", None))
                except Exception:
                    logger.debug("Stream finished (no final message metadata available)")
            return "".join(parts)

        resp = self.client.messages.create(**kwargs)

        # Extract plain text content (ignore tool calls for this minimal adapter)
        parts: List[str] = []
        for block in resp.content:
            if block.type == "text":
                parts.append(block.text)
            # Tool calls could be handled here later if needed

        return "\n".join(parts)
