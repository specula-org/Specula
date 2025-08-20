import os
import time
import logging
import hashlib
import json
from typing import Optional
from pathlib import Path
from ..utils.config import get_config

logger = logging.getLogger(__name__)


class LLMCache:
    """Deterministic cache for LLM responses based on content hash"""

    def __init__(self, cache_dir: str = None):
        """Initialize LLM cache

        Args:
            cache_dir: Cache directory path, defaults to .cache/llm in project root
        """
        if cache_dir is None:
            project_root = Path(__file__).parent.parent.parent
            cache_dir = project_root / ".cache" / "llm"

        self.cache_dir = Path(cache_dir)
        self.cache_dir.mkdir(parents=True, exist_ok=True)
        logger.info(f"LLM cache initialized at: {self.cache_dir}")

    def _get_cache_key(
        self, prompt: str, content: str, model: str, temperature: float, max_tokens: int
    ) -> str:
        """Generate deterministic cache key from request parameters"""
        # Create a hash of the request parameters
        request_data = {
            "prompt": prompt,
            "content": content,
            "model": model,
            "temperature": temperature,
            "max_tokens": max_tokens,
        }

        # Sort keys for deterministic ordering
        sorted_data = json.dumps(request_data, sort_keys=True, separators=(",", ":"))
        return hashlib.sha256(sorted_data.encode("utf-8")).hexdigest()

    def get(
        self, prompt: str, content: str, model: str, temperature: float, max_tokens: int
    ) -> Optional[str]:
        """Get cached response if available"""
        try:
            cache_key = self._get_cache_key(
                prompt, content, model, temperature, max_tokens
            )
            cache_file = self.cache_dir / f"{cache_key}.json"

            if cache_file.exists():
                with open(cache_file, "r", encoding="utf-8") as f:
                    cached_data = json.load(f)
                    logger.debug(f"Cache hit for request: {cache_key[:8]}...")
                    return cached_data.get("response")

            return None
        except Exception as e:
            logger.warning(f"Cache read failed: {e}")
            return None

    def set(
        self,
        prompt: str,
        content: str,
        model: str,
        temperature: float,
        max_tokens: int,
        response: str,
    ):
        """Cache LLM response"""
        try:
            cache_key = self._get_cache_key(
                prompt, content, model, temperature, max_tokens
            )
            cache_file = self.cache_dir / f"{cache_key}.json"

            cache_data = {
                "prompt": prompt,
                "content": content,
                "model": model,
                "temperature": temperature,
                "max_tokens": max_tokens,
                "response": response,
                "timestamp": time.time(),
            }

            with open(cache_file, "w", encoding="utf-8") as f:
                json.dump(cache_data, f, indent=2, ensure_ascii=False)

            logger.debug(f"Cached response for request: {cache_key[:8]}...")
        except Exception as e:
            logger.warning(f"Cache write failed: {e}")

    def clear(self):
        """Clear all cached responses"""
        try:
            for cache_file in self.cache_dir.glob("*.json"):
                cache_file.unlink()
            logger.info("LLM cache cleared")
        except Exception as e:
            logger.warning(f"Cache clear failed: {e}")

    def get_stats(self) -> dict:
        """Get cache statistics"""
        try:
            cache_files = list(self.cache_dir.glob("*.json"))
            total_size = sum(f.stat().st_size for f in cache_files)

            return {
                "cache_files": len(cache_files),
                "total_size_bytes": total_size,
                "total_size_mb": round(total_size / (1024 * 1024), 2),
            }
        except Exception as e:
            logger.warning(f"Cache stats failed: {e}")
            return {"error": str(e)}


class LLMClient:
    """LLM client for unified API call management"""

    def __init__(self, config_path: str = None):
        """Initialize LLM client

        Args:
            config_path: Configuration file path
        """
        self.config = get_config(config_path)
        api_config = self.config.get_api_config()

        # Get provider configuration
        self.provider = api_config.get("provider", "anthropic").lower()

        # Get API key from config or environment variables
        api_key = api_config.get("api_key")
        if not api_key:
            api_key = self._get_api_key_from_env()

        if not api_key:
            raise ValueError(
                f"API key not found for provider '{self.provider}'. Please set the appropriate environment variable or configure 'api_key' in config.yaml"
            )

        # Get timeout from config and store it
        self.client_timeout = api_config.get("timeout", 3000) / 1000.0
        self.model = api_config.get("model", self._get_default_model())
        self.temperature = api_config.get("temperature", 0.1)
        self.max_tokens = api_config.get("max_tokens", 8192)

        # Initialize cache
        self.cache = LLMCache()

        # Initialize the appropriate client based on provider
        self._init_client(api_config, api_key)

        logger.info(
            f"Initialized LLM client - Provider: {self.provider}, Model: {self.model}"
        )

    def _get_api_key_from_env(self) -> Optional[str]:
        """Get API key from environment variables based on provider"""
        if self.provider == "anthropic":
            return os.getenv("ANTHROPIC_API_KEY")
        elif self.provider == "openai":
            return os.getenv("OPENAI_API_KEY")
        elif self.provider == "deepseek":
            return os.getenv("DEEPSEEK_API_KEY")
        else:
            # Try common environment variables as fallback
            return (
                os.getenv("API_KEY")
                or os.getenv("ANTHROPIC_API_KEY")
                or os.getenv("OPENAI_API_KEY")
                or os.getenv("DEEPSEEK_API_KEY")
            )

    def _get_default_model(self) -> str:
        """Get default model based on provider"""
        if self.provider == "anthropic":
            return "claude-3-5-sonnet-20241022"
        elif self.provider == "openai":
            return "gpt-4"
        elif self.provider == "deepseek":
            return "deepseek-chat"
        else:
            return "claude-3-5-sonnet-20241022"

    def _init_client(self, api_config: dict, api_key: str):
        """Initialize the appropriate client based on provider"""
        if self.provider == "anthropic":
            try:
                import anthropic

                self.client = anthropic.Anthropic(
                    api_key=api_key,
                    base_url=api_config.get("base_url"),
                    timeout=self.client_timeout,
                )
            except ImportError:
                raise ImportError(
                    "anthropic package not found. Please install it with: pip install anthropic"
                )

        elif self.provider in ["openai", "deepseek"]:
            try:
                from openai import OpenAI

                self.client = OpenAI(
                    base_url=api_config.get("base_url"),
                    api_key=api_key,
                    timeout=self.client_timeout,
                )
            except ImportError:
                raise ImportError(
                    "openai package not found. Please install it with: pip install openai"
                )

        else:
            raise ValueError(f"Unsupported provider: {self.provider}")

    def get_completion(self, prompt: str, content: str, max_retries: int = 3) -> str:
        """Get LLM completion result with caching

        Args:
            prompt: System prompt
            content: User input content
            max_retries: Maximum retry attempts

        Returns:
            LLM response content
        """
        # Check cache first
        cached_response = self.cache.get(
            prompt, content, self.model, self.temperature, self.max_tokens
        )
        if cached_response:
            logger.info("Using cached LLM response")
            return cached_response

        retry_count = 0

        while retry_count < max_retries:
            try:
                logger.info(
                    f"Starting API request, code block length: {len(content)} characters"
                )
                logger.debug(f"Using prompt prefix: {prompt[:50]}...")

                if self.provider == "anthropic":
                    response = self._get_anthropic_completion(prompt, content)
                else:
                    response = self._get_openai_completion(prompt, content)

                # Cache the response
                self.cache.set(
                    prompt,
                    content,
                    self.model,
                    self.temperature,
                    self.max_tokens,
                    response,
                )

                return response

            except Exception as e:
                retry_count += 1
                logger.error(
                    f"API request failed (attempt {retry_count}/{max_retries}): {e}"
                )

                if retry_count < max_retries:
                    wait_time = min(30, 2**retry_count)
                    logger.info(f"Waiting {wait_time} seconds before retry...")
                    time.sleep(wait_time)
                else:
                    logger.error("Maximum retry attempts reached, request failed")
                    raise

        raise Exception("API request failed")

    def _get_anthropic_completion(self, prompt: str, content: str) -> str:
        """Get completion from Anthropic API"""
        try:
            response = self.client.messages.create(
                model=self.model,
                max_tokens=self.max_tokens,
                temperature=self.temperature,
                system=prompt,
                messages=[{"role": "user", "content": content}],
                timeout=self.client_timeout,
            )

            full_response = response.content[0].text
            logger.info(f"Anthropic request completed")
            logger.debug(
                f"First line of response: {full_response.splitlines()[0][:50]}..."
            )
            return full_response

        except Exception as e:
            logger.error(f"Anthropic API request failed: {e}")
            raise

    def _get_openai_completion(self, prompt: str, content: str) -> str:
        """Get completion from OpenAI-compatible API"""
        try:
            # Try streaming first
            try:
                completion = self.client.chat.completions.create(
                    model=self.model,
                    messages=[
                        {"role": "system", "content": prompt},
                        {"role": "user", "content": content},
                    ],
                    temperature=self.temperature,
                    max_tokens=self.max_tokens,
                    stream=True,
                    timeout=30,
                )

                full_response = ""
                chunk_count = 0
                start_time = time.time()

                for chunk in completion:
                    chunk_count += 1
                    if chunk_count % 1000 == 0:
                        logger.debug(
                            f"Received {chunk_count} chunks, elapsed time: {time.time()-start_time:.2f}s"
                        )

                    if chunk.choices[0].delta.content is not None:
                        full_response += chunk.choices[0].delta.content

                logger.info(
                    f"Streaming request completed, received {chunk_count} chunks total"
                )
                logger.debug(
                    f"First line of response: {full_response.splitlines()[0][:50]}..."
                )
                return full_response

            except Exception as stream_error:
                logger.warning(
                    f"Streaming request failed: {stream_error}, trying non-streaming..."
                )

                # Fallback to non-streaming
                completion = self.client.chat.completions.create(
                    model=self.model,
                    messages=[
                        {"role": "system", "content": prompt},
                        {"role": "user", "content": content},
                    ],
                    temperature=self.temperature,
                    max_tokens=self.max_tokens,
                    stream=False,
                    timeout=self.client_timeout,
                )

                full_response = completion.choices[0].message.content
                logger.info(f"Non-streaming request completed")
                logger.debug(
                    f"First line of response: {full_response.splitlines()[0][:50]}..."
                )
                return full_response

        except Exception as e:
            logger.error(f"OpenAI-compatible API request failed: {e}")
            raise


# Global client instance
_client = None


def get_llm_client(config_path: str = None) -> LLMClient:
    """Get global LLM client instance"""
    global _client
    if _client is None:
        _client = LLMClient(config_path)
    return _client
