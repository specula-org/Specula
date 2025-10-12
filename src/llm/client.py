import os
import time
import logging
from typing import Optional

try:
    import google.generativeai as genai
except ImportError:  # pragma: no cover - optional dependency until installed
    genai = None

from ..utils.config import get_config

logger = logging.getLogger(__name__)

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
        self.provider = api_config.get('provider', 'anthropic').lower()
        
        # Get API key from config or environment variables
        api_key = api_config.get('api_key')
        if not api_key:
            api_key = self._get_api_key_from_env()
        
        if not api_key:
            raise ValueError(f"API key not found for provider '{self.provider}'. Please set the appropriate environment variable or configure 'api_key' in config.yaml")
        
        # Get timeout from config and store it
        self.client_timeout = api_config.get('timeout', 3000) / 1000.0
        self.model = api_config.get('model', self._get_default_model())
        self.temperature = api_config.get('temperature', 0.1)
        self.max_tokens = api_config.get('max_tokens', 8192)
        self.use_streaming = api_config.get('use_streaming', True)

        # Initialize the appropriate client based on provider
        self._init_client(api_config, api_key)
        
        logger.info(f"Initialized LLM client - Provider: {self.provider}, Model: {self.model}")
    
    def _get_api_key_from_env(self) -> Optional[str]:
        """Get API key from environment variables based on provider"""
        if self.provider == 'anthropic':
            return os.getenv('ANTHROPIC_API_KEY')
        elif self.provider == 'openai':
            return os.getenv('OPENAI_API_KEY')
        elif self.provider == 'deepseek':
            return os.getenv('DEEPSEEK_API_KEY')
        elif self.provider == 'gemini':
            return os.getenv('GEMINI_API_KEY')
        else:
            # Try common environment variables as fallback
            return (os.getenv('API_KEY') or 
                   os.getenv('ANTHROPIC_API_KEY') or 
                   os.getenv('OPENAI_API_KEY') or 
                   os.getenv('DEEPSEEK_API_KEY') or 
                   os.getenv('GEMINI_API_KEY'))
    
    def _get_default_model(self) -> str:
        """Get default model based on provider"""
        if self.provider == 'anthropic':
            return 'claude-3-5-sonnet-20241022'
        elif self.provider == 'openai':
            return 'gpt-4'
        elif self.provider == 'deepseek':
            return 'deepseek-chat'
        elif self.provider == 'gemini':
            return 'gemini-1.5-pro'
        else:
            return 'claude-3-5-sonnet-20241022'
    
    def _init_client(self, api_config: dict, api_key: str):
        """Initialize the appropriate client based on provider"""
        if self.provider == 'anthropic':
            try:
                import anthropic
                self.client = anthropic.Anthropic(
                    api_key=api_key,
                    base_url=api_config.get('base_url'),
                    timeout=self.client_timeout
                )
            except ImportError:
                raise ImportError("anthropic package not found. Please install it with: pip install anthropic")
        
        elif self.provider in ['openai', 'deepseek']:
            try:
                from openai import OpenAI
                self.client = OpenAI(
                    base_url=api_config.get('base_url'),
                    api_key=api_key,
                    timeout=self.client_timeout
                )
            except ImportError:
                raise ImportError("openai package not found. Please install it with: pip install openai")

        elif self.provider == 'gemini':
            if genai is None:
                raise ImportError("google-generativeai package not found. Please install it with: pip install google-generativeai")

            configure_kwargs = {
                "api_key": api_key,
            }

            # Configure the global client; per-call model construction happens in _get_gemini_completion.
            genai.configure(**configure_kwargs)
            self.client = genai

        else:
            raise ValueError(f"Unsupported provider: {self.provider}")
    
    def get_completion(self, prompt: str, content: str, max_retries: int = 3) -> str:
        """Get LLM completion result
        
        Args:
            prompt: System prompt
            content: User input content
            max_retries: Maximum retry attempts
            
        Returns:
            LLM response content
        """
        retry_count = 0
        
        while retry_count < max_retries:
            try:
                logger.info(f"Starting API request, code block length: {len(content)} characters")
                logger.debug(f"Using prompt prefix: {prompt[:50]}...")
                
                if self.provider == 'anthropic':
                    return self._get_anthropic_completion(prompt, content)
                elif self.provider == 'gemini':
                    return self._get_gemini_completion(prompt, content)
                else:
                    return self._get_openai_completion(prompt, content)
                
            except Exception as e:
                retry_count += 1
                logger.error(f"API request failed (attempt {retry_count}/{max_retries}): {e}")
                
                if retry_count < max_retries:
                    wait_time = min(30, 2 ** retry_count)
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
                messages=[
                    {"role": "user", "content": content}
                ],
                timeout=self.client_timeout
            )
            
            full_response = response.content[0].text
            logger.info(f"Anthropic request completed")
            logger.debug(f"First line of response: {full_response.splitlines()[0][:50]}...")
            return full_response
            
        except Exception as e:
            logger.error(f"Anthropic API request failed: {e}")
            raise
    
    def _get_openai_completion(self, prompt: str, content: str) -> str:
        """Get completion from OpenAI-compatible API"""
        try:
            # Determine if this is GPT-5 model which requires max_completion_tokens instead of max_tokens
            is_gpt5_model = self.model.startswith("gpt-5")
            max_tokens_param = "max_completion_tokens" if is_gpt5_model else "max_tokens"

            # Prepare API parameters based on streaming config
            api_params = {
                "model": self.model,
                "messages": [
                    {"role": "system", "content": prompt},
                    {"role": "user", "content": content}
                ],
                "temperature": self.temperature,
                max_tokens_param: self.max_tokens,
                "stream": self.use_streaming,
                "timeout": self.client_timeout
            }

            completion = self.client.chat.completions.create(**api_params)

            if self.use_streaming:
                # Handle streaming response
                full_response = ""
                chunk_count = 0
                start_time = time.time()

                for chunk in completion:
                    chunk_count += 1
                    if chunk_count % 1000 == 0:
                        logger.debug(f"Received {chunk_count} chunks, elapsed time: {time.time()-start_time:.2f}s")

                    if chunk.choices[0].delta.content is not None:
                        full_response += chunk.choices[0].delta.content

                logger.info(f"Streaming request completed, received {chunk_count} chunks total")
                logger.debug(f"First line of response: {full_response.splitlines()[0][:50]}...")
                return full_response
            else:
                # Handle non-streaming response
                full_response = completion.choices[0].message.content
                logger.info(f"Non-streaming request completed")
                logger.debug(f"First line of response: {full_response.splitlines()[0][:50]}...")
                return full_response

        except Exception as e:
            logger.error(f"OpenAI-compatible API request failed: {e}")
            raise

    def _get_gemini_completion(self, prompt: str, content: str) -> str:
        """Get completion from Gemini API"""
        if self.client is None:
            raise RuntimeError("Gemini client not initialized")

        try:
            model = self.client.GenerativeModel(
                model_name=self.model,
                system_instruction=prompt,
                generation_config={
                    "temperature": self.temperature,
                    "max_output_tokens": self.max_tokens,
                }
            )

            response = model.generate_content(
                [
                    {
                        "role": "user",
                        "parts": [content]
                    }
                ],
                request_options={"timeout": self.client_timeout}
            )

            full_response = getattr(response, "text", "") or ""
            if not full_response.strip():
                raise ValueError("Gemini API returned an empty response")

            logger.info("Gemini request completed")
            logger.debug(f"First line of response: {full_response.splitlines()[0][:50]}...")
            return full_response

        except Exception as e:
            logger.error(f"Gemini API request failed: {e}")
            raise

# Global client instance
_client = None

def get_llm_client(config_path: str = None) -> LLMClient:
    """Get global LLM client instance"""
    global _client
    if _client is None:
        _client = LLMClient(config_path)
    return _client 
