import os
import time
import logging
from typing import Optional
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
        elif self.provider == 'genai':
            return os.getenv('GEMINI_API_KEY') or os.getenv('GOOGLE_AI_API_KEY')
        else:
            # Try common environment variables as fallback
            return (os.getenv('API_KEY') or
                   os.getenv('ANTHROPIC_API_KEY') or
                   os.getenv('OPENAI_API_KEY') or
                   os.getenv('DEEPSEEK_API_KEY') or
                   os.getenv('GEMINI_API_KEY') or
                   os.getenv('GOOGLE_AI_API_KEY'))
    
    def _get_default_model(self) -> str:
        """Get default model based on provider"""
        if self.provider == 'anthropic':
            return 'claude-3-5-sonnet-20241022'
        elif self.provider == 'openai':
            return 'gpt-4'
        elif self.provider == 'deepseek':
            return 'deepseek-chat'
        elif self.provider == 'genai':
            return 'gemini-2.5-flash'
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

        elif self.provider == 'genai':
            try:
                from google import genai
                self.client = genai.Client(api_key=api_key)
                # Store thinking budget if configured, default to 32768 for GenAI
                self.thinking_budget = api_config.get('thinking_budget', 32768)
            except ImportError:
                raise ImportError("google-genai package not found. Please install it with: pip install google-genai")

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
                elif self.provider == 'genai':
                    return self._get_genai_completion(prompt, content)
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

    def _get_genai_completion(self, prompt: str, content: str) -> str:
        """Get completion from Google GenAI API"""
        try:
            from google.genai import types

            # Format complete prompt - combine system prompt and user content
            # Add random prefix to avoid Gemini caching/deduplication issues
            import random
            random_id = random.randint(100000, 999999)
            complete_prompt = f"[REQ-{random_id}] Please ignore this prefix. {prompt}\n\n{content}"

            # Prepare generation config
            config_params = {
                "temperature": self.temperature,
                "max_output_tokens": self.max_tokens,
            }

            # Add thinking config if configured
            thinking_budget = getattr(self, 'thinking_budget', 32768)  # Default to 32768 as per config
            if thinking_budget > 0:
                config_params["thinking_config"] = types.ThinkingConfig(
                    thinking_budget=thinking_budget
                )
                logger.debug(f"Using thinking mode with budget: {thinking_budget}")
            # Note: Don't explicitly set thinking_budget=0 as it's invalid for models that require thinking mode

            genai_config = types.GenerateContentConfig(**config_params)

            # Use streaming for better responsiveness
            if self.use_streaming:
                logger.debug("Using streaming GenAI API")
                stream = self.client.models.generate_content_stream(
                    model=self.model,
                    contents=complete_prompt,
                    config=genai_config
                )

                # Collect streaming response
                full_response = ""
                for chunk in stream:
                    if hasattr(chunk, 'text') and chunk.text:
                        full_response += chunk.text

            else:
                logger.debug("Using non-streaming GenAI API")
                response = self.client.models.generate_content(
                    model=self.model,
                    contents=complete_prompt,
                    config=genai_config
                )
                full_response = response.text if hasattr(response, 'text') else str(response)

            if not full_response:
                raise Exception("Empty response from GenAI API")

            logger.info(f"GenAI request completed")
            logger.debug(f"First line of response: {full_response.splitlines()[0][:50]}...")
            return full_response.strip()

        except Exception as e:
            logger.error(f"GenAI API request failed: {e}")
            raise

    def get_completion_with_tools(self, messages: list, tools: list, max_retries: int = 3) -> dict:
        """Get LLM completion with function calling / tool use

        Args:
            messages: List of message dicts [{"role": "...", "content": "..."}]
            tools: List of tool schemas (OpenAI format)
            max_retries: Maximum retry attempts

        Returns:
            Dict with:
                - text: str (generated text if any)
                - tool_calls: list (list of tool calls if any)
                - stop_reason: str
        """
        retry_count = 0

        while retry_count < max_retries:
            try:
                if self.provider == 'anthropic':
                    return self._get_anthropic_completion_with_tools(messages, tools)
                else:
                    # OpenAI, DeepSeek support tool calling natively
                    return self._get_openai_completion_with_tools(messages, tools)

            except Exception as e:
                retry_count += 1
                logger.error(f"Tool calling API request failed (attempt {retry_count}/{max_retries}): {e}")

                if retry_count < max_retries:
                    wait_time = min(30, 2 ** retry_count)
                    logger.info(f"Waiting {wait_time} seconds before retry...")
                    time.sleep(wait_time)
                else:
                    logger.error("Maximum retry attempts reached, request failed")
                    raise

        raise Exception("API request with tools failed")

    def _get_anthropic_completion_with_tools(self, messages: list, tools: list) -> dict:
        """Get completion with tools from Anthropic API"""
        try:
            # Convert OpenAI-style tools to Anthropic format
            anthropic_tools = [
                {
                    "name": tool["function"]["name"],
                    "description": tool["function"]["description"],
                    "input_schema": tool["function"]["parameters"]
                }
                for tool in tools
            ]

            # Extract system message if present
            system_msg = None
            user_messages = []
            for msg in messages:
                if msg["role"] == "system":
                    system_msg = msg["content"]
                else:
                    user_messages.append(msg)

            response = self.client.messages.create(
                model=self.model,
                max_tokens=self.max_tokens,
                temperature=self.temperature,
                system=system_msg if system_msg else None,
                messages=user_messages,
                tools=anthropic_tools,
                timeout=self.client_timeout
            )

            # Extract content
            text_content = ""
            tool_calls = []

            for block in response.content:
                if block.type == "text":
                    text_content = block.text
                elif block.type == "tool_use":
                    tool_calls.append({
                        "id": block.id,
                        "name": block.name,
                        "function": {
                            "name": block.name,
                            "arguments": block.input
                        },
                        "arguments": block.input
                    })

            return {
                "text": text_content,
                "tool_calls": tool_calls if tool_calls else None,
                "stop_reason": response.stop_reason
            }

        except Exception as e:
            logger.error(f"Anthropic tool calling failed: {e}")
            raise

    def _get_openai_completion_with_tools(self, messages: list, tools: list) -> dict:
        """Get completion with tools from OpenAI-compatible API"""
        try:
            response = self.client.chat.completions.create(
                model=self.model,
                messages=messages,
                tools=tools,
                temperature=self.temperature,
                max_tokens=self.max_tokens,
                timeout=self.client_timeout
            )

            message = response.choices[0].message

            return {
                "text": message.content or "",
                "tool_calls": message.tool_calls if hasattr(message, 'tool_calls') else None,
                "stop_reason": response.choices[0].finish_reason
            }

        except Exception as e:
            logger.error(f"OpenAI tool calling failed: {e}")
            raise

# Global client instance
_client = None

def get_llm_client(config_path: str = None) -> LLMClient:
    """Get global LLM client instance"""
    global _client
    if _client is None:
        _client = LLMClient(config_path)
    return _client 
