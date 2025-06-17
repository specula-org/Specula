import time
import logging
from openai import OpenAI
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
        
        # Check API key
        api_key = api_config.get('api_key')
        if not api_key or api_key.startswith('${'):
            raise ValueError("Please set DEEPSEEK_API_KEY environment variable")
        
        self.client = OpenAI(
            base_url=api_config.get('base_url'),
            api_key=api_key
        )
        
        self.model = api_config.get('model', 'deepseek-reasoner')
        self.temperature = api_config.get('temperature', 0.1)
        self.max_tokens = api_config.get('max_tokens', 8192)
    
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
                
                completion = self.client.chat.completions.create(
                    model=self.model,
                    messages=[
                        {"role": "system", "content": prompt},
                        {"role": "user", "content": content}
                    ],
                    temperature=self.temperature,
                    max_tokens=self.max_tokens,
                    stream=True
                )
                
                full_response = ""
                chunk_count = 0
                start_time = time.time()
                
                for chunk in completion:
                    chunk_count += 1
                    if chunk_count % 1000 == 0:
                        logger.debug(f"Received {chunk_count} chunks, elapsed time: {time.time()-start_time:.2f}s")
                        
                    if chunk.choices[0].delta.content is not None:
                        full_response += chunk.choices[0].delta.content
                
                logger.info(f"Request completed, received {chunk_count} chunks total")
                logger.debug(f"First line of response: {full_response.splitlines()[0][:50]}...")
                return full_response
                
            except Exception as e:
                retry_count += 1
                logger.error(f"API request failed (attempt {retry_count}/{max_retries}): {e}")
                
                if retry_count < max_retries:
                    wait_time = min(60, 2 ** retry_count)  # Exponential backoff
                    logger.info(f"Waiting {wait_time} seconds before retry...")
                    time.sleep(wait_time)
                else:
                    logger.error("Maximum retry attempts reached, request failed")
                    raise
        
        raise Exception("API request failed")

# Global client instance
_client = None

def get_llm_client(config_path: str = None) -> LLMClient:
    """Get global LLM client instance"""
    global _client
    if _client is None:
        _client = LLMClient(config_path)
    return _client 