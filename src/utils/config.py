import os
import yaml
from typing import Dict, Any
from pathlib import Path

class Config:
    """Configuration management class"""
    
    def __init__(self, config_path: str = None):
        """Initialize configuration
        
        Args:
            config_path: Configuration file path, defaults to config.yaml in project root directory
        """
        if config_path is None:
            # Allow override via environment to avoid editing repo-tracked config.yaml
            env_config = os.getenv("SPECULA_CONFIG_PATH")
            if env_config:
                config_path = env_config
            else:
                # Get project root directory (Specula/)
                # Current file is src/utils/config.py, so we need to go up 2 levels
                project_root = Path(__file__).parent.parent.parent
                config_path = project_root / "config.yaml"
        
        self.config_path = Path(config_path).expanduser()
        self.config = self._load_config()
        
    def _load_config(self) -> Dict[str, Any]:
        """Load configuration file"""
        if not self.config_path.exists():
            raise FileNotFoundError(f"Configuration file does not exist: {self.config_path}")
            
        with open(self.config_path, 'r', encoding='utf-8') as f:
            config = yaml.safe_load(f)
            
        # Process environment variable replacement
        config = self._resolve_env_vars(config)
        return config
    
    def _resolve_env_vars(self, obj):
        """Recursively resolve environment variables"""
        if isinstance(obj, dict):
            return {k: self._resolve_env_vars(v) for k, v in obj.items()}
        elif isinstance(obj, list):
            return [self._resolve_env_vars(item) for item in obj]
        elif isinstance(obj, str) and obj.startswith("${") and obj.endswith("}"):
            # Extract environment variable name
            env_var = obj[2:-1]
            return os.getenv(env_var, obj)  # If environment variable doesn't exist, return original string
        else:
            return obj
    
    def get(self, key: str, default=None):
        """Get configuration value, supports dot-separated nested keys"""
        keys = key.split('.')
        value = self.config
        
        for k in keys:
            if isinstance(value, dict) and k in value:
                value = value[k]
            else:
                return default
                
        return value
    
    def get_api_config(self) -> Dict[str, Any]:
        """Get API configuration"""
        return self.get('llm', {})
    
    def get_paths_config(self) -> Dict[str, Any]:
        """Get paths configuration"""
        return self.get('paths', {})
    
    def get_experiments_config(self) -> Dict[str, Any]:
        """Get experiments configuration"""
        return self.get('experiments', {})
    
    def get_logging_config(self) -> Dict[str, Any]:
        """Get logging configuration"""
        return self.get('logging', {})

# Global configuration instance
_config = None

def get_config(config_path: str = None) -> Config:
    """Get global configuration instance"""
    global _config
    if _config is None:
        _config = Config(config_path)
    return _config 
