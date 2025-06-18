#!/usr/bin/env python3
"""
Phase 4: Agent-based Runtime Correction
Generates TLC configuration and iteratively fixes runtime errors
"""

import os
import sys
import json
import yaml
import argparse
import subprocess
import tempfile
from pathlib import Path
from typing import Dict, List, Optional, Tuple
import logging

# Setup logging
logging.basicConfig(level=logging.INFO, format='[%(levelname)s] %(message)s')
logger = logging.getLogger(__name__)


class Config:
    """Configuration management class (simplified version)"""
    
    def __init__(self, config_path: str = "config.yaml"):
        self.config_path = config_path
        self.config = self._load_config()
    
    def _load_config(self) -> Dict:
        """Load configuration file"""
        try:
            with open(self.config_path, 'r', encoding='utf-8') as f:
                return yaml.safe_load(f)
        except FileNotFoundError:
            print(f"Configuration file {self.config_path} not found, using defaults.")
            return self._get_default_config()
        except Exception as e:
            print(f"Failed to load configuration: {e}, using defaults.")
            return self._get_default_config()
    
    def _get_default_config(self) -> Dict:
        """Default configuration"""
        return {
            'llm': {
                'model': 'claude-3-5-sonnet-20241022',
                'max_tokens': 8192,
                'temperature': 0.1,
                'timeout': 300,
                'use_streaming': True,
                'stream_chunk_size': 2000
            },
            'tla_validator': {
                'tools_path': 'lib/tla2tools.jar',
                'timeout': 60
            },
            'generation': {
                'max_correction_attempts': 3
            },
            'paths': {
                'prompts_dir': 'src/prompts',
                'output_dir': 'output'
            }
        }
    
    def get(self, key_path: str, default=None):
        """Get configuration value using dot notation"""
        keys = key_path.split('.')
        value = self.config
        for key in keys:
            if isinstance(value, dict) and key in value:
                value = value[key]
            else:
                return default
        return value


class LLMClient:
    """Simple LLM client for Claude models"""
    
    def __init__(self, config_obj: Config):
        self.model = config_obj.get('llm.model')
        self.max_tokens = config_obj.get('llm.max_tokens')
        self.temperature = config_obj.get('llm.temperature')
        self.timeout = config_obj.get('llm.timeout')
        self.use_streaming = config_obj.get('llm.use_streaming')
        self.stream_chunk_size = config_obj.get('llm.stream_chunk_size')
        
        self.api_key = os.getenv("ANTHROPIC_API_KEY")
        if not self.api_key:
            raise ValueError("Anthropic API key not found. Set ANTHROPIC_API_KEY environment variable.")
        
        logger.info(f"Initialized LLM client - Model: {self.model}, Max Tokens: {self.max_tokens}, Temperature: {self.temperature}")
    
    def generate(self, prompt: str, max_tokens: Optional[int] = None, temperature: Optional[float] = None) -> str:
        """Generate response using Anthropic API"""
        try:
            import anthropic
        except ImportError:
            raise ImportError("anthropic package not installed. Run: pip install anthropic")
        
        max_tokens = max_tokens or self.max_tokens
        temperature = temperature or self.temperature
        
        logger.info(f"Starting generation - Parameters: max_tokens={max_tokens}, temperature={temperature}")
        
        client = anthropic.Anthropic(api_key=self.api_key)
        
        try:
            if self.use_streaming:
                return self._generate_streaming(client, prompt, max_tokens, temperature)
            else:
                return self._generate_standard(client, prompt, max_tokens, temperature)
        except Exception as e:
            logger.error(f"Generation failed: {e}")
            if self.use_streaming:
                logger.info("Streaming failed, falling back to standard generation...")
                return self._generate_standard(client, prompt, max_tokens, temperature)
            else:
                raise
    
    def _generate_streaming(self, client, prompt: str, max_tokens: int, temperature: float) -> str:
        """Streaming generation"""
        logger.info("Starting streaming generation...")
        response_text = ""
        
        with client.messages.stream(
            model=self.model,
            max_tokens=max_tokens,
            temperature=temperature,
            messages=[{"role": "user", "content": prompt}]
        ) as stream:
            for text in stream.text_stream:
                response_text += text
                if len(response_text) % self.stream_chunk_size == 0:
                    logger.debug(f"Generated {len(response_text)} characters...")
        
        logger.info(f"Streaming generation complete. Total length: {len(response_text)} characters")
        return response_text
    
    def _generate_standard(self, client, prompt: str, max_tokens: int, temperature: float) -> str:
        """Standard generation"""
        logger.info("Starting standard generation...")
        
        response = client.messages.create(
            model=self.model,
            max_tokens=max_tokens,
            temperature=temperature,
            messages=[{"role": "user", "content": prompt}]
        )
        
        result = response.content[0].text
        logger.info(f"Standard generation complete. Length: {len(result)} characters")
        return result


class TLCRunner:
    """TLC model checker runner"""
    
    def __init__(self, tla_tools_path: str):
        self.tla_tools_path = tla_tools_path
        if not os.path.exists(self.tla_tools_path):
            raise FileNotFoundError(f"TLA+ tools not found at {self.tla_tools_path}")
    
    def run_tlc(self, spec_file: str, config_file: str, timeout: int = 60) -> Tuple[bool, str]:
        """Run TLC model checker on specification with configuration"""
        try:
            cmd = [
                "java", "-cp", self.tla_tools_path,
                "tlc2.TLC", "-config", config_file, spec_file
            ]
            
            result = subprocess.run(
                cmd, capture_output=True, text=True, 
                timeout=timeout, cwd=Path(spec_file).parent
            )
            
            # TLC returns 0 for success, other codes for various types of errors
            success = result.returncode == 0
            output = result.stdout + result.stderr
            
            return success, output
            
        except subprocess.TimeoutExpired:
            return False, f"TLC execution timed out after {timeout} seconds"
        except Exception as e:
            return False, f"TLC execution failed: {e}"


class RuntimeCorrector:
    """Main runtime correction class"""
    
    def __init__(self, config_path: str = "config.yaml"):
        # Load configuration
        self.config = Config(config_path)
        
        # Initialize components
        self.llm = LLMClient(self.config)
        self.tlc = TLCRunner(self.config.get('tla_validator.tools_path'))
        
        # Load prompts
        self.prompts_dir = Path(self.config.get('paths.prompts_dir'))
        self.config_prompt = self._load_prompt("step3_config_generation.txt")
        self.correction_prompt = self._load_prompt("step4_runtime_correction.txt")
        
        # Configuration
        self.max_correction_attempts = self.config.get('generation.max_correction_attempts', 3)
        self.tlc_timeout = self.config.get('tla_validator.timeout', 60)
    
    def _load_prompt(self, filename: str) -> str:
        """Load prompt template from file"""
        prompt_path = self.prompts_dir / filename
        if not prompt_path.exists():
            raise FileNotFoundError(f"Prompt file not found: {prompt_path}")
        
        with open(prompt_path, 'r', encoding='utf-8') as f:
            return f.read()
    
    def _read_file(self, file_path: str) -> str:
        """Read content from file"""
        with open(file_path, 'r', encoding='utf-8') as f:
            return f.read()
    
    def _extract_module_name(self, tla_code: str) -> str:
        """Extract module name from TLA+ code"""
        for line in tla_code.split('\n'):
            if "---- MODULE" in line:
                try:
                    return line.split("---- MODULE")[1].split("----")[0].strip()
                except IndexError:
                    continue
        return "UnnamedModule"
    
    def _extract_config_content(self, response: str) -> str:
        """Extract configuration content from LLM response"""
        lines = response.split('\n')
        in_code_block = False
        config_lines = []
        
        for line in lines:
            if line.strip().startswith('```') and not in_code_block:
                in_code_block = True
                continue
            elif line.strip() == '```' and in_code_block:
                break
            elif in_code_block:
                config_lines.append(line)
            elif line.strip().startswith('SPECIFICATION'):
                # Direct configuration content without code blocks
                config_lines = lines[lines.index(line):]
                break
        
        if not config_lines:
            return response.strip()
        return '\n'.join(config_lines).strip()
    
    def _extract_tla_code(self, response: str) -> str:
        """Extract TLA+ code from LLM response"""
        lines = response.split('\n')
        in_code_block = False
        tla_lines = []
        
        for line in lines:
            if line.strip().startswith('```tla') or line.strip().startswith('```'):
                if not tla_lines:
                    in_code_block = True
                    continue
            elif line.strip() == '```' and in_code_block:
                break
            if in_code_block:
                tla_lines.append(line)
        
        if not tla_lines:
            return response.strip()
        return '\n'.join(tla_lines).strip()
    
    def generate_config(self, spec_content: str) -> str:
        """Generate TLC configuration for the specification"""
        logger.info("Generating TLC configuration file...")
        
        prompt = self.config_prompt.format(tla_spec=spec_content)
        response = self.llm.generate(prompt)
        config_content = self._extract_config_content(response)
        
        if not config_content.strip():
            raise ValueError("Failed to generate configuration from LLM response")
        
        return config_content
    
    def fix_runtime_errors(self, spec_content: str, config_content: str, error_output: str) -> str:
        """Fix runtime errors based on TLC output"""
        logger.info("Fixing runtime errors...")
        
        prompt = self.correction_prompt.format(
            original_spec=spec_content,
            config_content=config_content,
            error_output=error_output
        )
        
        response = self.llm.generate(prompt)
        corrected_spec = self._extract_tla_code(response)
        
        if not corrected_spec.strip():
            raise ValueError("Failed to extract corrected specification from LLM response")
        
        return corrected_spec
    
    def correct_specification(self, input_spec_path: str, output_dir: str) -> Dict:
        """Main correction workflow"""
        logger.info(f"Starting runtime correction for: {input_spec_path}")
        
        # Setup output directory
        output_path = Path(output_dir)
        output_path.mkdir(parents=True, exist_ok=True)
        
        # Read input specification
        try:
            spec_content = self._read_file(input_spec_path)
        except FileNotFoundError:
            logger.error(f"Input specification file not found: {input_spec_path}")
            sys.exit(1)
        
        module_name = self._extract_module_name(spec_content)
        
        # Step 1: Generate TLC configuration
        config_content = self.generate_config(spec_content)
        config_file = output_path / f"{module_name}.cfg"
        
        with open(config_file, 'w', encoding='utf-8') as f:
            f.write(config_content)
        logger.info(f"Generated configuration: {config_file}")
        
        # Step 2: Initial TLC run
        current_spec = spec_content
        current_spec_file = output_path / f"{module_name}_initial.tla"
        
        with open(current_spec_file, 'w', encoding='utf-8') as f:
            f.write(current_spec)
        
        success, tlc_output = self.tlc.run_tlc(str(current_spec_file), str(config_file), self.tlc_timeout)
        
        if success:
            logger.info("Specification passed TLC model checking! No corrections needed.")
            final_spec = current_spec
            correction_attempts = 0
        else:
            logger.info("TLC found errors, starting correction process...")
            
            # Step 3: Iterative correction loop
            correction_attempts = 0
            
            while correction_attempts < self.max_correction_attempts and not success:
                correction_attempts += 1
                logger.info(f"Correction attempt {correction_attempts}/{self.max_correction_attempts}")
                
                try:
                    # Fix the errors
                    corrected_spec = self.fix_runtime_errors(current_spec, config_content, tlc_output)
                    
                    # Save corrected version
                    corrected_spec_file = output_path / f"{module_name}_attempt_{correction_attempts}.tla"
                    with open(corrected_spec_file, 'w', encoding='utf-8') as f:
                        f.write(corrected_spec)
                    
                    # Test the corrected specification
                    success, tlc_output = self.tlc.run_tlc(str(corrected_spec_file), str(config_file), self.tlc_timeout)
                    
                    if success:
                        logger.info(f"Correction successful after {correction_attempts} attempt(s)!")
                        final_spec = corrected_spec
                        break
                    else:
                        logger.warning(f"Correction attempt {correction_attempts} failed. Retrying...")
                        current_spec = corrected_spec
                        
                except Exception as e:
                    logger.error(f"Correction attempt {correction_attempts} failed with error: {e}")
                    if correction_attempts == self.max_correction_attempts:
                        final_spec = current_spec
                        break
                    continue
            
            if not success:
                logger.error(f"Failed to fix all errors after {self.max_correction_attempts} attempts")
                final_spec = current_spec
        
        # Save final specification
        final_module_name = self._extract_module_name(final_spec)
        final_spec_file = output_path / f"{final_module_name}_corrected.tla"
        
        with open(final_spec_file, 'w', encoding='utf-8') as f:
            f.write(final_spec)
        
        # Generate summary
        summary = {
            "input_file": input_spec_path,
            "output_directory": str(output_path),
            "config_file": str(config_file),
            "final_spec_file": str(final_spec_file),
            "tlc_passed": success,
            "correction_attempts": correction_attempts,
            "final_tlc_output": tlc_output if not success else "Model checking passed",
            "config_used": {
                "model": self.llm.model,
                "max_tokens": self.llm.max_tokens,
                "temperature": self.llm.temperature
            }
        }
        
        # Save summary
        summary_file = output_path / "runtime_correction_summary.json"
        with open(summary_file, 'w', encoding='utf-8') as f:
            json.dump(summary, f, indent=2, ensure_ascii=False)
        
        logger.info(f"Runtime correction complete. Final specification: {final_spec_file}")
        logger.info(f"Summary saved to: {summary_file}")
        
        return summary


def main():
    """Main entry point"""
    parser = argparse.ArgumentParser(
        description="Phase 4: Agent-based Runtime Correction",
        formatter_class=argparse.RawTextHelpFormatter
    )
    parser.add_argument("input", help="Input TLA+ specification file (.tla)")
    parser.add_argument("output", help="Output directory path")
    parser.add_argument("--config", default="config.yaml", help="Configuration file path")
    parser.add_argument("--model", help="Override LLM model from config")
    parser.add_argument("--max-tokens", type=int, help="Override max_tokens from config")
    parser.add_argument("--temperature", type=float, help="Override temperature from config")
    parser.add_argument("--max-attempts", type=int, help="Maximum correction attempts")
    parser.add_argument("--tlc-timeout", type=int, help="TLC execution timeout in seconds")
    parser.add_argument("--log-level", choices=["DEBUG", "INFO", "WARNING", "ERROR"],
                        help="Override log level")
    
    args = parser.parse_args()
    
    try:
        # Validate input
        if not args.input.endswith('.tla'):
            logger.error("Input file must be a .tla specification file")
            sys.exit(1)
        
        if not os.path.exists(args.input):
            logger.error(f"Input file not found: {args.input}")
            sys.exit(1)
        
        # Setup logging
        if args.log_level:
            logging.getLogger().setLevel(getattr(logging, args.log_level))
        
        # Create corrector
        corrector = RuntimeCorrector(args.config)
        
        # Apply command-line overrides
        if args.model:
            corrector.llm.model = args.model
            logger.info(f"Using command-line override for model: {args.model}")
        if args.max_tokens:
            corrector.llm.max_tokens = args.max_tokens
            logger.info(f"Using command-line override for max_tokens: {args.max_tokens}")
        if args.temperature:
            corrector.llm.temperature = args.temperature
            logger.info(f"Using command-line override for temperature: {args.temperature}")
        if args.max_attempts:
            corrector.max_correction_attempts = args.max_attempts
            logger.info(f"Using command-line override for max attempts: {args.max_attempts}")
        if args.tlc_timeout:
            corrector.tlc_timeout = args.tlc_timeout
            logger.info(f"Using command-line override for TLC timeout: {args.tlc_timeout}")
        
        # Run correction
        summary = corrector.correct_specification(args.input, args.output)
        
        # Print results
        print(f"\nRuntime correction complete!")
        print(f"Input: {summary['input_file']}")
        print(f"Final specification: {summary['final_spec_file']}")
        print(f"Configuration: {summary['config_file']}")
        print(f"TLC passed: {summary['tlc_passed']}")
        print(f"Correction attempts: {summary['correction_attempts']}")
        
        if not summary['tlc_passed']:
            print(f"Final TLC output: {summary['final_tlc_output']}")
            sys.exit(1)
        else:
            print("✅ Specification successfully passed TLC model checking!")
    
    except Exception as e:
        logger.error(f"Runtime correction failed: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main() 