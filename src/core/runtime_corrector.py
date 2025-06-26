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

# Import unified LLM client and config
from ..llm.client import get_llm_client
from ..utils.config import get_config

# Setup logging
logging.basicConfig(level=logging.INFO, format='[%(levelname)s] %(message)s')
logger = logging.getLogger(__name__)


class TLCRunner:
    """TLC model checker runner"""
    
    def __init__(self, tla_tools_path: str):
        # Convert to absolute path to handle cwd changes
        self.tla_tools_path = str(Path(tla_tools_path).resolve())
        if not os.path.exists(self.tla_tools_path):
            raise FileNotFoundError(f"TLA+ tools not found at {self.tla_tools_path}")
    
    def run_tlc(self, spec_file: str, config_file: str, timeout: int = 60) -> Tuple[bool, str]:
        """Run TLC model checker on specification with configuration"""
        try:
            # Convert all paths to absolute to handle cwd changes
            spec_path = Path(spec_file).resolve()
            config_path = Path(config_file).resolve()
            working_dir = spec_path.parent
            
            cmd = [
                "java", "-cp", self.tla_tools_path,
                "tlc2.TLC", "-config", str(config_path), str(spec_path)
            ]
            
            result = subprocess.run(
                cmd, capture_output=True, text=True, 
                timeout=timeout, cwd=working_dir
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
        # Load configuration using unified config system
        self.config = get_config(config_path)
        
        # Initialize unified LLM client
        self.llm = get_llm_client(config_path)
        
        # Initialize TLC runner
        tla_tools_path = self.config.get('tla_validator', {}).get('tools_path', 'lib/tla2tools.jar')
        self.tlc = TLCRunner(tla_tools_path)
        
        # Load configuration values
        self.max_correction_attempts = self.config.get('generation', {}).get('max_correction_attempts', 3)
        self.tlc_timeout = self.config.get('tla_validator', {}).get('timeout', 60)
        
        # Load prompts
        self.config_prompt = self._load_prompt("step3_config_generation.txt")
        self.correction_prompt = self._load_prompt("step4_runtime_correction.txt")
        
        logger.info("Runtime corrector initialized with unified LLM client")
    
    def _load_prompt(self, filename: str) -> str:
        """Load prompt template from file"""
        prompts_dir = self.config.get('paths', {}).get('prompts_dir', 'src/prompts')
        prompt_path = Path(prompts_dir) / filename
        try:
            with open(prompt_path, 'r', encoding='utf-8') as f:
                return f.read()
        except FileNotFoundError:
            logger.error(f"Prompt file not found: {prompt_path}")
            sys.exit(1)
    
    def _read_file(self, file_path: str) -> str:
        """Read file content"""
        with open(file_path, 'r', encoding='utf-8') as f:
            return f.read()
    
    def _extract_module_name(self, tla_code: str) -> str:
        """Extract module name from TLA+ code"""
        lines = tla_code.strip().split('\n')
        for line in lines:
            if line.strip().startswith('---- MODULE'):
                parts = line.split()
                if len(parts) >= 3:
                    return parts[2]
        return "UnknownModule"
    
    def _extract_config_content(self, response: str) -> str:
        """Extract configuration content from LLM response"""
        lines = response.split('\n')
        config_lines = []
        in_config_block = False
        
        for line in lines:
            # Look for configuration file markers
            if '```' in line and any(marker in line.lower() for marker in ['cfg', 'config', 'tlc']):
                in_config_block = True
                continue
            elif line.strip() == '```' and in_config_block:
                break
            elif in_config_block:
                config_lines.append(line)
            # Also capture lines that look like configuration content
            elif any(keyword in line for keyword in ['SPECIFICATION', 'CONSTANTS', 'INVARIANT', 'PROPERTY']):
                config_lines.append(line)
        
        if not config_lines:
            # If no code block found, try to extract configuration-like lines
            for line in lines:
                if any(keyword in line for keyword in ['SPECIFICATION', 'CONSTANTS', 'INVARIANT', 'PROPERTY']):
                    config_lines.append(line)
        
        return '\n'.join(config_lines).strip()
    
    def _extract_tla_code(self, response: str) -> str:
        """Extract TLA+ code from LLM response"""
        lines = response.split('\n')
        tla_lines = []
        in_code_block = False
        
        for line in lines:
            # Look for TLA+ code block markers
            if '```' in line and any(marker in line.lower() for marker in ['tla', 'tlaplus']):
                in_code_block = True
                continue
            elif line.strip() == '```' and in_code_block:
                break
            elif in_code_block:
                tla_lines.append(line)
        
        if not tla_lines:
            return response.strip()
        return '\n'.join(tla_lines).strip()
    
    def generate_config(self, spec_content: str) -> str:
        """Generate TLC configuration for the specification"""
        logger.info("Generating TLC configuration file...")
        
        prompt = self.config_prompt.format(tla_spec=spec_content)
        response = self.llm.get_completion(
            "You are a TLA+ expert. Generate a TLC configuration file for the given specification.",
            prompt
        )
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
        
        response = self.llm.get_completion(
            "You are a TLA+ expert. Fix the runtime errors in the given specification based on the TLC error output.",
            prompt
        )
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
        initial_dir = output_path / "initial"
        initial_dir.mkdir(exist_ok=True)
        current_spec_file = initial_dir / f"{module_name}.tla"
        
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
                    
                    # Save corrected version in attempt directory
                    corrected_module_name = self._extract_module_name(corrected_spec)
                    attempt_dir = output_path / f"attempt_{correction_attempts}"
                    attempt_dir.mkdir(exist_ok=True)
                    corrected_spec_file = attempt_dir / f"{corrected_module_name}.tla"
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
            "initial_spec_file": str(current_spec_file),
            "final_spec_file": str(final_spec_file),
            "tlc_passed": success,
            "correction_attempts": correction_attempts,
            "final_tlc_output": tlc_output if not success else "Model checking passed",
            "config_used": {
                "model": self.llm.model,
                "temperature": self.llm.temperature,
                "max_tokens": self.llm.max_tokens
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
        if args.max_attempts:
            corrector.max_correction_attempts = args.max_attempts
            logger.info(f"Using command-line override for max attempts: {args.max_attempts}")
        if args.tlc_timeout:
            corrector.tlc_timeout = args.tlc_timeout
            logger.info(f"Using command-line override for TLC timeout: {args.tlc_timeout}")
        
        # Run correction
        summary = corrector.correct_specification(args.input, args.output)
        
        # Print summary
        print("\n" + "="*60)
        print("RUNTIME CORRECTION SUMMARY")
        print("="*60)
        print(f"Input file: {summary['input_file']}")
        print(f"Output directory: {summary['output_directory']}")
        print(f"Initial specification: {summary['initial_spec_file']}")
        print(f"Final specification: {summary['final_spec_file']}")
        print(f"TLC passed: {summary['tlc_passed']}")
        print(f"Correction attempts: {summary['correction_attempts']}")
        print("="*60)
        
        if summary['tlc_passed']:
            logger.info("✅ Runtime correction completed successfully!")
            sys.exit(0)
        else:
            logger.error("❌ Runtime correction failed - specification still has errors")
            sys.exit(1)
            
    except KeyboardInterrupt:
        logger.info("Runtime correction interrupted by user")
        sys.exit(1)
    except Exception as e:
        logger.error(f"Runtime correction failed: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main() 