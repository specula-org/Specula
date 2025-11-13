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
import shutil
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
            
        except subprocess.TimeoutExpired as e:
            # Timeout means TLC ran for the specified time without finding errors
            # This is considered a success for large state spaces
            output = ""
            if e.stdout:
                output += e.stdout.decode() if isinstance(e.stdout, bytes) else str(e.stdout)
            if e.stderr:
                output += e.stderr.decode() if isinstance(e.stderr, bytes) else str(e.stderr)
            return True, f"TLC ran for {timeout} seconds without finding errors (timeout reached)\n{output}"
        except Exception as e:
            return False, f"TLC execution failed: {e}"


class RuntimeCorrector:
    """Main runtime correction class"""
    
    def __init__(self, config_path: str = "config.yaml", enable_checkpoints: bool = False, cfg_file: Optional[str] = None):
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
        self.config_prompt = self._load_prompt("step2_config_generation.txt")
        self.correction_prompt = self._load_prompt("step3_runtime_correction.txt")
        summary_prompt = self._load_prompt("step1_error_correction_summary.txt")
        self.summary_prompt = summary_prompt.replace("SANY validation ", "")
        self.enable_checkpoints = enable_checkpoints
        self.cfg_file = cfg_file

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
        # Simply return the entire response, as it should contain the complete config
        return response.strip()
    
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

        # Step 1: Handle TLC configuration
        config_file = output_path / f"{module_name}.cfg"

        if self.cfg_file:
            # Use existing config file
            if not os.path.exists(self.cfg_file):
                raise FileNotFoundError(f"Specified config file not found: {self.cfg_file}")

            # Copy to output directory (only if source and destination are different)
            if os.path.abspath(self.cfg_file) != os.path.abspath(str(config_file)):
                shutil.copy(self.cfg_file, config_file)
                logger.info(f"Using existing configuration: {self.cfg_file}")
                logger.info(f"Copied to: {config_file}")
            else:
                logger.info(f"Using existing configuration in place: {self.cfg_file}")

            # Read config content for correction context
            with open(config_file, 'r', encoding='utf-8') as f:
                config_content = f.read()
        else:
            # Auto-generate config (original behavior)
            config_content = self.generate_config(spec_content)

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
        total_attempts = 0
        
        if success:
            logger.info("Specification passed TLC model checking! No corrections needed.")
            final_spec = current_spec
        else:
            logger.info("TLC found errors, starting correction process...")
            
            previous_output = tlc_output
            corrected_outputs = set()
            last_attempt_dir: Optional[Path] = None
            
            while not success:
                cycle_attempts = 0
                
                while cycle_attempts < self.max_correction_attempts and not success:
                    cycle_attempts += 1
                    total_attempts += 1
                    attempt_index = total_attempts
                    logger.info(f"Correction attempt {attempt_index} (cycle {(attempt_index-1)//self.max_correction_attempts})")
                    
                    try:
                        # Fix the errors
                        corrected_spec = self.fix_runtime_errors(current_spec, config_content, tlc_output)
                        
                        # Save corrected version in attempt directory
                        corrected_module_name = self._extract_module_name(corrected_spec)
                        attempt_dir = output_path / f"attempt_{attempt_index}"
                        attempt_dir.mkdir(exist_ok=True)
                        corrected_spec_file = attempt_dir / f"{corrected_module_name}.tla"
                        with open(corrected_spec_file, 'w', encoding='utf-8') as f:
                            f.write(corrected_spec)
                        last_attempt_dir = attempt_dir
                        
                        # Test the corrected specification
                        success, tlc_output = self.tlc.run_tlc(
                            str(corrected_spec_file), str(config_file), self.tlc_timeout
                        )
                        
                        if success:
                            logger.info(f"Correction successful after {attempt_index} attempt(s)!")
                            final_spec = corrected_spec
                            break
                        else:
                            if previous_output != tlc_output:
                                corrected_outputs.add(previous_output)
                                previous_output = tlc_output
                            if tlc_output in corrected_outputs:
                                corrected_outputs.remove(tlc_output)
                            logger.warning(f"Correction attempt {attempt_index} unsuccessful. Retrying...")
                            current_spec = corrected_spec
                    except Exception as e:
                        logger.error(f"Correction attempt {attempt_index} failed with error: {e}")
                        if cycle_attempts == self.max_correction_attempts and not self.enable_checkpoints:
                            final_spec = corrected_spec
                            break
                
                if success:
                    break
                
                if not self.enable_checkpoints:
                    logger.warning(f"Could not address all errors after {total_attempts} attempt(s)")
                    break
                
                # Construct checkpoint summary prompt
                corrected_errors_text = "\n\n---\n\n".join(
                    err.strip() for err in sorted(corrected_outputs) if err.strip()
                ) or "None"
                formatted_output = tlc_output.strip() if tlc_output.strip() else "No TLC output captured."
                prompt_content = self.summary_prompt.format(
                    errors=corrected_errors_text,
                    current_errors=formatted_output,
                    current_spec=current_spec.strip()
                )
                summary_response = self.llm.get_completion(
                    "You are a TLA+ specification expert specializing in error correction and specification refinement.",
                    prompt_content
                )
                logger.info("Final correction summary:\n%s", summary_response.strip())

                # Save checkpoint progress and error summary 
                summary_path = output_path / "runtimeFinalSummary.txt"
                existing_summary = summary_path.exists()
                with open(summary_path, 'a', encoding='utf-8') as f:
                    if existing_summary and summary_path.stat().st_size > 0:
                        f.write("\n\n" + "=" * 40 + "\n\n")
                    f.write(summary_response.strip() + "\n")
                
                if last_attempt_dir is not None and formatted_output:
                    remaining_path = last_attempt_dir / "remainingErrors.txt"
                    with open(remaining_path, 'w', encoding='utf-8') as f:
                        f.write(formatted_output)

                # HITL continuation 
                user_input = input("Correction incomplete. Continue iterating? (y/n): ").strip().lower()
                if user_input not in {"y", "yes"}:
                    logger.info(f"Failed to fix all errors after {total_attempts} attempt(s)")
                    break
                previous_output = tlc_output
            
            if not success:
                final_spec = current_spec
        
        correction_attempts = total_attempts
        
        # Save final specification in corrected_spec subdirectory
        corrected_spec_dir = output_path / "corrected_spec"
        corrected_spec_dir.mkdir(exist_ok=True)
        
        # Keep original filename
        original_filename = Path(input_spec_path).name
        final_spec_file = corrected_spec_dir / original_filename
        
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
    parser.add_argument("--interactive", action="store_true",
                        help="Enable checkpoint summaries and HITL continuation for corrections.")
    parser.add_argument("--cfg", dest="cfg_file",
                        help="Use existing TLC configuration file (.cfg)")

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
        corrector = RuntimeCorrector(args.config, enable_checkpoints=args.interactive, cfg_file=args.cfg_file)
        
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
            logger.warning("⚠️ Runtime correction could not fix all specification errors")
            sys.exit(1)
            
    except KeyboardInterrupt:
        logger.info("Runtime correction interrupted by user")
        sys.exit(1)
    except Exception as e:
        logger.error(f"Runtime correction failed: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main() 
