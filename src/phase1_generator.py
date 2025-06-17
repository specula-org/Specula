#!/usr/bin/env python3
"""
Phase 1: TLA+ Specification Generator
A two-step process: Code Translation + Error Correction
"""

import os
import sys
import json
import argparse
import subprocess
import tempfile
from pathlib import Path
from typing import Dict, List, Optional, Tuple
import logging

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='[%(levelname)s] %(message)s'
)
logger = logging.getLogger(__name__)

class LLMClient:
    """Simple LLM client supporting Claude Sonnet 4"""
    
    def __init__(self, model: str = "claude-sonnet-4-20250514", api_key: Optional[str] = None):
        self.model = model
        self.api_key = api_key or os.getenv("ANTHROPIC_API_KEY")
        if not self.api_key:
            raise ValueError("Claude API key not found. Set ANTHROPIC_API_KEY environment variable.")
    
    def generate(self, prompt: str, max_tokens: int = 8192) -> str:
        """Generate response using Claude API with streaming"""
        try:
            import anthropic
        except ImportError:
            raise ImportError("anthropic package not installed. Run: pip install anthropic")
        
        client = anthropic.Anthropic(api_key=self.api_key)
        
        try:
            # Use streaming for better handling of long requests
            logger.info("Starting streaming generation...")
            response_text = ""
            
            with client.messages.stream(
                model=self.model,
                max_tokens=max_tokens,
                messages=[{"role": "user", "content": prompt}]
            ) as stream:
                for text in stream.text_stream:
                    response_text += text
                    # Show progress for long generations
                    if len(response_text) % 2000 == 0:
                        logger.debug(f"Generated {len(response_text)} characters...")
            
            logger.info(f"Streaming generation completed. Total length: {len(response_text)} characters")
            return response_text
            
        except Exception as e:
            logger.error(f"Streaming API call failed: {e}")
            # For large requests, we must use streaming, so don't fallback
            if "strongly recommended" in str(e) or "10 minutes" in str(e):
                logger.error("Large request detected. Streaming is required but failed.")
                raise RuntimeError("Streaming API failed for large request. Please try with a smaller input file or check your API configuration.")
            
            # Fallback to non-streaming only for other errors
            logger.info("Retrying with non-streaming API...")
            try:
                response = client.messages.create(
                    model=self.model,
                    max_tokens=max_tokens,
                    messages=[{"role": "user", "content": prompt}]
                )
                return response.content[0].text
            except Exception as fallback_error:
                logger.error(f"Fallback API call also failed: {fallback_error}")
                raise

class TLAValidator:
    """TLA+ SANY validator"""
    
    def __init__(self, tla_tools_path: str = "lib/tla2tools.jar"):
        self.tla_tools_path = tla_tools_path
        if not os.path.exists(tla_tools_path):
            raise FileNotFoundError(f"TLA+ tools not found at {tla_tools_path}")
    
    def validate(self, tla_file: str) -> Tuple[bool, str]:
        """Validate TLA+ specification using SANY"""
        try:
            # Run SANY validation
            cmd = [
                "java", "-cp", self.tla_tools_path,
                "tla2sany.SANY", tla_file
            ]
            
            result = subprocess.run(
                cmd, capture_output=True, text=True, timeout=30
            )
            
            success = result.returncode == 0
            output = result.stdout + result.stderr
            
            return success, output
            
        except subprocess.TimeoutExpired:
            return False, "SANY validation timed out"
        except Exception as e:
            return False, f"SANY validation failed: {e}"

class Phase1Generator:
    """Main Phase 1 generator class"""
    
    def __init__(self, model: str = "claude-3-5-sonnet-20241022"):
        self.llm = LLMClient(model=model)
        self.validator = TLAValidator()
        self.prompts_dir = Path("src/prompts")
        
        # Load prompts
        self.step1_prompt = self._load_prompt("step1_code_translation.txt")
        self.step2_prompt = self._load_prompt("step2_error_correction.txt")
    
    def _load_prompt(self, filename: str) -> str:
        """Load prompt template from file"""
        prompt_path = self.prompts_dir / filename
        if not prompt_path.exists():
            raise FileNotFoundError(f"Prompt file not found: {prompt_path}")
        
        with open(prompt_path, 'r', encoding='utf-8') as f:
            return f.read()
    
    def _read_source_code(self, input_path: str) -> str:
        """Read source code from file"""
        with open(input_path, 'r', encoding='utf-8') as f:
            return f.read()
    
    def _extract_tla_code(self, response: str) -> str:
        """Extract TLA+ code from LLM response"""
        # First, try to find code in markdown blocks
        lines = response.split('\n')
        in_code_block = False
        tla_lines = []
        
        for line in lines:
            if line.strip().startswith('```tla') or line.strip().startswith('```'):
                in_code_block = True
                continue
            elif line.strip() == '```' and in_code_block:
                in_code_block = False
                continue
            elif in_code_block:
                tla_lines.append(line)
            elif line.strip().startswith('----') and 'MODULE' in line:
                # Start of TLA+ module - collect everything until ====
                tla_lines = [line]
                for remaining_line in lines[lines.index(line)+1:]:
                    tla_lines.append(remaining_line)
                    if remaining_line.strip() == '====':
                        break
                break
        
        # If no code block found, try to extract the entire response as TLA+
        if not tla_lines:
            # Look for module start and end
            response_lines = response.split('\n')
            start_idx = -1
            end_idx = -1
            
            for i, line in enumerate(response_lines):
                if line.strip().startswith('----') and 'MODULE' in line:
                    start_idx = i
                elif line.strip() == '====' and start_idx != -1:
                    end_idx = i
                    break
            
            if start_idx != -1 and end_idx != -1:
                tla_lines = response_lines[start_idx:end_idx+1]
            else:
                # Last resort: assume the entire response is TLA+ code
                tla_lines = response_lines
        
        return '\n'.join(tla_lines)
    
    def _extract_module_name(self, tla_code: str) -> str:
        """Extract module name from TLA+ code"""
        lines = tla_code.split('\n')
        for line in lines:
            if line.strip().startswith('----') and 'MODULE' in line:
                # Extract module name from ---- MODULE ModuleName ----
                parts = line.strip().split()
                if len(parts) >= 3 and parts[1] == 'MODULE':
                    return parts[2]
        return "Generated"
    
    def step1_translate_code(self, source_code: str) -> str:
        """Step 1: Translate source code to TLA+ specification"""
        logger.info("Step 1: Translating source code to TLA+ specification...")
        
        prompt = self.step1_prompt.format(source_code=source_code)
        response = self.llm.generate(prompt)
        
        tla_spec = self._extract_tla_code(response)
        if not tla_spec.strip():
            raise ValueError("Failed to extract TLA+ specification from LLM response")
        
        return tla_spec
    
    def step2_correct_errors(self, original_spec: str, error_messages: str, 
                           knowledge_context: str = "") -> str:
        """Step 2: Correct TLA+ specification errors"""
        logger.info("Step 2: Correcting TLA+ specification errors...")
        
        prompt = self.step2_prompt.format(
            original_spec=original_spec,
            error_messages=error_messages,
            knowledge_context=knowledge_context
        )
        
        response = self.llm.generate(prompt)
        corrected_spec = self._extract_tla_code(response)
        
        if not corrected_spec.strip():
            raise ValueError("Failed to extract corrected TLA+ specification from LLM response")
        
        return corrected_spec
    
    def generate_specification(self, input_path: str, output_dir: str, 
                             max_correction_attempts: int = 3) -> Dict:
        """Generate TLA+ specification from source code"""
        logger.info(f"Generating TLA+ specification from {input_path}")
        
        # Create output directory
        output_path = Path(output_dir)
        output_path.mkdir(parents=True, exist_ok=True)
        
        # Read source code
        source_code = self._read_source_code(input_path)
        
        # Step 1: Translate code
        step1_spec = self.step1_translate_code(source_code)
        
        # Extract module name and create appropriate filename
        module_name = self._extract_module_name(step1_spec)
        step1_file = output_path / f"{module_name}.tla"
        
        # Save Step 1 output
        with open(step1_file, 'w', encoding='utf-8') as f:
            f.write(step1_spec)
        
        logger.info(f"Step 1 output saved to {step1_file}")
        
        # Validate Step 1 output
        success, error_output = self.validator.validate(str(step1_file))
        
        if success:
            logger.info("Step 1 specification passed SANY validation!")
            final_spec = step1_spec
            correction_attempts = 0
        else:
            logger.info("Step 1 specification has errors, proceeding to Step 2...")
            
            # Step 2: Correct errors
            current_spec = step1_spec
            correction_attempts = 0
            
            while correction_attempts < max_correction_attempts:
                correction_attempts += 1
                logger.info(f"Correction attempt {correction_attempts}/{max_correction_attempts}")
                
                # Load knowledge context (if available)
                knowledge_context = self._load_knowledge_context()
                
                # Correct errors
                corrected_spec = self.step2_correct_errors(
                    current_spec, error_output, knowledge_context
                )
                
                # Extract module name for corrected spec and save
                corrected_module_name = self._extract_module_name(corrected_spec)
                attempt_file = output_path / f"{corrected_module_name}_corrected.tla"
                with open(attempt_file, 'w', encoding='utf-8') as f:
                    f.write(corrected_spec)
                
                # Validate corrected specification
                success, error_output = self.validator.validate(str(attempt_file))
                
                if success:
                    logger.info(f"Correction successful after {correction_attempts} attempts!")
                    final_spec = corrected_spec
                    break
                else:
                    logger.warning(f"Correction attempt {correction_attempts} failed, trying again...")
                    current_spec = corrected_spec
            
            if not success:
                logger.error(f"Failed to correct specification after {max_correction_attempts} attempts")
                final_spec = current_spec
        
        # Save final specification
        final_module_name = self._extract_module_name(final_spec)
        final_file = output_path / f"{final_module_name}.tla"
        with open(final_file, 'w', encoding='utf-8') as f:
            f.write(final_spec)
        
        # Generate summary
        summary = {
            "input_file": input_path,
            "output_directory": str(output_path),
            "step1_file": str(step1_file),
            "final_file": str(final_file),
            "validation_passed": success,
            "correction_attempts": correction_attempts,
            "final_errors": error_output if not success else None
        }
        
        # Save summary
        summary_file = output_path / "generation_summary.json"
        with open(summary_file, 'w', encoding='utf-8') as f:
            json.dump(summary, f, indent=2)
        
        logger.info(f"Generation complete. Final specification: {final_file}")
        logger.info(f"Summary saved to: {summary_file}")
        
        return summary
    
    def _load_knowledge_context(self) -> str:
        """Load knowledge context for error correction"""
        # This could be enhanced to load from a knowledge base
        # For now, return basic TLA+ syntax reminders
        return """
Common TLA+ syntax patterns:
- Record access: record["field"] not record.field
- Sequence operations: Append(seq, elem), Head(seq), Tail(seq)
- Set operations: elem \\in set, set \\cup {elem}
- Variable updates: var' = new_value
- Unchanged variables: UNCHANGED <<var1, var2>>
- Quantifiers: \\E x \\in S : P(x), \\A x \\in S : P(x)
        """.strip()

def main():
    """Main entry point"""
    parser = argparse.ArgumentParser(description="Phase 1: TLA+ Specification Generator")
    parser.add_argument("input", help="Input source code file")
    parser.add_argument("output", help="Output directory")
    parser.add_argument("--model", default="claude-3-5-sonnet-20241022", 
                       help="LLM model to use")
    parser.add_argument("--max-attempts", type=int, default=3,
                       help="Maximum correction attempts")
    parser.add_argument("--log-level", default="INFO",
                       choices=["DEBUG", "INFO", "WARNING", "ERROR"])
    
    args = parser.parse_args()
    
    # Set log level
    logging.getLogger().setLevel(getattr(logging, args.log_level))
    
    try:
        # Create generator
        generator = Phase1Generator(model=args.model)
        
        # Generate specification
        summary = generator.generate_specification(
            args.input, args.output, args.max_attempts
        )
        
        # Print results
        print("\n" + "="*50)
        print("PHASE 1 GENERATION COMPLETE")
        print("="*50)
        print(f"Input: {summary['input_file']}")
        print(f"Output Directory: {summary['output_directory']}")
        print(f"Final Specification: {summary['final_file']}")
        print(f"Validation Passed: {summary['validation_passed']}")
        print(f"Correction Attempts: {summary['correction_attempts']}")
        
        if not summary['validation_passed']:
            print(f"Final Errors: {summary['final_errors']}")
            sys.exit(1)
        else:
            print("✅ Successfully generated valid TLA+ specification!")
            
    except Exception as e:
        logger.error(f"Generation failed: {e}")
        sys.exit(1)

if __name__ == "__main__":
    main() 