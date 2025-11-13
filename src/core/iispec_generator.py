#!/usr/bin/env python3
"""
Phase 1: TLA+ Specification Generator
A multi-step process: Code Translation + Error Correction
Can also be used to correct existing TLA+ specifications.
"""

import os
import sys
import json
import yaml
import argparse
import subprocess
from pathlib import Path
from typing import Dict, Optional, Tuple
import logging
import traceback

from ..rag.retriever import ErrorRetriever
from .autosave import AutosaveManager

class Config:
    """Configuration management class"""
    
    def __init__(self, config_path: str = "config.yaml"):
        self.config_path = config_path
        self.config = self._load_config()
        self._setup_logging()
    
    def _load_config(self) -> Dict:
        """Loads the configuration file"""
        try:
            with open(self.config_path, 'r', encoding='utf-8') as f:
                return yaml.safe_load(f)
        except FileNotFoundError:
            print(f"Configuration file {self.config_path} not found, using default settings.")
            return self._get_default_config()
        except Exception as e:
            print(f"Failed to load configuration file: {e}, using default settings.")
            return self._get_default_config()
    
    def _get_default_config(self) -> Dict:
        """Returns the default configuration"""
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
                'timeout': 30
            },
            'generation': {
                'max_correction_attempts': 3,
                'mode': 'draft-based'
            },
            'paths': {
                'prompts_dir': 'src/prompts',
                'output_dir': 'output'
            },
            'logging': {
                'level': 'INFO',
                'format': '[%(levelname)s] %(message)s'
            }
        }
    
    def _setup_logging(self):
        """Sets up logging"""
        log_config = self.config.get('logging', {})
        level = getattr(logging, log_config.get('level', 'INFO'))
        format_str = log_config.get('format', '[%(levelname)s] %(message)s')
        
        logging.basicConfig(level=level, format=format_str, force=True)
    
    def get(self, key_path: str, default=None):
        """Gets a configuration value using dot-separated keys, e.g., 'llm.model'"""
        keys = key_path.split('.')
        value = self.config
        for key in keys:
            if isinstance(value, dict) and key in value:
                value = value[key]
            else:
                return default
        return value


# Global config instance
config = Config()
logger = logging.getLogger(__name__)

# Import the unified LLM client
from ..llm.client import get_llm_client

class LLMClientWrapper:
    """Wrapper for the unified LLM client to maintain compatibility"""
    
    def __init__(self):
        self.client = get_llm_client()
        self.model = self.client.model
        self.max_tokens = self.client.max_tokens
        self.temperature = self.client.temperature
    
        logger.info(f"Initialized LLM client - Model: {self.model}, Max Tokens: {self.max_tokens}, Temperature: {self.temperature}")
    
    def generate(self, prompt: str, max_tokens: Optional[int] = None, temperature: Optional[float] = None) -> str:
        """Generate response using unified LLM client"""
        # For compatibility with existing code structure, we'll use the prompt as both system and user content
        # This may need adjustment based on your specific prompt structure
        system_prompt = "You are a helpful assistant that generates TLA+ specifications."
        
        try:
            response = self.client.get_completion(system_prompt, prompt)
            logger.info(f"Generation complete. Length: {len(response)} characters")
            return response
        except Exception as e:
            logger.error(f"Generation failed: {e}")
            raise

class TLAValidator:
    """TLA+ SANY validator"""
    
    def __init__(self):
        self.tla_tools_path = config.get('tla_validator.tools_path')
        self.timeout = config.get('tla_validator.timeout')
        
        if not os.path.exists(self.tla_tools_path):
            raise FileNotFoundError(f"TLA+ tools not found at {self.tla_tools_path}")
    
    def validate(self, tla_file: str) -> Tuple[bool, str]:
        """Validate TLA+ specification using SANY"""
        try:
            cmd = ["java", "-cp", self.tla_tools_path, "tla2sany.SANY", tla_file]
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=self.timeout)
            success = result.returncode == 0
            output = result.stdout + result.stderr
            
            return success, output
            
        except subprocess.TimeoutExpired:
            return False, f"SANY validation timed out after {self.timeout} seconds"
        except Exception as e:
            return False, f"SANY validation failed: {e}"

class Phase1Generator:
    """Main Phase 1 generator class"""
    
    def __init__(self, use_rag: bool = True, autosave: Optional[AutosaveManager] = None,
                 enable_checkpoints: bool = False):
        self.llm = LLMClientWrapper()
        self.validator = TLAValidator()
        self.prompts_dir = Path(config.get('paths.prompts_dir'))
        self.max_correction_attempts = config.get('generation.max_correction_attempts')
        self.generation_mode = config.get('generation.mode', 'direct')
        self.step2_prompt_name = "step1_error_correction.txt"
        self.step2_prompt = self._load_prompt(self.step2_prompt_name)
        self.checkpoint_summary_prompt_name = "step1_error_correction_summary.txt"
        self.checkpoint_summary_prompt = self._load_prompt(self.checkpoint_summary_prompt_name)
        self.use_rag = use_rag
        self.retriever = None
        self.autosave = autosave if autosave is not None else AutosaveManager(
            base_dir=Path(config.get('paths.output_dir', 'output')) / 'autosave',
            enabled=False,
            config_path=config.config_path
        )
        self.enable_checkpoints = enable_checkpoints
        if self.use_rag:
            logger.info("RAG-based error correction from knowledge base is enabled.")
        else:
            logger.info("RAG-based error correction is disabled.")
    
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
        lines = response.split('\n')
        in_code_block = False
        tla_lines = []
        
        for line in lines:
            if line.strip().startswith('```tla') or line.strip().startswith('```'):
                if not tla_lines:  # Start of block
                    in_code_block = True
                    continue
            elif line.strip() == '```' and in_code_block:
                break  # End of block
            if in_code_block:
                tla_lines.append(line)
        
        if not tla_lines:
            return response.strip()
        return '\n'.join(tla_lines).strip()
    
    def _extract_module_name(self, tla_code: str) -> str:
        for line in tla_code.split('\n'):
            if "---- MODULE" in line:
                try:
                    # 提取 ---- MODULE 和 ---- 之间的内容并去除空格
                    return line.split("---- MODULE")[1].split("----")[0].strip()
                except (IndexError, AttributeError):
                    continue
        return "UnnamedModule"
        
    def step0_generate_draft(self, source_code: str) -> str:
        """Step 0: Generate a natural language analysis draft"""
        logger.info("Step 0: Generating natural language analysis draft...")
        prompt_template_name = "step0_draft_generation.txt"
        prompt_template = self._load_prompt(prompt_template_name)
        prompt = prompt_template.format(source_code=source_code)
        prompt_id = self.autosave.record_prompt(
            name="step0_draft_generation",
            prompt_content=prompt
        )
        response = self.llm.generate(prompt)
        self.autosave.record_response(prompt_id, response, suffix="draft_analysis")
        return response
    
    def step1_translate_code(self, source_code: str, draft_analysis: str = "") -> str:
        """Step 1: Translate source code to a TLA+ specification"""
        logger.info("Step 1: Translating source code to TLA+ specification...")
        if self.generation_mode in ["draft-based", "existing-draft"]:
            prompt_template_name = "step1_code_translation_with_draft.txt"
            prompt_template = self._load_prompt(prompt_template_name)
            prompt = prompt_template.format(source_code=source_code, draft_analysis=draft_analysis)
        else:
            prompt_template_name = "step1_code_translation.txt"
            prompt_template = self._load_prompt(prompt_template_name)
            prompt = prompt_template.format(source_code=source_code)
        prompt_id = self.autosave.record_prompt(
            name="step1_code_translation",
            prompt_content=prompt
        )
        response = self.llm.generate(prompt)
        self.autosave.record_response(prompt_id, response, suffix="tla_translation")
        return self._extract_tla_code(response)
    
    def step2_correct_errors(self, original_spec: str, error_messages: str,
                             knowledge_context: str = "", attempt_label: Optional[str] = None) -> str:
        """Step 2: Correct TLA+ specification based on SANY errors"""
        logger.info("Step 2: Correcting TLA+ specification errors...")
        
        prompt = self.step2_prompt.format(
            original_spec=original_spec,
            error_messages=error_messages,
            knowledge_context=knowledge_context
        )
        prompt_id = self.autosave.record_prompt(
            name=f"step2_correction_{attempt_label or 'attempt'}",
            prompt_content=prompt
        )
        
        try:
            corrected_response = self.llm.generate(prompt)
            self.autosave.record_response(prompt_id, corrected_response, suffix=f"correction_{attempt_label or 'attempt'}")
            corrected_spec = self._extract_tla_code(corrected_response)
            
            if not corrected_spec.strip():
                raise ValueError("Failed to extract corrected TLA+ specification from LLM response")
            
            return corrected_spec
        except Exception as e:
            logger.error(f"Correction failed: {e}\n{traceback.format_exc()}")
            raise
    
    def _run_correction_loop(
        self,
        initial_spec: str,
        initial_errors: str,
        output_path: Path,
        start_attempt: int = 0
    ) -> Tuple[str, bool, int, str]:
        """Runs the iterative correction loop for a given spec."""
        current_spec = initial_spec
        error_output = initial_errors
        correction_attempts = 0
        previous_error_output = initial_errors 
        corrected_errors = set()
        last_attempt_dir: Optional[Path] = None
        last_attempt_file: Optional[Path] = None

        if self.use_rag and self.retriever is None:
            try:
                error_db_path = config.get('paths.knowledge_base', 'src/rag/initial_errors.json')
                self.retriever = ErrorRetriever(data_path=error_db_path)
                logger.info("RAG error retriever initialized successfully.")
            except Exception as e:
                logger.warning(f"Failed to initialize RAG error retriever: {e}. Proceeding without RAG.")
                self.use_rag = False
        
        while correction_attempts < self.max_correction_attempts:
            correction_attempts += 1
            attempt_index = start_attempt + correction_attempts
            logger.info(f"Correction attempt {attempt_index} (cycle {attempt_index//self.max_correction_attempts})")
            if self.enable_checkpoints and error_output:
                logger.info("Checkpoint %d error output:\n%s", attempt_index, error_output.strip())
            
            knowledge_context = self._load_knowledge_context()
            
            if self.use_rag and self.retriever:
                try:
                    logger.info("Retrieving similar errors from the knowledge base...")
                    retrieved_errors = self.retriever.search(error_output, top_k=3)
                    if retrieved_errors:
                        retrieved_context = "\n\nHere are some similar errors and their solutions from our knowledge base:\n"
                        for err in retrieved_errors:
                            retrieved_context += f"- Error: {err['error_message']}\\n  Solution: {err['solution']}\\n"
                        knowledge_context += retrieved_context
                        logger.info(f"Found {len(retrieved_errors)} relevant solutions in the knowledge base.")
                    else:
                        logger.info("No similar errors found in the knowledge base.")
                except Exception as e:
                    logger.warning(f"Error retrieval failed: {e}. Proceeding without retrieved context.")
            
            attempt_label = f"{attempt_index}"
            corrected_spec = self.step2_correct_errors(
                current_spec,
                error_output,
                knowledge_context,
                attempt_label=attempt_label
            )
            
            module_name = self._extract_module_name(corrected_spec)
            attempt_dir = output_path / f"attempt_{attempt_index}"
            attempt_dir.mkdir(exist_ok=True)
            attempt_file = attempt_dir / f"{module_name}.tla"
            with open(attempt_file, 'w', encoding='utf-8') as f:
                f.write(corrected_spec)
            last_attempt_dir = attempt_dir
            last_attempt_file = attempt_file
            
            success, error_output = self.validator.validate(str(attempt_file))
            if success:
                logger.info(f"Correction successful after {attempt_index} total attempt(s)!")
                return corrected_spec, True, attempt_index, ""
            else:
                if previous_error_output != error_output:
                    corrected_errors.add(previous_error_output)
                    previous_error_output = error_output
                logger.warning(f"Correction attempt {attempt_index} failed. Retrying...")
                current_spec = corrected_spec
        
        logger.error(f"Failed to correct the specification after {self.max_correction_attempts} attempts this cycle.")
        if self.enable_checkpoints and last_attempt_file:
            _, final_errors = self.validator.validate(str(last_attempt_file))
            error_output = final_errors

            # save recent iteration's errors
            if error_output:
                summary_file = last_attempt_dir / "remainingErrors.txt"
                with open(summary_file, 'w', encoding='utf-8') as f:
                    f.write(error_output)

            # prompt LLM for summary of this cycle's corrections
            corrected_errors_text = "\n\n".join(
                err.strip() for err in corrected_errors if err.strip()
            ) or "None"
            prompt_content = self.checkpoint_summary_prompt.format(
                errors=corrected_errors_text,
                current_errors=error_output.strip(),
                current_spec=current_spec.strip()
            )
            summary_response = self.llm.generate(prompt_content)

            # log and display final summary
            logger.info(f"Final correction summary (cycle {(attempt_index-1)//self.max_correction_attempts}):\n{summary_response.strip()}")
            summary_path = output_path / "correctionSummary.txt"
            existing = summary_path.exists()
            with open(summary_path, 'a', encoding='utf-8') as f:
                if existing and summary_path.stat().st_size > 0:
                    f.write("\n\n" + "=" * 40 + "\n\n")
                f.write(summary_response.strip() + "\n")

            # HITL: wait for user decision to start or stop
            user_input = input("Correction failed. Continue iterating? (y/n): ").strip().lower()
            if user_input in {"y", "yes"}:
                return self._run_correction_loop(
                    current_spec,
                    error_output,
                    output_path,
                    start_attempt=start_attempt + correction_attempts
                )
            else:
                return current_spec, False, attempt_index, error_output

        # If checkpoints are disabled, return the last attempt result
        return current_spec, False, start_attempt + correction_attempts, error_output


    def generate_specification(self, input_path: str, output_dir: str) -> Dict:
        """Generate TLA+ specification from source code"""
        logger.info(f"Generating TLA+ specification from {input_path}")
        output_path = Path(output_dir)
        output_path.mkdir(parents=True, exist_ok=True)
        source_code = self._read_source_code(input_path)
        
        draft_analysis = ""
        if self.generation_mode == "draft-based":
            draft_analysis = self.step0_generate_draft(source_code)
            draft_file = output_path / "draft_analysis.txt"
            with open(draft_file, 'w', encoding='utf-8') as f:
                f.write(draft_analysis)
            logger.info(f"Draft analysis saved to {draft_file}")
            self.autosave.record_artifact("draft_analysis", draft_file)
        
        step1_spec = self.step1_translate_code(source_code, draft_analysis)
        module_name = self._extract_module_name(step1_spec)
        step1_file = output_path / f"{module_name}.tla"
        with open(step1_file, 'w', encoding='utf-8') as f:
            f.write(step1_spec)
        
        logger.info(f"Step 1 output saved to {step1_file}")
        self.autosave.record_artifact("step1_translation", step1_file)
        
        success, error_output = self.validator.validate(str(step1_file))
        if success:
            logger.info("Step 1 specification passed SANY validation!")
            final_spec = step1_spec
            correction_attempts = 0
        else:
            logger.info("Step 1 specification has errors, entering Step 2...")
            final_spec, success, correction_attempts, error_output = self._run_correction_loop(
                step1_spec, error_output, output_path
            )
        
        final_module_name = self._extract_module_name(final_spec)
        
        # If corrections were made, save to corrected_spec directory
        if correction_attempts > 0:
            corrected_dir = output_path / "corrected_spec"
            corrected_dir.mkdir(exist_ok=True)
            final_file = corrected_dir / f"{final_module_name}.tla"
        else:
            final_file = output_path / f"{final_module_name}.tla"
            
        if str(step1_file) != str(final_file):
            with open(final_file, 'w', encoding='utf-8') as f:
                f.write(final_spec)
        self.autosave.record_artifact("final_spec", final_file)
        
        summary = self._create_summary(
            input_path=input_path, output_path=output_path, generation_mode=self.generation_mode,
            step1_file=step1_file, final_file=final_file, success=success,
            correction_attempts=correction_attempts, final_errors=error_output
        )
        self._save_summary(summary, output_path)
        self.autosave.set_summary(summary)
        self.autosave.record_artifact("generation_summary", output_path / "generation_summary.json")
        logger.info(f"Generation complete. Final specification: {final_file}")
        return summary
    
    def generate_draft_only(self, input_path: str, output_dir: str) -> Dict:
        """Generate only natural language draft analysis"""
        logger.info(f"Generating draft analysis only from {input_path}")
        output_path = Path(output_dir)
        output_path.mkdir(parents=True, exist_ok=True)
        source_code = self._read_source_code(input_path)
        
        draft_analysis = self.step0_generate_draft(source_code)
        draft_file = output_path / "draft_analysis.txt"
        with open(draft_file, 'w', encoding='utf-8') as f:
            f.write(draft_analysis)
        logger.info(f"Draft analysis saved to {draft_file}")
        self.autosave.record_artifact("draft_analysis", draft_file)
        
        summary = {
            "input_file": input_path,
            "output_directory": str(output_path),
            "generation_mode": "draft-only",
            "draft_file": str(draft_file),
            "validation_passed": None,
            "correction_attempts": 0,
            "final_errors": None,
            "config_used": {
                "model": self.llm.model,
                "max_tokens": self.llm.max_tokens,
                "temperature": self.llm.temperature
            }
        }
        self._save_summary(summary, output_path)
        self.autosave.set_summary(summary)
        self.autosave.record_artifact("generation_summary", output_path / "generation_summary.json")
        logger.info(f"Draft generation complete. Draft file: {draft_file}")
        return summary
    
    def generate_from_existing_draft(self, input_path: str, draft_path: str, output_dir: str) -> Dict:
        """Generate TLA+ specification using existing draft analysis"""
        logger.info(f"Generating TLA+ specification from {input_path} using existing draft {draft_path}")
        output_path = Path(output_dir)
        output_path.mkdir(parents=True, exist_ok=True)
        
        source_code = self._read_source_code(input_path)
        
        try:
            with open(draft_path, 'r', encoding='utf-8') as f:
                draft_analysis = f.read()
        except FileNotFoundError:
            logger.error(f"Draft file not found: {draft_path}")
            raise
        self.autosave.record_artifact("input_draft", Path(draft_path))
        
        step1_spec = self.step1_translate_code(source_code, draft_analysis)
        module_name = self._extract_module_name(step1_spec)
        step1_file = output_path / f"{module_name}.tla"
        with open(step1_file, 'w', encoding='utf-8') as f:
            f.write(step1_spec)

        logger.info(f"Step 1 output saved to {step1_file}")
        self.autosave.record_artifact("step1_translation", step1_file)
        
        success, error_output = self.validator.validate(str(step1_file))
        if success:
            logger.info("Step 1 specification passed SANY validation!")
            final_spec = step1_spec
            correction_attempts = 0
        else:
            logger.info("Step 1 specification has errors, entering Step 2...")
            final_spec, success, correction_attempts, error_output = self._run_correction_loop(
                step1_spec, error_output, output_path
            )
        
        final_module_name = self._extract_module_name(final_spec)
        
        # If corrections were made, save to corrected_spec directory
        if correction_attempts > 0:
            corrected_dir = output_path / "corrected_spec"
            corrected_dir.mkdir(exist_ok=True)
            final_file = corrected_dir / f"{final_module_name}.tla"
        else:
            final_file = output_path / f"{final_module_name}.tla"
            
        if str(step1_file) != str(final_file):
            with open(final_file, 'w', encoding='utf-8') as f:
                f.write(final_spec)
        self.autosave.record_artifact("final_spec", final_file)
        
        summary = self._create_summary(
            input_path=input_path, output_path=output_path, generation_mode="existing-draft",
            step1_file=step1_file, final_file=final_file, success=success,
            correction_attempts=correction_attempts, final_errors=error_output
        )
        summary["draft_file"] = draft_path
        self._save_summary(summary, output_path)
        self.autosave.set_summary(summary)
        self.autosave.record_artifact("generation_summary", output_path / "generation_summary.json")
        logger.info(f"Generation complete. Final specification: {final_file}")
        return summary

    def correct_specification(self, input_spec_path: str, output_dir: str) -> Dict:
        """Correct an existing TLA+ specification"""
        logger.info(f"Attempting to correct existing TLA+ specification: {input_spec_path}")
        output_path = Path(output_dir)
        output_path.mkdir(parents=True, exist_ok=True)
        
        try:
            initial_spec = self._read_source_code(input_spec_path)
        except FileNotFoundError:
            logger.error(f"Input specification file not found: {input_spec_path}")
            sys.exit(1)
        self.autosave.record_artifact("input_spec", Path(input_spec_path))
        
        module_name = self._extract_module_name(initial_spec)
        initial_dir = output_path / "initial"
        initial_dir.mkdir(exist_ok=True)
        initial_file = initial_dir / f"{module_name}.tla"
        with open(initial_file, 'w', encoding='utf-8') as f:
            f.write(initial_spec)
        self.autosave.record_artifact("initial_spec", initial_file)
        
        success, error_output = self.validator.validate(str(initial_file))
        if success:
            logger.info("Input specification already passed SANY validation. No correction needed.")
            final_spec = initial_spec
            correction_attempts = 0
        else:
            logger.info("Input specification has errors, starting correction process...")
            final_spec, success, correction_attempts, error_output = self._run_correction_loop(
                initial_spec, error_output, output_path
            )
        
        final_module_name = self._extract_module_name(final_spec)
        
        # If corrections were made, save to corrected_spec directory
        if correction_attempts > 0:
            corrected_dir = output_path / "corrected_spec"
            corrected_dir.mkdir(exist_ok=True)
            final_file = corrected_dir / f"{final_module_name}.tla"
        else:
            final_file = output_path / f"{final_module_name}.tla"
            
        with open(final_file, 'w', encoding='utf-8') as f:
            f.write(final_spec)
        self.autosave.record_artifact("final_spec", final_file)

        summary = self._create_summary(
            input_path=input_spec_path, output_path=output_path, generation_mode="correct-only",
            step1_file=initial_file, final_file=final_file, success=success,
            correction_attempts=correction_attempts, final_errors=error_output
        )
        self._save_summary(summary, output_path)
        self.autosave.set_summary(summary)
        self.autosave.record_artifact("generation_summary", output_path / "generation_summary.json")
        logger.info(f"Correction complete. Final specification: {final_file}")
        return summary
    
    def _create_summary(self, **kwargs) -> Dict:
        """Creates the generation summary dictionary."""
        summary = {
            "input_file": kwargs.get("input_path"),
            "output_directory": str(kwargs.get("output_path")),
            "generation_mode": kwargs.get("generation_mode"),
            "initial_file": str(kwargs.get("step1_file")),
            "final_file": str(kwargs.get("final_file")),
            "validation_passed": kwargs.get("success"),
            "correction_attempts": kwargs.get("correction_attempts"),
            "final_errors": kwargs.get("final_errors") if not kwargs.get("success") else None,
            "config_used": {
                "model": self.llm.model,
                "max_tokens": self.llm.max_tokens,
                "temperature": self.llm.temperature
            }
        }
        if summary["generation_mode"] == "draft-based":
            summary["draft_file"] = str(kwargs.get("output_path") / "draft_analysis.txt")
        return summary
    
    def _save_summary(self, summary: Dict, output_path: Path):
        """Saves the summary to a JSON file."""
        summary_file = output_path / "generation_summary.json"
        with open(summary_file, 'w', encoding='utf-8') as f:
            json.dump(summary, f, indent=2, ensure_ascii=False)
        logger.info(f"Summary saved to: {summary_file}")
    
    def _load_knowledge_context(self) -> str:
        """Load knowledge context for error correction"""
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
    parser = argparse.ArgumentParser(
        description="Phase 1: TLA+ Specification Generator and Corrector",
        formatter_class=argparse.RawTextHelpFormatter
    )
    parser.add_argument("input", help="Input file path (source code or TLA+ spec)")
    parser.add_argument("output", help="Output directory path")
    parser.add_argument("--draft", help="Path to existing draft file (required for existing-draft mode)")
    parser.add_argument("--config", default="config.yaml", help="Configuration file path")
    parser.add_argument("--model", help="Override LLM model from config")
    parser.add_argument("--max-tokens", type=int, help="Override max_tokens from config")
    parser.add_argument("--temperature", type=float, help="Override temperature from config")
    parser.add_argument("--no-rag", action="store_true", help="Disable RAG-based error correction from the knowledge base.")
    parser.add_argument("--mode", choices=["direct", "draft-based", "correct-only", "draft-only", "existing-draft"],
                        help="""Generation mode:
- direct: Source code -> TLA+
- draft-based: Source code -> Draft -> TLA+
- correct-only: TLA+ -> Corrected TLA+
- draft-only: Source code -> Draft only
- existing-draft: Existing Draft + Source code -> TLA+""")
    parser.add_argument("--log-level", choices=["DEBUG", "INFO", "WARNING", "ERROR"],
                        help="Override log level from config")
    parser.add_argument("--autosave", action="store_true",
                        help="Enable autosaving of prompts, logs, and outputs under output/autosave/")
    parser.add_argument("--interactive", action="store_true",
                        help="Enable HITL checkpoints and logging summaries for correction attempts.")
    args = parser.parse_args()

    autosave_manager: Optional[AutosaveManager] = None
    summary: Optional[Dict] = None
    exit_code = 0
    error_message: Optional[str] = None

    try:
        global config
        if args.config != "config.yaml":
            config = Config(args.config)

        if args.log_level:
            logging.getLogger().setLevel(getattr(logging, args.log_level))

        use_rag = not args.no_rag
        mode = args.mode or config.get('generation.mode', 'direct')

        autosave_manager = AutosaveManager(
            base_dir=Path(config.get('paths.output_dir', 'output')) / 'autosave',
            enabled=args.autosave,
            config_path=config.config_path
        )
        autosave_manager.start_session(input_path=args.input, output_dir=args.output)
        autosave_manager.snapshot_config(config.config, label="base", source_path=config.config_path)
        if autosave_manager.enabled:
            autosave_manager.metadata["use_rag"] = use_rag

        generator = Phase1Generator(use_rag=use_rag, autosave=autosave_manager, enable_checkpoints=args.interactive)

        # Apply command-line overrides
        if args.model:
            generator.llm.model = args.model
            logger.info(f"Using command-line override for model: {args.model}")
            autosave_manager.record_override("model", args.model)
        if args.max_tokens is not None:
            generator.llm.max_tokens = args.max_tokens
            logger.info(f"Using command-line override for max_tokens: {args.max_tokens}")
            autosave_manager.record_override("max_tokens", args.max_tokens)
        if args.temperature is not None:
            generator.llm.temperature = args.temperature
            logger.info(f"Using command-line override for temperature: {args.temperature}")
            autosave_manager.record_override("temperature", args.temperature)

        # Determine mode from args or config
        generator.generation_mode = mode
        logger.info(f"Running in '{mode}' mode.")

        # Execute the chosen mode
        if mode == 'correct-only':
            if not args.input.endswith('.tla'):
                raise ValueError("Input for 'correct-only' mode must be a .tla file.")
            summary = generator.correct_specification(args.input, args.output)
        elif mode == 'draft-only':
            summary = generator.generate_draft_only(args.input, args.output)
        elif mode == 'existing-draft':
            if not args.draft:
                raise ValueError("--draft parameter is required for 'existing-draft' mode.")
            if not os.path.exists(args.draft):
                raise FileNotFoundError(f"Draft file not found: {args.draft}")
            summary = generator.generate_from_existing_draft(args.input, args.draft, args.output)
        else:
            summary = generator.generate_specification(args.input, args.output)

    except Exception as e:
        exit_code = 1
        error_message = f"An unexpected error occurred: {e}\n{traceback.format_exc()}"
        logger.error(error_message)
    finally:
        if autosave_manager:
            autosave_manager.finalize(summary=summary, exit_code=exit_code, error=error_message)

    if exit_code != 0:
        sys.exit(exit_code)

if __name__ == "__main__":
    main() 
