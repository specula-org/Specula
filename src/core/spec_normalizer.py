#!/usr/bin/env python3
"""
TLA+ Specification Normalizer for CFA Tool Compatibility

This module normalizes TLA+ specifications to make them compatible with the CFA tool
by converting complex \/ statements to CASE statements and fixing line breaks.
"""

import os
import sys
import argparse
from pathlib import Path
from typing import Optional

# Add src to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from ..utils.config import get_config
from ..llm.client import get_llm_client
import logging


class SpecNormalizer:
    """Normalizes TLA+ specifications for CFA tool compatibility."""
    
    def __init__(self, config_path: Optional[str] = None):
        """Initialize the normalizer with configuration."""
        self.config = get_config(config_path)
        self.llm_client = get_llm_client(config_path)
        self.logger = logging.getLogger(__name__)
        
        # Load the normalization prompt from config
        prompts_dir = self.config.get('paths', {}).get('prompts_dir', 'src/prompts')
        self.prompt_path = Path(prompts_dir) / "step2_spec_normalization.txt"
        if not self.prompt_path.exists():
            raise FileNotFoundError(f"Prompt file not found: {self.prompt_path}")
        
        with open(self.prompt_path, 'r', encoding='utf-8') as f:
            self.prompt_template = f.read()
    
    def normalize_spec(self, input_spec_path: str, output_dir: str) -> bool:
        """
        Normalize a TLA+ specification for CFA tool compatibility.
        
        Args:
            input_spec_path: Path to the input TLA+ specification file
            output_dir: Directory to save the normalized specification
            
        Returns:
            bool: True if successful, False otherwise
        """
        try:
            # Read the input specification
            input_path = Path(input_spec_path)
            if not input_path.exists():
                self.logger.error(f"Input specification file not found: {input_spec_path}")
                return False
            
            with open(input_path, 'r', encoding='utf-8') as f:
                spec_content = f.read()
            
            self.logger.info(f"Processing specification: {input_spec_path}")
            
            # Prepare the prompt with the specification content
            prompt = self.prompt_template.replace("{{SPEC_CONTENT}}", spec_content)
            
            # Send to LLM for normalization
            self.logger.info("Sending specification to LLM for normalization...")
            normalized_spec = self.llm_client.get_completion(
                "You are a TLA+ specification formatter. Follow the formatting rules provided.",
                prompt
            )
            
            if not normalized_spec:
                self.logger.error("LLM returned empty response")
                return False
            
            # Create output directories
            output_path = Path(output_dir)
            output_path.mkdir(parents=True, exist_ok=True)
            
            # Get CFA input directory from config
            cfa_input_dir = Path(self.config.get('cfa', {}).get('input_dir', 'tools/cfa/input'))
            cfa_input_dir.mkdir(parents=True, exist_ok=True)
            
            # Save normalized spec to CFA input directory
            spec_filename = input_path.name
            cfa_input_path = cfa_input_dir / spec_filename
            
            with open(cfa_input_path, 'w', encoding='utf-8') as f:
                f.write(normalized_spec)
            
            self.logger.info(f"Normalized specification saved to: {cfa_input_path}")
            
            # Run CFA tools
            self.logger.info("Running CFA tool...")
            success = self._run_cfa_tool(str(cfa_input_path), output_dir)
            
            if success:
                self.logger.info(f"CFA processing completed. Output saved to: {output_dir}")
                return True
            else:
                self.logger.error("CFA tool execution failed")
                return False
                
        except Exception as e:
            self.logger.error(f"Error during specification normalization: {str(e)}")
            return False
    
    def _run_cfa_tool(self, input_spec: str, output_dir: str) -> bool:
        """
        Run the CFA tool on the normalized specification.
        
        Args:
            input_spec: Path to the normalized specification
            output_dir: Directory to save CFA output
            
        Returns:
            bool: True if successful, False otherwise
        """
        try:
            import subprocess
            
            # Prepare CFA tool command from config
            cfa_script = Path(self.config.get('cfa', {}).get('script_path', 'tools/cfa/run.sh'))
            if not cfa_script.exists():
                self.logger.error(f"CFA script not found: {cfa_script}")
                return False
            
            # Make sure the script is executable
            os.chmod(cfa_script, 0o755)
            
            # Prepare output file path
            output_path = Path(output_dir)
            spec_name = Path(input_spec).name  # Keep the full filename including .tla
            output_file = output_path / spec_name
            
            # Run CFA tool
            cmd = [str(cfa_script), input_spec, str(output_file)]
            self.logger.info(f"Running command: {' '.join(cmd)}")
            
            # Get timeout from config
            timeout = self.config.get('cfa', {}).get('timeout', 300)
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=timeout
            )
            
            if result.returncode == 0:
                self.logger.info("CFA tool executed successfully")
                self.logger.debug(f"CFA output: {result.stdout}")
                return True
            else:
                self.logger.error(f"CFA tool failed with return code: {result.returncode}")
                self.logger.error(f"CFA stderr: {result.stderr}")
                self.logger.error(f"CFA stdout: {result.stdout}")
                return False
                
        except subprocess.TimeoutExpired:
            self.logger.error("CFA tool execution timed out")
            return False
        except Exception as e:
            self.logger.error(f"Error running CFA tool: {str(e)}")
            return False


def main():
    """Main entry point for the specification normalizer."""
    parser = argparse.ArgumentParser(
        description="Normalize TLA+ specifications for CFA tool compatibility"
    )
    parser.add_argument(
        "input_spec",
        help="Path to the input TLA+ specification file"
    )
    parser.add_argument(
        "output_dir",
        help="Directory to save the CFA output (will be created if not exists)"
    )
    parser.add_argument(
        "--config",
        help="Path to configuration file",
        default=None
    )
    
    args = parser.parse_args()
    
    # Initialize normalizer
    try:
        normalizer = SpecNormalizer(args.config)
        success = normalizer.normalize_spec(args.input_spec, args.output_dir)
        
        if success:
            print(f"Specification normalization completed successfully!")
            print(f"Output saved to: {args.output_dir}")
            sys.exit(0)
        else:
            print("Specification normalization failed!")
            sys.exit(1)
            
    except Exception as e:
        print(f"Error: {str(e)}")
        sys.exit(1)


if __name__ == "__main__":
    main() 