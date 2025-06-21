#!/usr/bin/env python3
"""
TLA+ RAG Error Correction System Main Script
Integrated with action completion functionality

Usage:
    python main.py input.yaml output_dir simple
    python main.py input.yaml output_dir experiments
"""

import argparse
import logging
import sys
import os
import json
from pathlib import Path
from .core.processor import TLAProcessor

def setup_logging(level: str = "INFO"):
    """Setup logging configuration"""
    logging.basicConfig(
        level=getattr(logging, level.upper()),
        format="[%(levelname)s] %(asctime)s - %(name)s - %(message)s",
        datefmt="%Y-%m-%d %H:%M:%S"
    )

def clean_llm_response(response: str) -> str:
    """Clean LLM response code, remove markdown markers and other illegal characters
    
    Args:
        response: Raw response from LLM
        
    Returns:
        Cleaned TLA+ code
    """
    import re
    
    # Remove markdown code block markers
    # Match code blocks starting with ```tla or ```TLA or ```
    response = re.sub(r'^```(?:tla|TLA)?\s*\n?', '', response, flags=re.MULTILINE | re.IGNORECASE)
    response = re.sub(r'\n?```\s*$', '', response, flags=re.MULTILINE)
    
    # Remove other possible markdown markers
    response = re.sub(r'^`{1,2}(?:tla|TLA)?\s*', '', response, flags=re.MULTILINE | re.IGNORECASE)
    response = re.sub(r'\s*`{1,2}$', '', response, flags=re.MULTILINE)
    
    # Remove excessive empty lines (keep necessary empty lines)
    lines = response.split('\n')
    cleaned_lines = []
    prev_empty = False
    
    for line in lines:
        line = line.rstrip()  # Remove trailing whitespace
        if line == '':
            if not prev_empty:  # Keep only one consecutive empty line
                cleaned_lines.append(line)
            prev_empty = True
        else:
            cleaned_lines.append(line)
            prev_empty = False
    
    # Remove leading and trailing empty lines
    while cleaned_lines and cleaned_lines[0] == '':
        cleaned_lines.pop(0)
    while cleaned_lines and cleaned_lines[-1] == '':
        cleaned_lines.pop()
    
    cleaned_code = '\n'.join(cleaned_lines)
    
    # Validate basic TLA+ structure
    if not cleaned_code.strip():
        return ""
    
    # Ensure ends with ==== (TLA+ specification requirement)
    if not cleaned_code.rstrip().endswith('===='):
        cleaned_code = cleaned_code.rstrip() + '\n===='
    
    return cleaned_code

def parse_arguments():
    """Parse command line arguments"""
    parser = argparse.ArgumentParser(
        description="TLA+ RAG Error Correction System - Integrated with action completion functionality",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Running Mode Description:
  simple      - Simple mode: action completion + RAG correction
    * Extract TLA+ actions from YAML
    * Automatically complete variable and function definitions
    * TLA+ SANY syntax validation
    * If errors exist, use RAG+LLM for automatic correction
  experiments - Experiment mode: three experiment comparison analysis
    * Experiment 1: Baseline compilation test
    * Experiment 2: Baseline correction
    * Experiment 3: RAG correction
  generate-config - Generate trace validation configuration from TLA+ specification
    * Analyze TLA+ specification structure
    * Generate YAML configuration for trace validation
    * Output includes constants, variables, and actions

Environment Requirements:
  - Set DEEPSEEK_API_KEY environment variable to enable LLM correction functionality
  - Without API key, only action completion and validation will be performed

Examples:
  # Positional argument format
  python main.py input.yaml ./results simple
  python main.py input.yaml ./results experiments
  python main.py spec.tla config.yaml generate-config
  
  # Option argument format (compatible with old version)
  python main.py --input input.yaml --output ./results --mode simple
  python main.py --input input.yaml --output ./results --mode experiments
  python main.py --input spec.tla --output config.yaml --mode generate-config
        """
    )
    
    # Option arguments
    parser.add_argument(
        "--input", "-i",
        type=str,
        help="Input file path (YAML for simple/experiments mode, TLA+ for generate-config mode)"
    )
    
    parser.add_argument(
        "--output", "-o",
        type=str,
        help="Output path (directory for simple/experiments mode, file for generate-config mode)"
    )
    
    parser.add_argument(
        "--mode", "-m",
        type=str,
        choices=["simple", "experiments", "generate-config"],
        help="Running mode: simple (simple mode), experiments (experiment mode), or generate-config (generate trace config)"
    )
    
    parser.add_argument(
        "--config", "-c",
        type=str,
        default=None,
        help="Configuration file path (optional)"
    )
    
    parser.add_argument(
        "--log-level",
        type=str,
        choices=["DEBUG", "INFO", "WARNING", "ERROR"],
        default="INFO",
        help="Log level (default: INFO)"
    )
    
    parser.add_argument(
        "--check-env",
        action="store_true",
        help="Check environment configuration and exit"
    )
    
    # Positional arguments (optional, for simplified commands)
    parser.add_argument(
        "positional_args",
        nargs="*",
        help="Positional arguments: input_file output_dir mode"
    )
    
    return parser.parse_args()

def check_environment():
    """Check environment configuration"""
    print("[INFO] Checking environment configuration...")
    
    # Check API key
    api_key = os.getenv("DEEPSEEK_API_KEY")
    if not api_key:
        print("[ERROR] DEEPSEEK_API_KEY environment variable not set")
        print("        Please run: export DEEPSEEK_API_KEY=your_api_key")
        return False
    else:
        print(f"[OK] DEEPSEEK_API_KEY is set (length: {len(api_key)})")
    
    # Check TLA+ tools
    try:
        import subprocess
        result = subprocess.run(['tla_sany', '-help'], 
                              capture_output=True, text=True, timeout=5)
        if result.returncode == 0 or "SANY" in result.stdout or "TLA" in result.stdout:
            print("[OK] TLA+ SANY tools available")
        else:
            print("[ERROR] TLA+ SANY tools not available")
            return False
    except (subprocess.TimeoutExpired, FileNotFoundError):
        print("[ERROR] TLA+ SANY tools not installed or not in PATH")
        return False
    
    # Check required Python packages
    required_packages = [
        "openai", "yaml", "sentence_transformers", 
        "torch", "numpy", "pathlib"
    ]
    
    missing_packages = []
    for package in required_packages:
        try:
            __import__(package.replace("-", "_"))
            print(f"[OK] {package} installed")
        except ImportError:
            missing_packages.append(package)
            print(f"[ERROR] {package} not installed")
    
    if missing_packages:
        print(f"\nPlease install missing packages: pip install {' '.join(missing_packages)}")
        return False
    
    print("\n[OK] Environment check passed!")
    return True

def validate_inputs(args):
    """Validate input parameters"""
    # Handle compatibility between two parameter formats
    input_file = None
    output_dir = None
    mode = None
    
    # If positional arguments exist, use positional arguments first
    if args.positional_args and len(args.positional_args) >= 3:
        input_file = args.positional_args[0]
        output_dir = args.positional_args[1]
        mode = args.positional_args[2]
        if mode not in ['simple', 'experiments', 'generate-config']:
            raise ValueError(f"Invalid running mode: {mode}, must be 'simple', 'experiments', or 'generate-config'")
    # Otherwise use option arguments
    else:
        input_file = args.input
        output_dir = args.output
        mode = args.mode
    
    # Check required parameters
    if not input_file:
        raise ValueError("Must specify input file path (use positional arguments or --input option)")
    if not output_dir:
        raise ValueError("Must specify output directory path (use positional arguments or --output option)")
    if not mode:
        raise ValueError("Must specify running mode (use positional arguments or --mode option)")
    
    # Check input file
    input_path = Path(input_file)
    if not input_path.exists():
        raise FileNotFoundError(f"Input file does not exist: {input_file}")
    
    # Validate input file format based on mode
    if mode in ['simple', 'experiments']:
        if not input_path.suffix.lower() in ['.yaml', '.yml']:
            raise ValueError(f"Input file must be in YAML format for {mode} mode: {input_file}")
    elif mode == 'generate-config':
        if not input_path.suffix.lower() == '.tla':
            raise ValueError(f"Input file must be in TLA+ format for generate-config mode: {input_file}")
    
    # Check configuration file
    if args.config:
        config_path = Path(args.config)
        if not config_path.exists():
            raise FileNotFoundError(f"Configuration file does not exist: {args.config}")
    
    # Create output directory or ensure output file parent directory exists
    if mode in ['simple', 'experiments']:
        output_path = Path(output_dir)
        output_path.mkdir(parents=True, exist_ok=True)
    elif mode == 'generate-config':
        output_path = Path(output_dir)
        output_path.parent.mkdir(parents=True, exist_ok=True)
    
    # Store normalized parameters back to args object
    args.input_file = input_file
    args.output_dir = output_dir
    args.mode = mode
    
    print(f"[OK] Input validation passed")
    print(f"     Input file: {input_path.absolute()}")
    print(f"     Output directory: {output_path.absolute()}")
    print(f"     Running mode: {mode}")

    return input_file, output_dir, mode

def run_simple_mode(input_file: str, output_dir: str, config_path: str = None):
    """Run in simple mode"""
    logger = logging.getLogger(__name__)
    logger.info("Starting simple mode...")
    
    try:
        processor = TLAProcessor(config_path)
        stats = processor.simple_correction(input_file, output_dir)
        
        logger.info("Simple mode finished successfully.")
        logger.info(f"Statistics: {json.dumps(stats, indent=2)}")
            
    except Exception as e:
        logger.error(f"Error occurred during simple mode: {e}", exc_info=True)
        sys.exit(1)

def run_experiments_mode(input_file: str, output_dir: str, config_path: str = None):
    """Run in experiment mode"""
    logger = logging.getLogger(__name__)
    logger.info("Starting experiment mode...")
    
    try:
        processor = TLAProcessor(config_path)
        report = processor.run_experiments(input_file, output_dir)
        
        logger.info("Experiment mode finished successfully.")
        logger.info(f"Comparison Report: {json.dumps(report, indent=2)}")
        
    except Exception as e:
        logger.error(f"Error occurred during experiment mode: {e}", exc_info=True)
        sys.exit(1)

def run_generate_config_mode(input_file: str, output_file: str, config_path: str = None):
    """Run in generate-config mode"""
    logger = logging.getLogger(__name__)
    logger.info("Starting generate-config mode...")
    
    try:
        processor = TLAProcessor(config_path)
        result = processor.generate_trace_config(input_file, output_file)
        
        if result['success']:
            logger.info("Generate-config mode finished successfully.")
            logger.info(f"Generated configuration: {result['spec_name']}")
            logger.info(f"  - Constants: {result['constants_count']}")
            logger.info(f"  - Variables: {result['variables_count']}")
            logger.info(f"  - Actions: {result['actions_count']}")
            logger.info(f"  - Output file: {result['output_file']}")
        else:
            logger.error(f"Generate-config mode failed: {result['error']}")
            sys.exit(1)
        
    except Exception as e:
        logger.error(f"Error occurred during generate-config mode: {e}", exc_info=True)
        sys.exit(1)

def main():
    """Main function"""
    args = parse_arguments()
    setup_logging(args.log_level)
    
    if args.check_env:
        if check_environment():
            sys.exit(0)
        else:
            sys.exit(1)
            
    try:
        input_file, output_dir, mode = validate_inputs(args)
        
        if mode == 'simple':
            run_simple_mode(input_file, output_dir, args.config)
        elif mode == 'experiments':
            run_experiments_mode(input_file, output_dir, args.config)
        elif mode == 'generate-config':
            run_generate_config_mode(input_file, output_dir, args.config)
            
    except (ValueError, FileNotFoundError) as e:
        logging.error(f"Input error: {e}")
        sys.exit(1)

if __name__ == "__main__":
    main() 