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

# Add src directory to Python path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'src'))

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

Environment Requirements:
  - Set DEEPSEEK_API_KEY environment variable to enable LLM correction functionality
  - Without API key, only action completion and validation will be performed

Examples:
  # Positional argument format
  python main.py input.yaml ./results simple
  python main.py input.yaml ./results experiments
  
  # Option argument format (compatible with old version)
  python main.py --input input.yaml --output ./results --mode simple
  python main.py --input input.yaml --output ./results --mode experiments
        """
    )
    
    # Option arguments
    parser.add_argument(
        "--input", "-i",
        type=str,
        help="Input YAML file path"
    )
    
    parser.add_argument(
        "--output", "-o",
        type=str,
        help="Output directory path"
    )
    
    parser.add_argument(
        "--mode", "-m",
        type=str,
        choices=["simple", "experiments"],
        help="Running mode: simple (simple mode) or experiments (experiment mode)"
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
        if mode not in ['simple', 'experiments']:
            raise ValueError(f"Invalid running mode: {mode}, must be 'simple' or 'experiments'")
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
    
    if not input_path.suffix.lower() in ['.yaml', '.yml']:
        raise ValueError(f"Input file must be in YAML format: {input_file}")
    
    # Check configuration file
    if args.config:
        config_path = Path(args.config)
        if not config_path.exists():
            raise FileNotFoundError(f"Configuration file does not exist: {args.config}")
    
    # Create output directory
    output_path = Path(output_dir)
    output_path.mkdir(parents=True, exist_ok=True)
    
    # Store normalized parameters back to args object
    args.input_file = input_file
    args.output_dir = output_dir
    args.mode = mode
    
    print(f"[OK] Input validation passed")
    print(f"     Input file: {input_path.absolute()}")
    print(f"     Output directory: {output_path.absolute()}")
    print(f"     Running mode: {mode}")

def run_simple_mode(input_file: str, output_dir: str):
    """Run simple mode: action completion + RAG correction"""
    print("[START] Running simple mode (action completion + RAG correction)...")
    
    # Import necessary modules
    from action_completion import process_actions, add_var_func
    from processing.get_errors import tla_sany
    
    output_path = Path(output_dir)
    
    # Step 1: Process actions
    print("\n[STEP 1] Processing actions from YAML file...")
    action_files = process_actions(input_file, str(output_path))
    print(f"         Generated {len(action_files)} action files")
    
    # Step 2: Complete each action file
    print("\n[STEP 2] Completing action files...")
    completed_files = []
    for action_file in action_files:
        full_path = output_path / action_file
        try:
            add_var_func(str(full_path))
            completed_files.append(str(full_path))
            print(f"         [OK] Completed: {action_file}")
        except Exception as e:
            print(f"         [ERROR] Completion failed: {action_file} - {e}")
    
    # Step 3: Validate and correct
    print("\n[STEP 3] Validating TLA+ files and performing RAG correction...")
    passed_count = 0
    failed_count = 0
    corrected_count = 0
    failed_files = []
    
    # Check if API key is available for correction
    api_key = os.getenv('DEEPSEEK_API_KEY')
    use_llm_correction = bool(api_key)
    
    if not use_llm_correction:
        print("         [WARNING] DEEPSEEK_API_KEY not set, will only validate without LLM correction")
    
    for file_path in completed_files:
        try:
            output = tla_sany(file_path)
            if "Error" not in output and "error" not in output:
                print(f"         [OK] Validation passed: {Path(file_path).name}")
                passed_count += 1
            else:
                print(f"         [ERROR] Validation failed: {Path(file_path).name}")
                
                if use_llm_correction:
                    # Try RAG correction
                    print(f"         [FIXING] Attempting RAG correction: {Path(file_path).name}")
                    try:
                        corrected = perform_rag_correction(file_path, output)
                        if corrected:
                            # After RAG correction, re-run action completion
                            print(f"         [RERUN] Re-completing: {Path(file_path).name}")
                            try:
                                add_var_func(file_path)
                                print(f"         [OK] Re-completion finished: {Path(file_path).name}")
                            except Exception as e:
                                print(f"         [WARNING] Re-completion failed: {Path(file_path).name} - {e}")
                            
                            # Re-validate corrected and completed file
                            new_output = tla_sany(file_path)
                            if "Error" not in new_output and "error" not in new_output:
                                print(f"         [OK] Correction successful: {Path(file_path).name}")
                                passed_count += 1
                                corrected_count += 1
                            else:
                                print(f"         [ERROR] Still has errors after correction: {Path(file_path).name}")
                                failed_count += 1
                                failed_files.append((Path(file_path).name, new_output))
                        else:
                            print(f"         [ERROR] Correction failed: {Path(file_path).name}")
                            failed_count += 1
                            failed_files.append((Path(file_path).name, output))
                    except Exception as e:
                        print(f"         [ERROR] Correction exception: {Path(file_path).name} - {e}")
                        failed_count += 1
                        failed_files.append((Path(file_path).name, str(e)))
                else:
                    failed_count += 1
                    failed_files.append((Path(file_path).name, output))
                    
        except Exception as e:
            print(f"         [ERROR] Validation exception: {Path(file_path).name} - {e}")
            failed_count += 1
            failed_files.append((Path(file_path).name, str(e)))
    
    # Generate statistics report
    stats = {
        'total_actions': len(action_files),
        'completed_files': len(completed_files),
        'passed_validation': passed_count,
        'failed_validation': failed_count,
        'corrected_count': corrected_count,
        'success_rate': passed_count / len(completed_files) if completed_files else 0,
        'correction_rate': corrected_count / failed_count if failed_count > 0 else 0,
        'llm_correction_enabled': use_llm_correction,
        'failed_files': [{'file': f[0], 'error': f[1]} for f in failed_files]
    }
    
    # Save statistics
    stats_file = output_path / "stats.json"
    with open(stats_file, 'w', encoding='utf-8') as f:
        json.dump(stats, f, indent=2, ensure_ascii=False)
    
    # Display results
    print(f"\n[COMPLETE] Simple mode finished!")
    print(f"           Total actions: {stats['total_actions']}")
    print(f"           Completed files: {stats['completed_files']}")
    print(f"           Validation passed: {stats['passed_validation']}")
    print(f"           Validation failed: {stats['failed_validation']}")
    if use_llm_correction:
        print(f"           RAG correction successful: {stats['corrected_count']}")
        print(f"           Correction success rate: {stats['correction_rate']:.2%}")
    print(f"           Total success rate: {stats['success_rate']:.2%}")
    print(f"           Statistics saved to: {stats_file}")
    
    return stats

def perform_rag_correction(file_path: str, error_output: str) -> bool:
    """Perform RAG correction"""
    try:
        # Import RAG and LLM related modules
        from rag.basic_retriever import ErrorRetriever
        from llm_client import get_llm_client
        
        # Read file content
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # Initialize RAG retriever - add required data_path parameter
        data_path = "/home/ubuntu/LLM_gen/spec_rag_system/knowledge_base/raw_errors/sany_errors/initial_errors.json"
        retriever = ErrorRetriever(data_path)
        
        # Retrieve relevant error information - use correct method name
        relevant_errors = retriever.search(error_output, top_k=3)
        
        # Build correction prompt
        rag_context = "\n".join([
            f"Similar error: {err['error_message']}\nSolution: {err['solution']}\n"
            for err in relevant_errors
        ])
        
        correction_prompt = f"""
You are a TLA+ expert. Please fix the TLA+ code based on the following error information and related solutions.

Current code:
{content}

Error information:
{error_output}

Related solutions:
{rag_context}

Please provide the complete corrected TLA+ code, output only the code without other explanations:
"""
        
        # Call LLM for correction
        llm_client = get_llm_client()
        system_prompt = "You are a TLA+ expert. Please fix TLA+ code based on error information and related solutions. Output only the complete corrected TLA+ code without other explanations."
        response = llm_client.get_completion(system_prompt, correction_prompt)
        
        if response and response.strip():
            # Clean LLM response code, remove markdown markers
            cleaned_code = clean_llm_response(response.strip())
            if cleaned_code:
                # Save corrected code
                with open(file_path, 'w', encoding='utf-8') as f:
                    f.write(cleaned_code)
                return True
            else:
                print(f"         [WARNING] Cleaned code is empty")
                return False
        else:
            return False
            
    except Exception as e:
        print(f"         Error during RAG correction process: {e}")
        return False

def run_experiments_mode(input_file: str, output_dir: str, config_path: str = None):
    """Run experiment mode: three experiment comparison"""
    print("[START] Running experiment mode (three experiment comparison)...")
    
    # Check if API key is set
    if not os.getenv('DEEPSEEK_API_KEY'):
        print("[ERROR] DEEPSEEK_API_KEY environment variable not set")
        print("        Experiment mode requires API key to call LLM for correction")
        print("        Please run: export DEEPSEEK_API_KEY=your_api_key")
        return None
    
    try:
        from processor import TLAProcessor
        processor = TLAProcessor(config_path)
        results = processor.run_experiments(input_file, output_dir)
        
        print(f"\n[COMPLETE] Experiment mode finished!")
        print("[RESULTS] Experiment results:")
        for key, value in results.items():
            print(f"          {key}: {value}")
        
        return results
    except Exception as e:
        print(f"[ERROR] Experiment mode execution failed: {e}")
        return None

def main():
    """Main function"""
    try:
        # Parse arguments
        args = parse_arguments()
        
        # Setup logging
        setup_logging(args.log_level)
        logger = logging.getLogger(__name__)
        
        # Check environment
        if args.check_env:
            success = check_environment()
            sys.exit(0 if success else 1)
        
        # Validate inputs
        validate_inputs(args)
        
        logger.info(f"Starting TLA+ RAG Error Correction System")
        logger.info(f"Input: {args.input_file}")
        logger.info(f"Output: {args.output_dir}")
        logger.info(f"Mode: {args.mode}")
        
        # Run based on mode
        if args.mode == "simple":
            results = run_simple_mode(args.input_file, args.output_dir)
        elif args.mode == "experiments":
            results = run_experiments_mode(args.input_file, args.output_dir, args.config)
        
        print(f"\n[OUTPUT] Output directory: {Path(args.output_dir).absolute()}")
        
    except KeyboardInterrupt:
        print("\n[WARNING] User interrupted operation")
        sys.exit(1)
    except Exception as e:
        print(f"\n[ERROR] {e}")
        logger.exception("Error occurred during execution")
        sys.exit(1)

if __name__ == "__main__":
    sys.exit(main()) 