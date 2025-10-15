#!/usr/bin/env python3
"""
Specula CLI - Command line interface for TLA+ specification repair

Usage:
    specula fix <spec_path> --workflow <type> [options]
    specula batch <dataset_path> --workflow <type> [options]
    specula list-workflows
"""

import argparse
import sys
import json
from pathlib import Path
from typing import Optional

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from src.workflows import SimpleLoop, AgenticLoop, AgenticLoop_RAG
from src.llm.client import get_llm_client


def get_workflow_class(workflow_type: str):
    """Get workflow class by name"""
    workflows = {
        'simple': SimpleLoop,
        'agentic': AgenticLoop,
        'agentic_rag': AgenticLoop_RAG,
        # Aliases
        'simple_loop': SimpleLoop,
        'agentic_loop': AgenticLoop,
        'script': SimpleLoop,  # Deprecated
    }

    if workflow_type not in workflows:
        print(f"Error: Unknown workflow type '{workflow_type}'")
        print(f"Available workflows: {', '.join(sorted(set(workflows.keys())))}")
        sys.exit(1)

    return workflows[workflow_type]


def cmd_fix(args):
    """Fix a single TLA+ specification"""
    spec_path = Path(args.spec_path)

    # Validate spec path
    if not spec_path.exists():
        print(f"Error: File not found: {spec_path}")
        sys.exit(1)

    if spec_path.suffix != '.tla':
        print(f"Error: Not a .tla file: {spec_path}")
        sys.exit(1)

    # Create LLM client
    try:
        llm_client = get_llm_client(args.config)
        if args.verbose:
            print(f"✓ LLM client initialized")
            print(f"  Provider: {llm_client.provider}")
            print(f"  Model: {llm_client.model}")
    except Exception as e:
        print(f"Error: Failed to initialize LLM client: {e}")
        sys.exit(1)

    # Create workflow
    workflow_class = get_workflow_class(args.workflow)

    try:
        if args.workflow == 'agentic_rag':
            workflow = workflow_class(
                llm_client=llm_client,
                max_compilations=args.max_compilations,
                knowledge_base_path=args.knowledge_base
            )
        else:
            workflow = workflow_class(
                llm_client=llm_client,
                max_compilations=args.max_compilations
            )

        if args.verbose:
            print(f"✓ Workflow created: {workflow.workflow_name}")
            print(f"  Max compilations: {args.max_compilations}")
    except Exception as e:
        print(f"Error: Failed to create workflow: {e}")
        sys.exit(1)

    # Run workflow
    print(f"\n{'='*80}")
    print(f"Fixing: {spec_path}")
    print(f"Workflow: {args.workflow}")
    print(f"{'='*80}\n")

    try:
        result = workflow.fix_spec(str(spec_path))
    except Exception as e:
        print(f"\nError: Workflow failed: {e}")
        if args.verbose:
            import traceback
            traceback.print_exc()
        sys.exit(1)

    # Print result
    print_result(result, verbose=args.verbose)

    # Save result if requested
    if args.output:
        output_path = Path(args.output)
        output_path.parent.mkdir(parents=True, exist_ok=True)

        with open(output_path, 'w') as f:
            json.dump(result.to_dict(), f, indent=2)

        print(f"\n✓ Result saved to: {output_path}")

    # Exit with appropriate code
    sys.exit(0 if result.success else 1)


def cmd_batch(args):
    """Fix multiple specifications in a dataset"""
    dataset_path = Path(args.dataset_path)

    if not dataset_path.exists():
        print(f"Error: Dataset path not found: {dataset_path}")
        sys.exit(1)

    # Find all .tla files
    if dataset_path.is_file():
        spec_files = [dataset_path]
    else:
        spec_files = list(dataset_path.rglob("*.tla"))

    if not spec_files:
        print(f"Error: No .tla files found in {dataset_path}")
        sys.exit(1)

    print(f"Found {len(spec_files)} specification(s)")

    # Create LLM client
    try:
        llm_client = get_llm_client(args.config)
        print(f"✓ LLM client initialized ({llm_client.provider}/{llm_client.model})")
    except Exception as e:
        print(f"Error: Failed to initialize LLM client: {e}")
        sys.exit(1)

    # Create workflow
    workflow_class = get_workflow_class(args.workflow)

    # Process each spec
    results = []
    success_count = 0

    for i, spec_file in enumerate(spec_files, 1):
        print(f"\n{'='*80}")
        print(f"[{i}/{len(spec_files)}] Processing: {spec_file.name}")
        print(f"{'='*80}")

        try:
            if args.workflow == 'agentic_rag':
                workflow = workflow_class(
                    llm_client=llm_client,
                    max_compilations=args.max_compilations,
                    knowledge_base_path=args.knowledge_base
                )
            else:
                workflow = workflow_class(
                    llm_client=llm_client,
                    max_compilations=args.max_compilations
                )

            result = workflow.fix_spec(str(spec_file))
            results.append({
                'spec': str(spec_file),
                'result': result.to_dict()
            })

            if result.success:
                success_count += 1
                print(f"✓ Success")
            else:
                print(f"✗ Failed ({result.final_error_count} errors remaining)")

        except Exception as e:
            print(f"✗ Error: {e}")
            results.append({
                'spec': str(spec_file),
                'error': str(e)
            })

    # Summary
    print(f"\n{'='*80}")
    print(f"BATCH SUMMARY")
    print(f"{'='*80}")
    print(f"Total: {len(spec_files)}")
    print(f"Success: {success_count}")
    print(f"Failed: {len(spec_files) - success_count}")
    print(f"Success rate: {success_count/len(spec_files)*100:.1f}%")

    # Save results
    if args.output:
        output_path = Path(args.output)
        output_path.parent.mkdir(parents=True, exist_ok=True)

        with open(output_path, 'w') as f:
            json.dump({
                'total': len(spec_files),
                'success': success_count,
                'failed': len(spec_files) - success_count,
                'results': results
            }, f, indent=2)

        print(f"\n✓ Results saved to: {output_path}")

    sys.exit(0 if success_count == len(spec_files) else 1)


def cmd_list_workflows(args):
    """List available workflows"""
    print("Available workflows:")
    print()
    print("  simple (simple_loop)")
    print("    Fixed iterative flow: Compile → Read → LLM → Write")
    print()
    print("  agentic (agentic_loop)")
    print("    Agent with basic tools: compile, read, write")
    print()
    print("  agentic_rag")
    print("    Agent with RAG support: compile, read, write, rag_search")
    print()


def print_result(result, verbose=False):
    """Print workflow result"""
    print(f"\n{'='*80}")
    print("RESULT")
    print('='*80)

    # Success status
    status = "✓ SUCCESS" if result.success else "✗ FAILED"
    print(f"Status: {status}")

    # Resource usage
    print(f"\nResource Usage:")
    print(f"  Compilations: {result.compilations_used}/{result.compilations_used}")
    print(f"  LLM calls: {result.llm_calls}")
    print(f"  Tool calls: {result.tool_calls_total}")
    print(f"  Total time: {result.total_time:.2f}s")

    # Token usage
    if result.total_tokens > 0:
        print(f"\nToken Usage:")
        print(f"  Total: {result.total_tokens:,}")
        print(f"  Prompt: {result.prompt_tokens:,}")
        print(f"  Completion: {result.completion_tokens:,}")

    # Final status
    if not result.success:
        print(f"\nFinal Errors: {result.final_error_count}")
        if verbose and result.final_errors:
            print("\nError details:")
            for i, error in enumerate(result.final_errors[:5], 1):
                print(f"  {i}. {error[:150]}...")

    # Iteration history (verbose only)
    if verbose and result.attempts:
        print(f"\nIteration History:")
        for attempt in result.attempts:
            arrow = "→" if attempt.improved else "×"
            print(f"  {arrow} Iteration {attempt.iteration}: {attempt.error_count_before} → {attempt.error_count_after} errors")

    print('='*80)


def main():
    """Main CLI entry point"""
    parser = argparse.ArgumentParser(
        prog='specula',
        description='Specula - TLA+ Specification Repair Tool',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Fix a single spec with SimpleLoop
  specula fix spec.tla --workflow simple

  # Fix with AgenticLoop + RAG
  specula fix spec.tla --workflow agentic_rag

  # Batch processing
  specula batch experiments/dataset/ --workflow agentic --output results.json

  # List available workflows
  specula list-workflows
        """
    )

    subparsers = parser.add_subparsers(dest='command', help='Command to run')

    # Fix command
    fix_parser = subparsers.add_parser('fix', help='Fix a single TLA+ specification')
    fix_parser.add_argument('spec_path', help='Path to .tla file')
    fix_parser.add_argument('--workflow', '-w', required=True,
                           choices=['simple', 'agentic', 'agentic_rag'],
                           help='Workflow type')
    fix_parser.add_argument('--max-compilations', '-m', type=int, default=3,
                           help='Maximum compilation checks (default: 3)')
    fix_parser.add_argument('--output', '-o', help='Save result to JSON file')
    fix_parser.add_argument('--config', '-c', help='Path to config.yaml')
    fix_parser.add_argument('--knowledge-base', help='Path to RAG knowledge base (for agentic_rag)')
    fix_parser.add_argument('--verbose', '-v', action='store_true', help='Verbose output')

    # Batch command
    batch_parser = subparsers.add_parser('batch', help='Fix multiple specifications')
    batch_parser.add_argument('dataset_path', help='Path to dataset directory or file')
    batch_parser.add_argument('--workflow', '-w', required=True,
                             choices=['simple', 'agentic', 'agentic_rag'],
                             help='Workflow type')
    batch_parser.add_argument('--max-compilations', '-m', type=int, default=3,
                             help='Maximum compilation checks (default: 3)')
    batch_parser.add_argument('--output', '-o', help='Save results to JSON file')
    batch_parser.add_argument('--config', '-c', help='Path to config.yaml')
    batch_parser.add_argument('--knowledge-base', help='Path to RAG knowledge base (for agentic_rag)')

    # List workflows command
    list_parser = subparsers.add_parser('list-workflows', help='List available workflows')

    # Parse args
    args = parser.parse_args()

    if not args.command:
        parser.print_help()
        sys.exit(1)

    # Run command
    if args.command == 'fix':
        cmd_fix(args)
    elif args.command == 'batch':
        cmd_batch(args)
    elif args.command == 'list-workflows':
        cmd_list_workflows(args)


if __name__ == '__main__':
    main()
