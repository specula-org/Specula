#!/usr/bin/env python3
"""
Flexible workflow comparison script

This script allows you to compare any combination of workflows on a diverse set of specs.

Usage examples:
    # Compare SimpleLoop and SimpleLoop_RAG
    python run_workflow_comparison.py --workflows SimpleLoop SimpleLoop_RAG

    # Compare all four workflows
    python run_workflow_comparison.py --workflows SimpleLoop SimpleLoop_RAG AgenticLoop AgenticLoop_RAG

    # Test only SimpleLoop_RAG
    python run_workflow_comparison.py --workflows SimpleLoop_RAG -n 10
"""

import sys
import json
import time
import random
import os
import io
from pathlib import Path
from datetime import datetime
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor, as_completed
from threading import Lock
from contextlib import redirect_stdout, redirect_stderr

# Add project root to path
sys.path.insert(0, str(Path(__file__).parent.parent.parent))

from src.workflows import SimpleLoop, SimpleLoop_RAG, AgenticLoop, AgenticLoop_RAG
from src.llm.client import get_llm_client

# Global lock for thread-safe printing
print_lock = Lock()

# Workflow registry
AVAILABLE_WORKFLOWS = {
    'SimpleLoop': SimpleLoop,
    'SimpleLoop_RAG': SimpleLoop_RAG,
    'AgenticLoop': AgenticLoop,
    'AgenticLoop_RAG': AgenticLoop_RAG,
}


def collect_diverse_specs(dataset_path, num_specs=100, exclude_systems=None, prefer_systems=None):
    """
    Intelligently sample specs from different systems and models

    Strategy:
    1. Group specs by (system, model)
    2. Optionally filter by system preferences
    3. Sample evenly across groups to ensure diversity

    Args:
        exclude_systems: List of systems to exclude (e.g., ['redisraft'])
        prefer_systems: List of systems to prefer (e.g., ['mutex', 'dqueue'])
    """
    dataset = Path(dataset_path)

    if exclude_systems is None:
        exclude_systems = []
    if prefer_systems is None:
        prefer_systems = []

    # Group all specs by (system, model)
    groups = defaultdict(list)
    preferred_groups = defaultdict(list)
    excluded_count = 0

    all_specs = list(dataset.rglob("*.tla"))

    for spec_path in all_specs:
        parts = spec_path.parts
        try:
            # Find 'dataset' in path
            dataset_idx = parts.index('dataset')
            system = parts[dataset_idx + 1]
            model = parts[dataset_idx + 2]

            # Skip test/debug specs
            if system in ['test', 'debug']:
                continue

            # Skip excluded systems
            if system in exclude_systems:
                excluded_count += 1
                continue

            # Separate preferred from normal
            if system in prefer_systems:
                preferred_groups[(system, model)].append(spec_path)
            else:
                groups[(system, model)].append(spec_path)

        except (ValueError, IndexError):
            continue

    if excluded_count > 0:
        print(f"ℹ️  Excluded {excluded_count} specs from systems: {exclude_systems}")

    # Print distribution
    print(f"\n{'='*80}")
    print("DATASET DISTRIBUTION")
    print(f"{'='*80}")
    print(f"{'System':<15} {'Model':<15} {'Count':<10}")
    print(f"{'-'*15} {'-'*15} {'-'*10}")

    total_available = 0
    for (system, model), specs in sorted(groups.items()):
        print(f"{system:<15} {model:<15} {len(specs):<10}")
        total_available += len(specs)

    print(f"{'-'*15} {'-'*15} {'-'*10}")
    print(f"{'TOTAL':<15} {'':<15} {total_available:<10}")

    # Stratified sampling
    print(f"\n{'='*80}")
    print(f"SAMPLING STRATEGY: Stratified sampling for diversity")
    print(f"{'='*80}")

    selected_specs = []
    group_list = list(groups.items())

    # Calculate how many specs per group
    num_groups = len(group_list)
    specs_per_group = num_specs // num_groups
    remainder = num_specs % num_groups

    print(f"Number of groups: {num_groups}")
    print(f"Base specs per group: {specs_per_group}")
    print(f"Extra specs to distribute: {remainder}")

    sampling_info = []

    for (system, model), specs in group_list:
        # Take base amount
        group_sample = specs_per_group

        # Add one extra to some groups
        if remainder > 0:
            group_sample += 1
            remainder -= 1

        # Can't take more than available
        group_sample = min(group_sample, len(specs))

        # Random sample from this group
        sampled = random.sample(specs, group_sample)
        selected_specs.extend(sampled)

        sampling_info.append({
            'system': system,
            'model': model,
            'available': len(specs),
            'sampled': group_sample
        })

    # Print sampling summary
    print(f"\n{'System':<15} {'Model':<15} {'Available':<10} {'Sampled':<10}")
    print(f"{'-'*15} {'-'*15} {'-'*10} {'-'*10}")
    for info in sampling_info:
        print(f"{info['system']:<15} {info['model']:<15} {info['available']:<10} {info['sampled']:<10}")

    print(f"\n✓ Sampled {len(selected_specs)} specs total")

    return selected_specs


def run_workflow_on_spec(workflow_class, spec_path, llm_client, max_compilations=3, knowledge_base=None):
    """Run a single workflow on a single spec"""
    try:
        # Check if workflow needs knowledge base
        needs_kb = workflow_class.__name__ in ['AgenticLoop_RAG', 'SimpleLoop_RAG']

        if needs_kb:
            workflow = workflow_class(
                llm_client=llm_client,
                max_compilations=max_compilations,
                knowledge_base_path=knowledge_base
            )
        else:
            workflow = workflow_class(
                llm_client=llm_client,
                max_compilations=max_compilations
            )

        start = time.time()
        result = workflow.fix_spec(str(spec_path))
        elapsed = time.time() - start

        return {
            'success': result.success,
            'compilations_used': result.compilations_used,
            'iterations': result.iterations,
            'llm_calls': result.llm_calls,
            'tool_calls': result.tool_calls_total,
            'time': result.total_time,
            'tokens': result.total_tokens,
            'final_error_count': result.final_error_count,
            'error': None
        }

    except Exception as e:
        return {
            'success': False,
            'error': str(e)
        }


def process_single_spec(spec_path, spec_index, total_specs, max_compilations,
                       knowledge_base, dataset_path, workflows_to_test):
    """Process a single spec with selected workflows (runs in parallel)"""

    # Create spec identifier
    if dataset_path:
        try:
            spec_display = str(spec_path.relative_to(dataset_path))
        except ValueError:
            spec_display = spec_path.name
    else:
        spec_display = spec_path.name

    spec_result = {
        'spec': str(spec_path),
        'spec_name': spec_display,
        'workflows': {}
    }

    # Get LLM client (each thread gets its own or shares)
    llm_client = get_llm_client()

    # Run each workflow sequentially for this spec (suppress output)
    for workflow_name, workflow_class in workflows_to_test:
        # Redirect output to string buffer (thread-safe)
        stdout_buffer = io.StringIO()
        stderr_buffer = io.StringIO()

        with redirect_stdout(stdout_buffer), redirect_stderr(stderr_buffer):
            result = run_workflow_on_spec(
                workflow_class=workflow_class,
                spec_path=spec_path,
                llm_client=llm_client,
                max_compilations=max_compilations,
                knowledge_base=knowledge_base
            )
        spec_result['workflows'][workflow_name] = result

    return spec_result, spec_index


def run_comparison_experiment(specs, workflows_to_test, max_compilations=3,
                              knowledge_base=None, dataset_path=None, max_workers=4):
    """Run selected workflows on all specs in parallel"""

    # Initialize LLM client
    print(f"\n{'='*80}")
    print("INITIALIZING")
    print(f"{'='*80}")

    llm_client = get_llm_client()
    print(f"✓ LLM client: {llm_client.provider}/{llm_client.model}")
    print(f"✓ Parallel workers: {max_workers}")
    print(f"✓ Total specs to process: {len(specs)}")
    print(f"✓ Workflows to test: {', '.join([name for name, _ in workflows_to_test])}")

    print(f"\n{'='*80}")
    print("RUNNING EXPERIMENT (parallel processing)")
    print(f"{'='*80}\n")

    # Results storage (maintain order)
    comparison_results = [None] * len(specs)
    completed = 0
    total = len(specs)

    start_time = time.time()

    # Process specs in parallel
    with ThreadPoolExecutor(max_workers=max_workers) as executor:
        # Submit all tasks
        future_to_spec = {
            executor.submit(
                process_single_spec,
                spec_path,
                i,
                total,
                max_compilations,
                knowledge_base,
                dataset_path,
                workflows_to_test
            ): i
            for i, spec_path in enumerate(specs)
        }

        # Process completed tasks
        for future in as_completed(future_to_spec):
            try:
                spec_result, spec_index = future.result()
                comparison_results[spec_index] = spec_result
                completed += 1

                # Calculate stats
                elapsed = time.time() - start_time
                avg_time = elapsed / completed
                eta = avg_time * (total - completed)

                # Show progress
                progress_bar = '█' * int(50 * completed / total) + '░' * (50 - int(50 * completed / total))

                with print_lock:
                    print(f"\r[{progress_bar}] {completed}/{total} specs | "
                          f"Elapsed: {elapsed:.0f}s | ETA: {eta:.0f}s | "
                          f"Avg: {avg_time:.1f}s/spec", end='', flush=True)

            except Exception as e:
                with print_lock:
                    print(f"\n✗ Error processing spec: {e}")

    print("\n")  # New line after progress bar

    total_time = time.time() - start_time
    print(f"✓ Completed all specs in {total_time:.0f}s ({total_time/60:.1f} minutes)")
    print(f"  Average: {total_time/total:.1f}s per spec")

    return comparison_results


def analyze_comparison(comparison_results, workflow_names):
    """Analyze comparison results"""

    analysis = {
        'total_specs': len(comparison_results),
        'workflow_stats': {},
        'agreement': {},
        'unique_successes': {},
        'spec_details': []
    }

    # Initialize stats
    for wf in workflow_names:
        analysis['workflow_stats'][wf] = {
            'success': 0,
            'failed': 0,
            'success_rate': 0,
            'avg_compilations': 0,
            'avg_time': 0,
            'avg_llm_calls': 0
        }
        analysis['unique_successes'][wf] = []

    # Count how many workflows in total
    num_workflows = len(workflow_names)

    # Initialize agreement counters
    for i in range(num_workflows + 1):
        analysis['agreement'][f'{i}_success'] = 0

    # Analyze each spec
    for spec_result in comparison_results:
        spec_name = spec_result['spec_name']
        results = {wf: spec_result['workflows'][wf] for wf in workflow_names}

        success_count = sum(1 for r in results.values() if r['success'])

        # Update stats
        for wf in workflow_names:
            r = results[wf]
            if r['success']:
                analysis['workflow_stats'][wf]['success'] += 1
            else:
                analysis['workflow_stats'][wf]['failed'] += 1

            if not r.get('error'):
                analysis['workflow_stats'][wf]['avg_compilations'] += r.get('compilations_used', 0)
                analysis['workflow_stats'][wf]['avg_time'] += r.get('time', 0)
                analysis['workflow_stats'][wf]['avg_llm_calls'] += r.get('llm_calls', 0)

        # Check agreement
        analysis['agreement'][f'{success_count}_success'] += 1

        # Find unique successes
        for wf in workflow_names:
            if results[wf]['success']:
                other_wfs = [w for w in workflow_names if w != wf]
                if all(not results[other_wf]['success'] for other_wf in other_wfs):
                    analysis['unique_successes'][wf].append(spec_name)

        # Record details
        detail = {
            'spec': spec_name,
            'compilations': {},
            'time': {}
        }
        for wf in workflow_names:
            detail[wf] = '✓' if results[wf]['success'] else '✗'
            detail['compilations'][wf] = results[wf].get('compilations_used', '-')
            detail['time'][wf] = f"{results[wf].get('time', 0):.1f}s" if not results[wf].get('error') else '-'

        analysis['spec_details'].append(detail)

    # Calculate averages
    for wf in workflow_names:
        total = analysis['total_specs']
        stats = analysis['workflow_stats'][wf]
        stats['success_rate'] = (stats['success'] / total * 100) if total > 0 else 0
        stats['avg_compilations'] = stats['avg_compilations'] / total if total > 0 else 0
        stats['avg_time'] = stats['avg_time'] / total if total > 0 else 0
        stats['avg_llm_calls'] = stats['avg_llm_calls'] / total if total > 0 else 0

    return analysis


def print_analysis(analysis, workflow_names):
    """Print analysis report"""

    print(f"\n{'='*80}")
    print("COMPARISON ANALYSIS")
    print(f"{'='*80}")

    # Overall stats
    print(f"\n📊 Overall Statistics:")
    print(f"   Total specs tested: {analysis['total_specs']}")

    # Agreement stats
    print(f"\n   Success agreement:")
    for key, count in sorted(analysis['agreement'].items()):
        print(f"     {key}: {count}")

    # Per-workflow stats
    print(f"\n🎯 Workflow Success Rates:")
    for wf, stats in analysis['workflow_stats'].items():
        print(f"   {wf:20s}: {stats['success']}/{analysis['total_specs']} ({stats['success_rate']:.1f}%)")

    # Average resource usage
    print(f"\n⚙️  Average Resource Usage:")
    print(f"   {'Workflow':<20s} {'Compilations':<15s} {'LLM Calls':<15s} {'Time'}")
    print(f"   {'-'*20} {'-'*15} {'-'*15} {'-'*10}")
    for wf, stats in analysis['workflow_stats'].items():
        print(f"   {wf:<20s} {stats['avg_compilations']:<15.1f} {stats['avg_llm_calls']:<15.1f} {stats['avg_time']:.1f}s")

    # Unique successes - MOST IMPORTANT!
    print(f"\n⭐ UNIQUE SUCCESSES (workflow succeeded where others failed):")
    has_unique = False
    for wf, specs in analysis['unique_successes'].items():
        if specs:
            has_unique = True
            print(f"\n   {wf} ONLY ({len(specs)} specs):")
            for spec in specs[:10]:  # Show first 10
                print(f"      - {spec}")
            if len(specs) > 10:
                print(f"      ... and {len(specs) - 10} more")

    if not has_unique:
        print("   None - all workflows agree on success/failure")

    print(f"\n{'='*80}")


def save_results(output_path, comparison_results, analysis, args, workflow_names):
    """Save detailed results"""

    output = {
        'experiment': {
            'type': 'workflow_comparison',
            'timestamp': datetime.now().isoformat(),
            'dataset': str(args.dataset),
            'num_specs': args.num_specs,
            'max_compilations': args.max_compilations,
            'workflows': workflow_names
        },
        'analysis': analysis,
        'detailed_results': comparison_results
    }

    output_path = Path(output_path)
    output_path.parent.mkdir(parents=True, exist_ok=True)

    with open(output_path, 'w') as f:
        json.dump(output, f, indent=2)

    print(f"\n✓ Detailed results saved to: {output_path}")


def main():
    import argparse

    parser = argparse.ArgumentParser(
        description='Compare multiple TLA+ fixing workflows on diverse specs',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Compare SimpleLoop and SimpleLoop_RAG
  %(prog)s --workflows SimpleLoop SimpleLoop_RAG

  # Compare all four workflows
  %(prog)s --workflows SimpleLoop SimpleLoop_RAG AgenticLoop AgenticLoop_RAG

  # Test only SimpleLoop_RAG on 10 specs
  %(prog)s --workflows SimpleLoop_RAG -n 10
        """
    )

    parser.add_argument('--workflows', '-w', nargs='+',
                       default=['SimpleLoop', 'SimpleLoop_RAG'],
                       choices=list(AVAILABLE_WORKFLOWS.keys()),
                       help='Workflows to compare (default: SimpleLoop SimpleLoop_RAG)')
    parser.add_argument('--dataset', '-d', default='dataset',
                       help='Dataset directory (default: dataset)')
    parser.add_argument('--num-specs', '-n', type=int, default=46,
                       help='Number of specs to process (default: 46)')
    parser.add_argument('--max-compilations', '-m', type=int, default=3,
                       help='Max compilations per spec (default: 3)')
    parser.add_argument('--output', '-o',
                       help='Output JSON file (auto-generated if not specified)')
    parser.add_argument('--knowledge-base',
                       help='Knowledge base path for RAG workflows')
    parser.add_argument('--seed', type=int,
                       help='Random seed for reproducibility')
    parser.add_argument('--workers', type=int, default=5,
                       help='Number of parallel workers (default: 5)')

    args = parser.parse_args()

    # Set random seed if specified
    if args.seed:
        random.seed(args.seed)
        print(f"Using random seed: {args.seed}")

    # Build workflow list
    workflows_to_test = [(name, AVAILABLE_WORKFLOWS[name]) for name in args.workflows]

    # Collect diverse specs
    dataset_path = Path(__file__).parent / args.dataset
    try:
        specs = collect_diverse_specs(dataset_path, args.num_specs)
    except Exception as e:
        print(f"Error collecting specs: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)

    if not specs:
        print("Error: No specs found")
        sys.exit(1)

    # Generate output filename
    if not args.output:
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        workflow_suffix = "_".join(args.workflows)
        args.output = f"results/comparison_{workflow_suffix}_{args.num_specs}specs_{timestamp}.json"

    # Run comparison
    print(f"\n{'='*80}")
    print(f"WORKFLOW COMPARISON EXPERIMENT")
    print(f"{'='*80}")
    print(f"Dataset: {dataset_path}")
    print(f"Specs: {len(specs)}")
    print(f"Max compilations: {args.max_compilations}")
    print(f"Workflows: {', '.join(args.workflows)}")

    try:
        comparison_results = run_comparison_experiment(
            specs=specs,
            workflows_to_test=workflows_to_test,
            max_compilations=args.max_compilations,
            knowledge_base=args.knowledge_base,
            dataset_path=dataset_path,
            max_workers=args.workers
        )
    except Exception as e:
        print(f"\nError running experiment: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)

    # Analyze
    analysis = analyze_comparison(comparison_results, args.workflows)

    # Print analysis
    print_analysis(analysis, args.workflows)

    # Save results
    save_results(args.output, comparison_results, analysis, args, args.workflows)

    print(f"\n✅ Experiment complete!")


if __name__ == '__main__':
    main()
