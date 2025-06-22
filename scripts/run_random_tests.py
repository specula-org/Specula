#!/usr/bin/env python3
"""
Unified Random Test Runner
"""

import os
import sys
import json
import argparse
import logging
from pathlib import Path

# Add src path to Python path
sys.path.insert(0, str(Path(__file__).parent.parent / "src"))

from core.raft_state_machine_runner import RaftStateMachineRunner
from core.raftexample_runner import RaftExampleRunner
from core.docker_runner import DockerRaftRunner
from core.instrumentation import InstrumentationTool

logger = logging.getLogger(__name__)

class UnifiedRandomTestRunner:
    """Unified random test runner"""
    
    def __init__(self, config: dict):
        self.config = config
        self.runners = {}
        
    def setup_runners(self, instrumented_raft_path: str, trace_dir: str):
        """Setup all runners"""
        self.runners = {
            'state_machine': RaftStateMachineRunner(instrumented_raft_path, trace_dir),
            'raftexample': RaftExampleRunner(
                self.config.get('raftexample_path', './raftexample'), 
                trace_dir
            ),
            'docker': DockerRaftRunner(instrumented_raft_path, trace_dir)
        }
    
    def run_tests(self, methods: list, num_runs: int = 10, duration: int = 30) -> dict:
        """Run tests for specified methods"""
        all_results = {}
        
        for method in methods:
            if method not in self.runners:
                logger.warning(f"Unknown test method: {method}")
                continue
                
            logger.info(f"Running {method} tests...")
            
            try:
                runner = self.runners[method]
                
                if method == 'state_machine':
                    results = runner.run_random_test(num_runs, duration)
                elif method == 'raftexample':
                    results = runner.run_random_test(num_runs, duration)
                elif method == 'docker':
                    results = runner.run_random_test(num_runs, duration)
                
                report = runner.generate_report(results)
                all_results[method] = report
                
                logger.info(f"{method} completed: {report['summary']['successful_runs']}/{report['summary']['total_runs']} successful")
                
            except Exception as e:
                logger.error(f"Failed to run {method} tests: {e}")
                all_results[method] = {
                    'success': False,
                    'error': str(e)
                }
        
        return all_results
    
    def generate_unified_report(self, all_results: dict) -> dict:
        """Generate unified report"""
        total_runs = 0
        total_successful_runs = 0
        total_operations = 0
        total_successful_operations = 0
        all_trace_files = []
        
        method_summaries = {}
        
        for method, result in all_results.items():
            if result.get('success', True) and 'summary' in result:
                summary = result['summary']
                total_runs += summary.get('total_runs', 0)
                total_successful_runs += summary.get('successful_runs', 0)
                total_operations += summary.get('total_operations', 0)
                total_successful_operations += summary.get('successful_operations', 0)
                
                if 'trace_files' in result:
                    all_trace_files.extend(result['trace_files'])
                
                method_summaries[method] = summary
        
        unified_report = {
            'overall_summary': {
                'total_methods': len(all_results),
                'successful_methods': len([r for r in all_results.values() if r.get('success', True)]),
                'total_runs': total_runs,
                'total_successful_runs': total_successful_runs,
                'overall_run_success_rate': total_successful_runs / total_runs if total_runs > 0 else 0,
                'total_operations': total_operations,
                'total_successful_operations': total_successful_operations,
                'overall_operation_success_rate': total_successful_operations / total_operations if total_operations > 0 else 0
            },
            'method_summaries': method_summaries,
            'detailed_results': all_results,
            'all_trace_files': all_trace_files
        }
        
        return unified_report


def create_instrumented_raft(config_file: str, raft_go_path: str, output_path: str) -> str:
    """Create instrumented version of raft.go"""
    logger.info("Creating instrumented raft.go...")
    
    tool = InstrumentationTool()
    
    # Use configuration file for instrumentation
    result = tool.process_file(config_file, raft_go_path, output_path)
    
    if result['success']:
        logger.info(f"Instrumented raft.go created at: {output_path}")
        return output_path
    else:
        raise Exception(f"Failed to create instrumented raft.go: {result.get('message', 'Unknown error')}")


def main():
    parser = argparse.ArgumentParser(
        description="Unified Random Test Runner for Raft Implementation",
        formatter_class=argparse.RawTextHelpFormatter
    )
    
    parser.add_argument('config_file', help="Configuration file (YAML)")
    parser.add_argument('raft_go_path', help="Path to original raft.go file")
    
    parser.add_argument('--methods', nargs='+', 
                       choices=['state_machine', 'raftexample', 'docker', 'all'],
                       default=['state_machine'],
                       help="Test methods to run (default: state_machine)")
    
    parser.add_argument('--runs', type=int, default=10, 
                       help="Number of test runs per method")
    
    parser.add_argument('--duration', type=int, default=30,
                       help="Duration per run in seconds")
    
    parser.add_argument('--trace-dir', default='./traces',
                       help="Directory for trace output")
    
    parser.add_argument('--output-dir', default='./test_results',
                       help="Directory for test results")
    
    parser.add_argument('--raftexample-path', 
                       help="Path to raftexample directory")
    
    parser.add_argument('--log-level', choices=['DEBUG', 'INFO', 'WARNING', 'ERROR'],
                       default='INFO', help="Log level")
    
    args = parser.parse_args()
    
    # Setup logging
    logging.basicConfig(
        level=getattr(logging, args.log_level),
        format='[%(asctime)s] [%(levelname)s] %(message)s'
    )
    
    # Create output directories
    output_dir = Path(args.output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)
    
    trace_dir = Path(args.trace_dir)
    trace_dir.mkdir(parents=True, exist_ok=True)
    
    # Process methods parameter
    if 'all' in args.methods:
        methods = ['state_machine', 'raftexample', 'docker']
    else:
        methods = args.methods
    
    # Create configuration
    config = {}
    if args.raftexample_path:
        config['raftexample_path'] = args.raftexample_path
    
    try:
        # Create instrumented version of raft.go
        instrumented_raft_path = output_dir / "instrumented_raft.go"
        create_instrumented_raft(args.config_file, args.raft_go_path, str(instrumented_raft_path))
        
        # Create unified runner
        runner = UnifiedRandomTestRunner(config)
        runner.setup_runners(str(instrumented_raft_path), str(trace_dir))
        
        # Run tests
        logger.info(f"Starting unified random tests with methods: {methods}")
        all_results = runner.run_tests(methods, args.runs, args.duration)
        
        # Generate unified report
        unified_report = runner.generate_unified_report(all_results)
        
        # Save report
        report_file = output_dir / "unified_test_report.json"
        with open(report_file, 'w') as f:
            json.dump(unified_report, f, indent=2)
        
        # Display summary
        summary = unified_report['overall_summary']
        logger.info("=== Test Results Summary ===")
        logger.info(f"Methods: {summary['successful_methods']}/{summary['total_methods']} successful")
        logger.info(f"Runs: {summary['total_successful_runs']}/{summary['total_runs']} successful ({summary['overall_run_success_rate']:.2%})")
        logger.info(f"Operations: {summary['total_successful_operations']}/{summary['total_operations']} successful ({summary['overall_operation_success_rate']:.2%})")
        logger.info(f"Trace files: {len(unified_report['all_trace_files'])}")
        logger.info(f"Report saved to: {report_file}")
        
        return 0 if summary['successful_methods'] == summary['total_methods'] else 1
        
    except Exception as e:
        logger.error(f"Test execution failed: {e}")
        return 1


if __name__ == "__main__":
    sys.exit(main()) 