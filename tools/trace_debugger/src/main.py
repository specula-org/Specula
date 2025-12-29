import argparse
import logging
import sys
import os

# Adjust path to find modules
sys.path.append(os.path.join(os.path.dirname(__file__), '..'))

from src.handler.trace_handler import TraceDebugger

logging.basicConfig(level=logging.INFO, format='%(message)s')
logger = logging.getLogger(__name__)

def cmd_run(args):
    debugger = TraceDebugger()
    
    spec_path = os.path.abspath(args.spec)
    work_dir = os.path.dirname(spec_path)
    spec_name = os.path.basename(spec_path)
    config_name = spec_name.replace('.tla', '.cfg')
    
    if args.config:
        config_name = args.config

    logger.info(f"Starting Debugger for {spec_name}...")
    
    success = debugger.start(spec_name, config_name, args.trace, cwd=work_dir)
    if not success:
        return

    try:
        # Set Breakpoint
        if args.breakpoint:
            line = int(args.breakpoint.split(':')[0])
            cond = args.breakpoint.split(':')[1] if ':' in args.breakpoint else None
            logger.info(f"Setting breakpoint at line {line} (Condition: {cond})")
            debugger.add_breakpoint(spec_path, line, cond)

        # Run
        logger.info("Continuing execution...")
        debugger.continue_execution()
        
        # Wait for stop
        stop_evt = debugger.wait_for_stop()
        if stop_evt:
            logger.info(f"Stopped! Reason: {stop_evt['body']['reason']}")
            
            # Inspect
            frame = debugger.get_stack_frame()
            if frame:
                logger.info(f"Location: {frame['source']['name']}:{frame['line']}")
                
                if args.inspect:
                    logger.info("Inspecting variables...")
                    vars_map = debugger.get_variables(frame['id'])
                    for scope, vars in vars_map.items():
                        print(f"--- {scope} ---")
                        for name, val in vars.items():
                            print(f"  {name} = {val}")
                            
                if args.step_in:
                    logger.info("Stepping In...")
                    debugger.step_in()
                    stop_evt = debugger.wait_for_stop()
                    if stop_evt:
                        frame = debugger.get_stack_frame()
                        logger.info(f"Stepped to: {frame['source']['name']}:{frame['line']}")

        else:
            logger.info("Finished without stopping.")

    finally:
        debugger.stop()

def cmd_test(args):
    """Quick test command for development"""
    work_dir = "/home/ubuntu/specula/data/workloads/etcdraft/scenarios/progress_inflights/spec"
    spec_file = "Traceetcdraft_progress.tla"
    spec_path = os.path.join(work_dir, spec_file)
    trace_file = "../traces/basic.ndjson"

    logger.info("=" * 60)
    logger.info("Quick Test Mode")
    logger.info("=" * 60)

    debugger = TraceDebugger()

    try:
        logger.info("\n[1/5] Starting debugger...")
        if not debugger.start(spec_file, f"{spec_file.replace('.tla', '.cfg')}", trace_file, cwd=work_dir):
            logger.error("Failed to start")
            return
        logger.info("✓ Debugger started")

        logger.info("\n[2/5] Setting breakpoint at line 513...")
        if debugger.add_breakpoint(spec_path, 513):
            logger.info("✓ Breakpoint set")
        else:
            logger.warning("Breakpoint may not have been set correctly")

        logger.info(f"Breakpoints: {debugger.breakpoints}")

        logger.info("\n[3/5] Continuing execution...")
        debugger.continue_execution()

        logger.info("\n[4/5] Waiting for stop (30 sec timeout)...")
        stop_evt = debugger.wait_for_stop(timeout=30)

        if stop_evt:
            logger.info(f"✓✓✓ STOPPED!")
            reason = stop_evt["body"]["reason"]
            logger.info(f"Reason: {reason}")

            frame = debugger.get_stack_frame()
            if frame:
                loc = f"{frame['source']['name']}:{frame['line']}"
                logger.info(f"Location: {loc}")

                logger.info("\n[5/5] Getting variables...")
                vars_map = debugger.get_variables(frame['id'])
                for scope_name, scope_vars in vars_map.items():
                    logger.info(f"\n--- {scope_name} ({len(scope_vars)} vars) ---")
                    # Print first 5 variables
                    for i, (name, val) in enumerate(list(scope_vars.items())[:5]):
                        logger.info(f"  {name} = {val}")
                    if len(scope_vars) > 5:
                        logger.info(f"  ... and {len(scope_vars) - 5} more")
        else:
            logger.error("Did not hit breakpoint within timeout")
            logger.info(f"Event queue: {len(debugger.event_queue)} events")

    finally:
        debugger.stop()

def main():
    parser = argparse.ArgumentParser(description="TLA+ Trace Debugger Tool")
    subparsers = parser.add_subparsers(dest='command')

    run_parser = subparsers.add_parser('run', help='Run trace validation with debugging')
    run_parser.add_argument('spec', help='Path to TLA+ spec file')
    run_parser.add_argument('--trace', required=True, help='Path to NDJSON trace file')
    run_parser.add_argument('--config', help='Config file name (default: spec.cfg)')
    run_parser.add_argument('--breakpoint', help='Breakpoint "line:condition" (e.g. "522:TLCGet("level")=29")')
    run_parser.add_argument('--inspect', action='store_true', help='Dump variables upon stopping')
    run_parser.add_argument('--step-in', action='store_true', help='Perform one step-in after stopping')

    test_parser = subparsers.add_parser('test', help='Quick test with default configuration')

    args = parser.parse_args()

    if args.command == 'run':
        cmd_run(args)
    elif args.command == 'test':
        cmd_test(args)
    else:
        parser.print_help()

if __name__ == "__main__":
    main()
