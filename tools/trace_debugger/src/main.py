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
    debugger = TraceDebugger(args.tla_jar, args.community_jar)
    
    spec_path = args.spec
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
                    for name, val in vars_map.items():
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
    run_parser.add_argument('--tla-jar', default='/home/ubuntu/specula/lib/tla2tools.jar', help='Path to tla2tools.jar')
    run_parser.add_argument('--community-jar', default='/home/ubuntu/specula/lib/CommunityModules-deps.jar', help='Path to CommunityModules-deps.jar')

    args = parser.parse_args()

    if args.command == 'run':
        cmd_run(args)
    else:
        parser.print_help()

if __name__ == "__main__":
    main()
