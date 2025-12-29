#!/usr/bin/env python3
"""
Debug test with detailed logging
"""
import sys
import os
sys.path.insert(0, '/home/ubuntu/specula/tools/trace_debugger/src')

from handler.trace_handler import TraceDebugger
import logging

logging.basicConfig(
    level=logging.DEBUG,
    format='[%(levelname)s] %(name)s: %(message)s'
)
logger = logging.getLogger(__name__)

def test():
    work_dir = "/home/ubuntu/specula/data/workloads/etcdraft/scenarios/progress_inflights/spec"
    spec_file = "Traceetcdraft_progress.tla"
    config_file = "Traceetcdraft_progress.cfg"
    trace_file = "../traces/basic.ndjson"
    spec_path = os.path.join(work_dir, spec_file)

    logger.info("=" * 60)
    logger.info("Debug Test with Detailed Logging")
    logger.info("=" * 60)

    debugger = TraceDebugger()

    try:
        logger.info("\n1. Starting debugger...")
        success = debugger.start(spec_file, config_file, trace_file, cwd=work_dir)
        if not success:
            logger.error("Failed to start")
            return False
        logger.info("✓ Started")

        logger.info("\n2. Adding breakpoint at line 513...")
        success = debugger.add_breakpoint(spec_path, 513)
        logger.info(f"Breakpoint set result: {success}")
        logger.info(f"Breakpoints dict: {debugger.breakpoints}")

        logger.info("\n3. Continuing execution...")
        cont_success = debugger.continue_execution()
        logger.info(f"Continue result: {cont_success}")

        logger.info("\n4. Waiting for stop (15 sec timeout)...")
        stop_evt = debugger.wait_for_stop(timeout=15)

        if stop_evt:
            logger.info(f"✓✓✓ STOPPED! Event: {stop_evt}")
            frame = debugger.get_stack_frame()
            if frame:
                logger.info(f"Frame: {frame['source']['name']}:{frame['line']}")
        else:
            logger.warning("Did not stop within 15 seconds")
            logger.info("Checking event queue...")
            logger.info(f"Event queue length: {len(debugger.event_queue)}")
            for evt in list(debugger.event_queue):
                logger.info(f"  Event: {evt.get('event')} - {evt.get('body', {})}")

        return True

    except Exception as e:
        logger.error(f"Exception: {e}")
        import traceback
        traceback.print_exc()
        return False
    finally:
        logger.info("\nStopping debugger...")
        debugger.stop()

if __name__ == "__main__":
    test()
