#!/usr/bin/env python3
"""
Basic functionality test for TLA+ Trace Debugger
Tests: connection, breakpoints, variable inspection, stepIn
"""
import sys
import os
import logging

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'src'))

from handler.trace_handler import TraceDebugger

logging.basicConfig(level=logging.INFO, format='%(levelname)s: %(message)s')
logger = logging.getLogger(__name__)

def test_basic_debugging():
    """Test basic debugging workflow"""

    # Test Configuration (based on Phase2 success)
    work_dir = "/home/ubuntu/specula/data/workloads/etcdraft/scenarios/progress_inflights/spec"
    spec_file = "Traceetcdraft_progress.tla"
    config_file = "Traceetcdraft_progress.cfg"
    trace_file = "../traces/confchange_disable_validation.ndjson"
    spec_path = os.path.join(work_dir, spec_file)

    logger.info("=" * 60)
    logger.info("TLA+ Trace Debugger - Basic Test")
    logger.info("=" * 60)

    debugger = TraceDebugger()

    try:
        # Test 1: Start debugging session
        logger.info("\n[Test 1] Starting debugging session...")
        success = debugger.start(spec_file, config_file, trace_file, cwd=work_dir)
        if not success:
            logger.error("Failed to start debugger")
            return False
        logger.info("✓ Debugger started successfully")

        # Test 2: Add conditional breakpoint (level 29)
        logger.info("\n[Test 2] Adding conditional breakpoint at level 29...")
        bp_line = 522  # TraceNext
        bp_condition = 'TLCGet("level") = 29'
        success = debugger.add_breakpoint(spec_path, bp_line, bp_condition)
        if not success:
            logger.error("Failed to set breakpoint")
            return False
        logger.info(f"✓ Breakpoint set at line {bp_line} with condition: {bp_condition}")

        # Test 3: Add unconditional breakpoints (carpet bombing)
        logger.info("\n[Test 3] Adding additional breakpoints...")
        for line in [513, 514, 515, 516]:  # Inside TraceNextReceiveActions
            debugger.add_breakpoint(spec_path, line)
        logger.info("✓ Additional breakpoints set at lines 513-516")

        # Test 4: Continue and wait for stop
        logger.info("\n[Test 4] Continuing execution...")
        debugger.continue_execution()

        logger.info("Waiting for breakpoint hit (this may take a while)...")
        stop_evt = debugger.wait_for_stop(timeout=120)

        if not stop_evt:
            logger.error("Did not hit any breakpoint within timeout")
            return False

        reason = stop_evt["body"]["reason"]
        logger.info(f"✓ Stopped! Reason: {reason}")

        # Test 5: Get stack frame
        logger.info("\n[Test 5] Getting stack frame...")
        frame = debugger.get_stack_frame()
        if not frame:
            logger.error("Failed to get stack frame")
            return False

        location = f"{frame['source']['name']}:{frame['line']}"
        logger.info(f"✓ Location: {location}")

        # Test 6: Get variables
        logger.info("\n[Test 6] Getting variables...")
        variables = debugger.get_variables(frame['id'])

        if not variables:
            logger.warning("No variables returned")
        else:
            logger.info(f"✓ Got {len(variables)} scopes:")
            for scope_name, scope_vars in variables.items():
                logger.info(f"  - {scope_name}: {len(scope_vars)} variables")

                # Look for key variables
                for key in ['l', 'currentTerm', 'state', 'commitIndex']:
                    if key in scope_vars:
                        logger.info(f"    {key} = {scope_vars[key]}")

        # Test 7: Step In (be careful of recursion)
        logger.info("\n[Test 7] Testing stepIn (1 step only)...")
        before_line = frame['line']
        success = debugger.step_in()
        if not success:
            logger.error("stepIn failed")
            return False

        # Wait for next stop
        stop_evt = debugger.wait_for_stop(timeout=10)
        if stop_evt:
            frame = debugger.get_stack_frame()
            after_line = frame['line']
            logger.info(f"✓ Stepped from line {before_line} to line {after_line}")
        else:
            logger.warning("stepIn did not stop (might have completed execution)")

        logger.info("\n" + "=" * 60)
        logger.info("All tests passed!")
        logger.info("=" * 60)
        return True

    except Exception as e:
        logger.error(f"Test failed with exception: {e}")
        import traceback
        traceback.print_exc()
        return False
    finally:
        debugger.stop()
        logger.info("\nDebugger stopped.")

if __name__ == "__main__":
    success = test_basic_debugging()
    sys.exit(0 if success else 1)
