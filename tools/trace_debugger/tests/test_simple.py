#!/usr/bin/env python3
"""
Minimal test - just connect and initialize
"""
import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'src'))

from client.dap_client import DAPClient
from executor.tlc_process import TLCExecutor
from handler.trace_handler import TraceDebugger
import logging

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

def test_connection():
    work_dir = "/home/ubuntu/specula/data/workloads/etcdraft/scenarios/progress_inflights/spec"
    spec_file = "Traceetcdraft_progress.tla"
    config_file = "Traceetcdraft_progress.cfg"
    trace_file = "../traces/confchange_disable_validation.ndjson"

    debugger = TraceDebugger()

    try:
        logger.info("Test 1: Start debugger")
        success = debugger.start(spec_file, config_file, trace_file, cwd=work_dir)
        if success:
            logger.info("✓ Connected and initialized")
        else:
            logger.error("✗ Failed to start")
            return False

        logger.info("\nTest 2: Get initial state (should not be stopped yet)")
        frame = debugger.get_stack_frame()
        if frame:
            logger.info(f"Frame: {frame}")
        else:
            logger.info("No frame yet (expected - not stopped)")

        logger.info("\n✓ All basic tests passed")
        return True

    except Exception as e:
        logger.error(f"Error: {e}")
        import traceback
        traceback.print_exc()
        return False
    finally:
        debugger.stop()

if __name__ == "__main__":
    success = test_connection()
    sys.exit(0 if success else 1)
