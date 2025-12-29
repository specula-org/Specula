import sys
import os
import logging

# Add src to path
sys.path.append(os.path.join(os.path.dirname(__file__), '..'))

from src.handler.trace_handler import TraceDebugger

logging.basicConfig(level=logging.INFO, format='%(message)s')
logger = logging.getLogger(__name__)

def test_raft_scenario():
    # Configuration
    tla_jar = "/home/ubuntu/specula/lib/tla2tools.jar"
    community_jar = "/home/ubuntu/specula/lib/CommunityModules-deps.jar"
    work_dir = "/home/ubuntu/specula/data/workloads/etcdraft/scenarios/progress_inflights/spec"
    spec_file = "Traceetcdraft_progress.tla"
    cfg_file = "Traceetcdraft_progress.cfg"
    trace_file = "../traces/confchange_disable_validation.ndjson"
    
    debugger = TraceDebugger(tla_jar, community_jar)
    
    logger.info(">>> [TEST] Starting Debugger...")
    if not debugger.start(spec_file, cfg_file, trace_file, cwd=work_dir):
        logger.error("Failed to start")
        return False

    try:
        # 1. Set the target level breakpoint
        spec_path = os.path.join(work_dir, spec_file)
        logger.info(f">>> [TEST] Setting breakpoint at line 522 for level 29...")
        debugger.add_breakpoint(spec_path, 522, condition='TLCGet("level") = 29')
        
        # 2. Execute
        debugger.continue_execution()
        
        # 3. Wait for stop
        logger.info(">>> [TEST] Running to failure point...")
        stop_evt = debugger.wait_for_stop(timeout=30)
        if not stop_evt:
            logger.error("Timed out waiting for breakpoint")
            return False
            
        logger.info(f"✅ STOPPED! Reason: {stop_evt['body'].get('reason')}")
        
        # 4. Deep Inspection
        frame = debugger.get_stack_frame()
        if frame:
            logger.info(f"   At: {frame['source']['name']}:{frame['line']}")
            
            # Print variables
            vars_map = debugger.get_variables(frame['id'])
            # Extract current level to verify
            state_vars = vars_map.get('State', {}) or vars_map.get('Variables', {})
            current_l = state_vars.get('l', 'Unknown')
            logger.info(f"   Current level variable (l): {current_l}")
            
            if str(current_l) == '29':
                logger.info("✅ SUCCESS: Correctly stopped at Level 29.")
            else:
                logger.warning(f"❌ MISMATCH: Expected l=29, got {current_l}")

            # 5. Proof of Step In
            logger.info(">>> [TEST] Performing Step-In to verify deep access...")
            debugger.step_in()
            step_stop = debugger.wait_for_stop(timeout=5)
            if step_stop:
                new_frame = debugger.get_stack_frame()
                logger.info(f"   Stepped to: {new_frame['source']['name']}:{new_frame['line']}")
                return True
        
        return False

    finally:
        debugger.stop()

if __name__ == "__main__":
    success = test_raft_scenario()
    sys.exit(0 if success else 1)
