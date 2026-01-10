#!/usr/bin/env python3
"""Simple test without breakpoint conditions."""

import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from debugger import DebugSession, Breakpoint

def get_specula_root():
    """Auto-detect Specula root directory."""
    specula_root = os.environ.get('SPECULA_ROOT')
    if specula_root:
        return specula_root
    # Calculate relative to this file: tools/trace_debugger/tests/xxx.py
    this_file = os.path.abspath(__file__)
    tests_dir = os.path.dirname(this_file)              # .../tests
    trace_debugger_dir = os.path.dirname(tests_dir)     # .../trace_debugger
    tools_dir = os.path.dirname(trace_debugger_dir)     # .../tools
    return os.path.dirname(tools_dir)                   # .../Specula

specula_root = get_specula_root()
work_dir = os.path.join(specula_root, "data/workloads/etcdraft/scenarios/progress_inflights/spec")

print("="*70)
print("Simple Test: Breakpoints WITHOUT conditions")
print("="*70)

session = DebugSession(
    spec_file="Traceetcdraft_progress.tla",
    config_file="Traceetcdraft_progress.cfg",
    trace_file="../traces/confchange_disable_validation.ndjson",
    work_dir=work_dir
)

print("\n1. Starting session...")
if not session.start():
    print("Failed to start")
    sys.exit(1)

print("2. Setting breakpoint at line 522 WITHOUT condition...")
session.set_breakpoints([
    Breakpoint(line=522, description="TraceNext - NO CONDITION")
])

print("3. Running (60s timeout)...")
stats = session.run_until_done(timeout=60)

print("\n4. Results:")
stats.print_summary()

session.close()
print("\n✅ Test completed")
