#!/usr/bin/env python3
"""Test advanced variable access: fields, indexing, expressions."""

import asyncio
import json
import sys
import os
import pytest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from tla_mcp.handlers.trace_validation import TraceValidationHandler


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


@pytest.mark.asyncio
async def test_advanced_features():
    """Test field access, indexing, and expressions."""
    print("=" * 70)
    print("Testing Advanced Variable Access")
    print("=" * 70)

    handler = TraceValidationHandler()

    specula_root = get_specula_root()
    work_dir = os.path.join(specula_root, "data/workloads/etcdraft/scenarios/progress_inflights/spec")

    arguments = {
        "spec_file": "Traceetcdraft_progress.tla",
        "config_file": "Traceetcdraft_progress.cfg",
        "trace_file": "../traces/confchange_disable_validation.ndjson",
        "work_dir": work_dir,
        "breakpoints": [
            {"line": 522, "file": "Traceetcdraft_progress.tla", "condition": 'TLCGet("level") = 29'}
        ],
        "timeout": 60,
        "collect_variables": {
            "breakpoint_line": 522,
            "breakpoint_file": "Traceetcdraft_progress.tla",
            "variables": [
                # Simple variables
                "l",
                "pl",
                # Index access (state is a function from node id to state)
                'state["1"]',
                'state["2"]',
                # Field access (durableState is a function, get node 1's record, access currentTerm field)
                # Note: TLA+ uses [field] syntax, not .field for records
                'durableState["1"].currentTerm',
                # Index into log (log is a function from node id to sequence)
                'Len(log["1"])',
                # Expression
                "l + 1",
                "pl - 1",
            ],
            "max_samples": 2
        }
    }

    print(f"\nTesting with variables:")
    for var in arguments["collect_variables"]["variables"]:
        print(f"  - {var}")

    result_json = await handler.handle(arguments)
    result = json.loads(result_json)

    print(f"\nSuccess: {result.get('success')}")
    print(f"Execution time: {result.get('execution_time', 0):.2f}s")

    if "collected_variables" in result:
        print(f"\n✅ Collected Variables ({len(result['collected_variables'])} samples):")
        for sample in result["collected_variables"]:
            print(f"\n  Sample {sample['sample_index']}:")
            for var_name, var_value in sample['variables'].items():
                print(f"    {var_name} = {var_value}")
        return True
    else:
        print("\n❌ No collected variables!")
        if not result.get('success'):
            print(f"Error: {result.get('error_message')}")
        return False


if __name__ == "__main__":
    success = asyncio.run(test_advanced_features())
    sys.exit(0 if success else 1)
