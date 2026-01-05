#!/usr/bin/env python3
"""Test advanced variable access: fields, indexing, expressions."""

import asyncio
import json
import sys
import os
import pytest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from tla_mcp.handlers.trace_validation import TraceValidationHandler


@pytest.mark.asyncio
async def test_advanced_features():
    """Test field access, indexing, and expressions."""
    print("=" * 70)
    print("Testing Advanced Variable Access")
    print("=" * 70)

    handler = TraceValidationHandler()

    arguments = {
        "spec_file": "Traceetcdraft_progress.tla",
        "config_file": "Traceetcdraft_progress.cfg",
        "trace_file": "../traces/confchange_disable_validation.ndjson",
        "work_dir": "/home/ubuntu/specula/data/workloads/etcdraft/scenarios/progress_inflights/spec",
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
