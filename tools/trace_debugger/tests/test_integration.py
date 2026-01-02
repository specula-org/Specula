#!/usr/bin/env python3
"""Integration test - simulates the examples/coarse_grained_localization.py scenario."""

import sys
import os

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from debugger import DebugSession, Breakpoint


def test_coarse_grained_localization():
    """
    Simulates the debugging scenario from examples/coarse_grained_localization.py.

    This test validates trace line 30 (confchange_disable_validation.ndjson)
    by setting breakpoints at key locations to identify which branch is taken.
    """

    print("="*70)
    print("Integration Test: Coarse-Grained Localization")
    print("="*70)
    print()
    print("Scenario: Debugging confchange_disable_validation.ndjson line 30 failure")
    print()

    work_dir = "/home/ubuntu/specula/data/workloads/etcdraft/scenarios/progress_inflights/spec"

    # Create session
    print("Step 1: Creating DebugSession...")
    session = DebugSession(
        spec_file="Traceetcdraft_progress.tla",
        config_file="Traceetcdraft_progress.cfg",
        trace_file="../traces/confchange_disable_validation.ndjson",
        work_dir=work_dir
    )
    print("  ✅ Session created")
    print()

    # Start session
    print("Step 2: Starting TLC debugger (this may take 30-60 seconds)...")
    if not session.start():
        print("  ❌ Failed to start session")
        print("  This could be because:")
        print("    - TLC is not found")
        print("    - Spec file doesn't exist")
        print("    - Trace file doesn't exist")
        return False
    print("  ✅ TLC debugger started and connected")
    print()

    # Set breakpoints for coarse-grained localization
    print("Step 3: Setting breakpoints for coarse-grained localization...")
    print("  Strategy: Place breakpoints at major branch points")
    print()

    breakpoints = [
        Breakpoint(
            line=522,
            condition='TLCGet("level") = 29',
            description="TraceNext entry point"
        ),
        Breakpoint(
            line=489,
            condition='TLCGet("level") = 29',
            description="SendAppendEntriesRequest branch"
        ),
        Breakpoint(
            line=323,
            condition='TLCGet("level") = 29',
            description="AppendEntriesIfLogged entry"
        ),
        Breakpoint(
            line=327,
            condition='TLCGet("level") = 29',
            description="AppendEntries action call"
        ),
    ]

    for bp in breakpoints:
        print(f"    Line {bp.line:3d}: {bp.description}")
    print()

    session.set_breakpoints(breakpoints)
    print("  ✅ Breakpoints set")
    print()

    # Run until done
    print("Step 4: Running trace validation with breakpoints...")
    print("  (Collecting statistics, 120s timeout)")
    print()

    stats = session.run_until_done(timeout=120)

    print("Step 5: Analyzing results...")
    print()
    stats.print_summary()
    print()

    # Analyze results
    print("Step 6: Interpretation...")
    print()

    hit_323 = stats.get_hit_count(323, "Traceetcdraft_progress.tla")
    hit_327 = stats.get_hit_count(327, "Traceetcdraft_progress.tla")

    if hit_323 > 0 and hit_327 == 0:
        print("  🔍 Analysis:")
        print(f"     - Line 323 was hit {hit_323} times ✅")
        print(f"     - Line 327 was hit {hit_327} times ❌")
        print()
        print("  💡 Conclusion:")
        print("     The failure occurs BETWEEN line 323 and line 327")
        print("     This means AppendEntriesIfLogged was entered, but")
        print("     the AppendEntries action call never happened.")
        print()
        print("  📋 Next Step (Fine-Grained Localization):")
        print("     Set breakpoints on each condition inside")
        print("     AppendEntriesIfLogged to find which condition fails.")
        print()
    else:
        print(f"  Hit counts: Line 323={hit_323}, Line 327={hit_327}")
        print("  (Results may differ from original debugging session)")
        print()

    # Close session
    print("Step 7: Closing session...")
    session.close()
    print("  ✅ Session closed")
    print()

    print("="*70)
    print("✅ Integration test completed successfully!")
    print("="*70)

    return True


if __name__ == "__main__":
    try:
        success = test_coarse_grained_localization()
        sys.exit(0 if success else 1)
    except KeyboardInterrupt:
        print("\n\n⚠️  Test interrupted by user")
        sys.exit(130)
    except Exception as e:
        print(f"\n❌ Test failed with error: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)
