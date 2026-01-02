#!/usr/bin/env python3
"""Basic test to verify imports and class instantiation."""

import sys
import os

# Add src to path (go up one level from tests/)
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

def test_imports():
    """Test that all imports work."""
    print("Testing imports...")

    try:
        from debugger.breakpoint import Breakpoint, BreakpointHit, BreakpointStatistics
        print("  ✅ breakpoint module imported")
    except Exception as e:
        print(f"  ❌ breakpoint import failed: {e}")
        raise

    try:
        from debugger.session import DebugSession
        print("  ✅ session module imported")
    except Exception as e:
        print(f"  ❌ session import failed: {e}")
        raise

    try:
        from debugger.utils import collect_variable_values
        print("  ✅ utils module imported")
    except Exception as e:
        print(f"  ❌ utils import failed: {e}")
        raise

    try:
        from debugger import DebugSession, Breakpoint
        print("  ✅ Package-level import works")
    except Exception as e:
        print(f"  ❌ Package import failed: {e}")
        raise

    print("✅ All imports successful\n")
    return True


def test_breakpoint_classes():
    """Test Breakpoint and BreakpointStatistics classes."""
    print("Testing Breakpoint classes...")

    from debugger import Breakpoint, BreakpointHit, BreakpointStatistics

    # Test Breakpoint creation
    bp1 = Breakpoint(line=100, description="Test breakpoint")
    print(f"  ✅ Created breakpoint: line={bp1.line}, desc='{bp1.description}'")

    bp2 = Breakpoint(line=200, condition='TLCGet("level") = 29', file="test.tla", description="Conditional BP")
    print(f"  ✅ Created conditional breakpoint: line={bp2.line}, condition='{bp2.condition}'")

    # Test BreakpointHit
    hit = BreakpointHit(file="test.tla", line=100, description="Test", hit_count=5)
    print(f"  ✅ Created BreakpointHit: {hit.hit_count} hits")

    # Test BreakpointStatistics
    stats = BreakpointStatistics(
        hits=[
            BreakpointHit("test.tla", 100, "First BP", 10),
            BreakpointHit("test.tla", 200, "Second BP", 0),
            BreakpointHit("test.tla", 300, "Third BP", 5),
        ],
        total_hits=15
    )
    print(f"  ✅ Created BreakpointStatistics: {stats.total_hits} total hits")

    # Test get_hit_count
    count = stats.get_hit_count(100, "test.tla")
    assert count == 10, f"Expected 10 hits, got {count}"
    print(f"  ✅ get_hit_count works: line 100 has {count} hits")

    # Test get_never_hit
    never_hit = stats.get_never_hit()
    assert len(never_hit) == 1, f"Expected 1 never-hit BP, got {len(never_hit)}"
    assert never_hit[0].line == 200
    print(f"  ✅ get_never_hit works: found {len(never_hit)} never-hit breakpoints")

    # Test print_summary
    print("\n  Testing print_summary():")
    print("  " + "="*60)
    stats.print_summary()
    print("  " + "="*60)

    print("✅ Breakpoint classes work correctly\n")
    return True


def test_session_instantiation():
    """Test DebugSession can be instantiated."""
    print("Testing DebugSession instantiation...")

    from debugger import DebugSession

    session = DebugSession(
        spec_file="Test.tla",
        config_file="Test.cfg",
        trace_file="test.ndjson",
        work_dir="/tmp"
    )

    print(f"  ✅ Created DebugSession")
    print(f"     - spec_file: {session.spec_file}")
    print(f"     - config_file: {session.config_file}")
    print(f"     - trace_file: {session.trace_file}")
    print(f"     - work_dir: {session.work_dir}")
    print(f"     - port: {session.port}")

    # Check defaults
    assert session.tla_jar.endswith("tla2tools.jar")
    assert session.community_jar.endswith("CommunityModules-deps.jar")
    print(f"  ✅ Default JAR paths set correctly")

    print("✅ DebugSession instantiation works\n")
    return True


def main():
    """Run all tests."""
    print("="*70)
    print("Basic Functionality Tests")
    print("="*70)
    print()

    try:
        test_imports()
        test_breakpoint_classes()
        test_session_instantiation()

        print("="*70)
        print("✅ All basic tests passed!")
        print("="*70)
        return 0

    except Exception as e:
        print()
        print("="*70)
        print(f"❌ Tests failed: {e}")
        print("="*70)
        import traceback
        traceback.print_exc()
        return 1


if __name__ == "__main__":
    sys.exit(main())
