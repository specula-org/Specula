# Testing Guide

## Test Suite

### Basic Tests (test_basic.py)
Tests imports and basic class instantiation without TLC.

```bash
python3 test_basic.py
```

What it tests:
- Module imports work
- Breakpoint classes can be created
- BreakpointStatistics functions work
- DebugSession can be instantiated

Expected result: All tests pass in < 1 second

### Integration Test (test_integration.py)
Full integration test with real TLC debugger.

```bash
python3 test_integration.py
```

What it tests:
- TLC debugger starts correctly
- DAP connection established
- Breakpoints can be set
- Statistics are collected correctly
- Session closes cleanly

Expected result: Complete test in 60-120 seconds

### Simple Test (test_simple.py)
Simple debugging test with a single breakpoint (used during development).

```bash
python3 test_simple.py
```

What it tests:
- Breakpoint without condition
- Basic event loop
- Hit counting

Expected result: Completes trace validation (timeout 60s)

### Step Operations Test (test_step_operations.py)
Comprehensive test suite for step operations (step_over, step_into, step_out).

```bash
python3 test_step_operations.py
```

What it tests:
- **step_over()**: Execute next line without entering functions
- **step_into()**: Step into action/function calls
- **step_out()**: Step out of current action/function
- **Interactive stepping workflow**: Combined multi-step debugging scenario

Features:
- Uses dynamically created TLA+ spec (no external files needed)
- All specs defined as Python strings in the test file
- Automatic cleanup with `tempfile.TemporaryDirectory()`
- Gracefully handles TLC termination during stepping

Expected result: All 4 tests pass in ~90 seconds

### Example Scripts (../examples/demo/)
Real-world debugging scenarios.

```bash
python3 ../examples/demo/coarse_grained_localization.py
python3 ../examples/demo/fine_grained_localization.py
python3 ../examples/demo/variable_inspection.py
```

## Test Status

| Test | Status | Notes |
|------|--------|-------|
| test_basic.py | ✅ PASS | All imports and classes work |
| test_integration.py | ✅ PASS | Full E2E test with TLC |
| test_simple.py | ✅ PASS | Simple debugging test |
| test_step_operations.py | ✅ PASS | Step operations (step_over, step_into, step_out) |
| examples/demo/*.py | ✅ WORKS | Demo scripts with real-world scenarios |

## Running All Tests

Run all tests in sequence:
```bash
cd tools/trace_debugger/tests
python3 test_basic.py
python3 test_integration.py
python3 test_step_operations.py
```

Expected total runtime: ~3-4 minutes

## Requirements

- **Java 11+**: Required to run TLC
- **Python 3.8+**: Required for the test suite
- **TLA+ Tools**: `tla2tools.jar` and `CommunityModules-deps.jar` in `lib/` directory
- **Environment variable** (optional): `SPECULA_ROOT` pointing to the specula root directory

## Troubleshooting

### "Failed to connect DAP client"
- **Cause**: TLC debugger not starting or port 4712 already in use
- **Solution**: Check if another TLC debugger is running, kill it, and retry

### "Timeout waiting for stopped event"
- **Cause**: TLC terminated before step operation completed
- **Solution**: This is expected behavior in some tests - TLC finishes quickly and terminates

### "TLA+ tools JAR not found"
- **Cause**: Missing `tla2tools.jar` or `CommunityModules-deps.jar`
- **Solution**: Ensure JAR files are in `$SPECULA_ROOT/lib/` or set paths explicitly

### Tests hang indefinitely
- **Cause**: Deadlock in TLC or network issue
- **Solution**: Kill the process (Ctrl+C) and check TLC output for errors
