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
| test_basic.py | PASS | All imports and classes work |
| test_integration.py | PASS | Full E2E test with TLC |
| test_simple.py | PASS | Simple debugging test |
| examples/demo/*.py | WORKS | Old scripts with hardcoded logic |
