# Test Fixtures

This directory contains test data used by the test suite.

## Structure

- `sample_specs/` - Sample TLA+ specifications for testing
- `sample_traces/` - Sample execution traces
- `expected_outputs/` - Expected outputs for validation

## Usage

Access fixtures in tests via the `fixtures_dir` fixture.

Or use shared fixtures from `conftest.py` like `sample_spec_content`.
