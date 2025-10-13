# Specula Test Suite

Test organization.

## Structure

```
tests/
├── conftest.py                   ← pytest config & shared fixtures
├── __init__.py                   ← makes tests a package
├── unit/                         ← unit tests (mirrors src/)
│   ├── __init__.py
│   ├── tools/                    ← mirrors src/tools/
│   │   ├── __init__.py
│   │   ├── test_read_tool.py    ← tests for read_tool.py
│   │   └── test_write_tool.py   ← tests for write_tool.py
│   └── utils/                    ← mirrors src/utils/
│       ├── __init__.py
│       └── test_result_types.py ← tests for result_types.py
├── integration/                  ← integration tests(TODO)
│   └── test_pipeline.py
└── fixtures/                     ← shared test data
    ├── sample_specs/
    └── sample_traces/
```
