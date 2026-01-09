# Phase 1: Trace Validation

This document provides detailed guidance for the validation phase.

## Overview

`run_trace_validation` runs TLC directly (without debugger) to validate a trace against a TLA+ specification. It provides concise, actionable feedback.

**Always start here.** This is faster than debugging and tells you exactly where validation failed.

## Tool Parameters

| Parameter | Required | Description |
|-----------|----------|-------------|
| `spec_file` | Yes | TLA+ spec file name (e.g., `Traceetcdraft.tla`) |
| `config_file` | Yes | TLC config file name (e.g., `Traceetcdraft.cfg`) |
| `trace_file` | Yes | Trace file path (relative to work_dir or absolute) |
| `work_dir` | Yes | Working directory (absolute path) |
| `timeout` | No | Timeout in seconds (default: 300) |
| `tla_jar` | No | Path to tla2tools.jar (auto-detected) |
| `community_jar` | No | Path to CommunityModules-deps.jar (auto-detected) |

## Response Types

### 1. Success

```json
{
  "status": "success",
  "states_generated": 40,
  "message": "Trace validation passed"
}
```

**Action:** Done. The trace is valid.

### 2. Trace Mismatch

```json
{
  "status": "trace_mismatch",
  "last_state_number": 112,
  "failed_trace_line": 107,
  "states_generated": 116,
  "last_state": "State 112: <TraceNext...>\n/\\ l = 107\n...",
  "suggestion": "Trace validation failed at trace line 107. Use run_trace_debugging with breakpoint condition 'TLCGet(\"level\") = 112' to debug."
}
```

**Key fields:**
- `failed_trace_line`: The `l` value - the trace line that failed validation
- `last_state_number`: Use this for breakpoint condition
- `last_state`: Full variable values at failure point
- `suggestion`: Ready-to-use debugging instruction

**Important:** `last_state_number` and `failed_trace_line` may differ because TLC can generate multiple states for the same trace line (e.g., when processing pending messages).

**Action:** Proceed to Phase 2 (Debugging).

### 3. Error

```json
{
  "status": "error",
  "message": "TLC reported an error",
  "raw_output": "... full TLC output ..."
}
```

**Action:** Check `raw_output` for error details. Common causes:
- Syntax error → Use `validate_spec_syntax` to check
- Missing file → Verify paths
- Configuration error → Check .cfg file

## Usage Examples

### Basic Validation

```python
result = run_trace_validation(
    spec_file="Traceetcdraft.tla",
    config_file="Traceetcdraft.cfg",
    trace_file="../traces/basic.ndjson",
    work_dir="/path/to/spec"
)
```

### With Custom Timeout (for long traces)

```python
result = run_trace_validation(
    spec_file="Traceetcdraft.tla",
    config_file="Traceetcdraft.cfg",
    trace_file="../traces/long_trace.ndjson",
    work_dir="/path/to/spec",
    timeout=600  # 10 minutes
)
```

## After Validation Fails

### Step 1: Understand the Failure

From the `trace_mismatch` response:
1. Note `failed_trace_line` - this is which line in the trace file failed
2. Note `last_state_number` - use this for breakpoint conditions
3. Read `last_state` to see all variable values at failure

### Step 2: Check the Trace File

```bash
# View the failing line (e.g., line 107)
sed -n '107p' trace.ndjson | jq .

# View context (5 lines before and after)
sed -n '102,112p' trace.ndjson | jq -c .
```

Or use `get_trace_info` tool:

```python
info = get_trace_info(trace_file="/path/to/trace.ndjson")
# Returns: line_count, file_size_bytes, first_lines, last_lines
```

**Understand:**
- What event is this line? (SendAppendEntriesRequest, Commit, etc.)
- Which nodes are involved? (from, to)
- What are the key parameters? (index, entries, term)

### Step 3: Use the Suggestion

The `suggestion` field tells you exactly how to proceed:

```
"Trace validation failed at trace line 107. Use run_trace_debugging
with breakpoint condition 'TLCGet(\"level\") = 112' to debug."
```

Use this condition for all breakpoints in Phase 2.

### Step 4: Proceed to Phase 2

Go to `references/debugging.md` for detailed debugging methodology.

## Syntax Check

If `status == "error"` with syntax errors:

```python
result = validate_spec_syntax(
    spec_file="Traceetcdraft.tla",
    config_file="Traceetcdraft.cfg",
    work_dir="/path/to/spec"
)

if result["syntax_valid"]:
    print("Syntax is OK, error is something else")
else:
    print("Syntax errors found:")
    for error in result["errors"]:
        print(f"  {error}")
```

## Common Issues

### Timeout

Increase timeout for long traces:

```python
result = run_trace_validation(
    ...,
    timeout=600  # Increase from default 300
)
```

### JAR Files Not Found

Specify paths explicitly:

```python
result = run_trace_validation(
    ...,
    tla_jar="/path/to/tla2tools.jar",
    community_jar="/path/to/CommunityModules-deps.jar"
)
```

### Trace File Issues

Use `get_trace_info` to verify:

```python
info = get_trace_info(trace_file="/path/to/trace.ndjson")
print(f"Trace has {info['line_count']} lines")
print(f"First line: {info['first_lines'][0]}")
```

## Best Practices

1. **Always start with `run_trace_validation`** - It's faster and gives you the exact failure point
2. **Use the `suggestion` field** - It provides ready-to-use debugging instructions
3. **Check the trace file** - Understand what event failed before debugging
4. **Inspect `last_state`** - Variable values often reveal the issue directly

## Decision Tree

```
run_trace_validation
    │
    ├─ status == "success"
    │      └─ Done! Trace is valid.
    │
    ├─ status == "trace_mismatch"
    │      ├─ Note failed_trace_line and last_state_number
    │      ├─ Check trace file at failed_trace_line
    │      ├─ Inspect last_state for clues
    │      └─ Proceed to Phase 2 (debugging.md)
    │
    └─ status == "error"
           ├─ Check raw_output for details
           ├─ If syntax error → use validate_spec_syntax
           ├─ If file not found → verify paths
           └─ Fix error and retry validation
```
