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
| `include_last_state` | No | Include full last matched state in output (default: false). Rarely needed since it's the last successful match before failure. |

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
  "suggestion": "Trace validation failed at trace line 107. Use run_trace_debugging with breakpoint condition 'TLCGet(\"level\") = 112' to debug."
}
```

**Key fields:**
- `failed_trace_line`: The `l` value - the trace line that failed validation
- `last_state_number`: Use this for breakpoint condition
- `suggestion`: Ready-to-use debugging instruction

**Note:** Set `include_last_state=true` to include full `last_state` content (all variable values). This is rarely needed since it's the last successful match, not the failure point.

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
3. Use `suggestion` to proceed to debugging

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

## Category B (Concurrent/Lock-Free) Differences

For Category B systems (DPDK, arc-swap, libomp, crossbeam-epoch), trace validation works differently:

### Trace Format
- Input is a **preprocessed JSON** file (not raw NDJSON) with per-thread arrays and compressed timestamps
- Preprocessor merges per-thread files and compresses rdtsc timestamps to dense integers
- Run the preprocessor before validation (see `harness-generation` skill's `concurrent-timebox-guide.md`)

### Validation Behavior
- TLC explores **multiple interleavings** of concurrent events (overlapping `[start, end]` intervals)
- A trace mismatch at one interleaving doesn't mean failure — TLC tries all viable orderings
- Validation fails only if **no** interleaving can fully consume all events
- Expect **higher state counts** than Category A (branching at each overlap point)
- **Longer TLC runtimes** are normal — the search space is inherently larger

### Debugging Differences
- `failed_trace_line` may not be meaningful in the same way — failure could be at different points across different interleavings
- State mismatches may indicate TLC is exploring a non-real interleaving (normal pruning)
- If validation fails, check: (1) are intervals too wide (creating too much apparent concurrency)? (2) is state captured at the wrong time? (3) is a silent action missing?

### Timeout Considerations
- Category B traces may need longer timeouts (600-1200s) due to interleaving search
- Short traces (50-300 events) are strongly recommended to keep search tractable

## Best Practices

1. **Always start with `run_trace_validation`** - It's faster and gives you the exact failure point
2. **Use the `suggestion` field** - It provides ready-to-use debugging instructions
3. **Check the trace file** - Understand what event failed before debugging
4. **Proceed to debugging** - Use `run_trace_debugging` to inspect variable values at failure point
5. **Check `Trace.cfg` has `PROPERTIES TraceMatched`** before your first run — without it, `success` is a false positive.
6. **(Category B) Use short traces** - 50-300 events per trace, run many traces for coverage

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
    │      └─ Proceed to Phase 2 (debugging.md)
    │
    └─ status == "error"
           ├─ Check raw_output for details
           ├─ If syntax error → use validate_spec_syntax
           ├─ If file not found → verify paths
           └─ Fix error and retry validation
```
