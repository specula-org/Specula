# Trace Validation Tool Guide

This document describes how to use the `run_trace_validation` tool for TLA+ trace validation.

## Overview

`run_trace_validation` is a lightweight tool that runs TLC directly (without debugger mode) to validate traces against TLA+ specifications. It provides concise, actionable feedback suitable for AI agents.

**When to use this tool:**
- Initial validation to check if a trace matches the spec
- Quick feedback on trace validation results
- As the first step before detailed debugging

**When to use `run_trace_debugging` instead:**
- When you need to set breakpoints
- When you need to inspect variable values
- When you need to evaluate TLA+ expressions
- After `run_trace_validation` reports a failure and you need to debug

---

## Tool Parameters

| Parameter | Required | Description |
|-----------|----------|-------------|
| `spec_file` | Yes | TLA+ spec file name (e.g., `Traceetcdraft.tla`) |
| `config_file` | Yes | TLC config file name (e.g., `Traceetcdraft.cfg`) |
| `trace_file` | Yes | Trace file path (relative to work_dir or absolute) |
| `work_dir` | Yes | Working directory (absolute path) |
| `timeout` | No | Timeout in seconds (default: 300) |
| `tla_jar` | No | Path to tla2tools.jar (auto-detected if not provided) |
| `community_jar` | No | Path to CommunityModules-deps.jar (auto-detected if not provided) |

---

## Return Values

The tool returns one of three statuses:

### 1. Success (`status: "success"`)

Trace validation passed. All trace lines match the specification.

```json
{
  "status": "success",
  "states_generated": 40,
  "message": "Trace validation passed",
  "success": true
}
```

**Fields:**
- `states_generated`: Number of states TLC generated (equals trace length for success)
- `message`: Human-readable success message

### 2. Trace Mismatch (`status: "trace_mismatch"`)

Trace validation failed. The trace does not match the specification at a specific point.

```json
{
  "status": "trace_mismatch",
  "last_state_number": 112,
  "failed_trace_line": 107,
  "states_generated": 116,
  "last_state": "State 112: <TraceNext...>\n/\\ l = 107\n/\\ ...",
  "suggestion": "Trace validation failed at trace line 107. Use run_trace_debugging with breakpoint condition 'TLCGet(\"level\") = 112' to debug.",
  "success": true
}
```

**Fields:**
- `last_state_number`: The last state number in the counterexample (use this for breakpoint condition)
- `failed_trace_line`: The `l` value - which trace line failed validation
- `states_generated`: Total number of states TLC generated
- `last_state`: Full content of the last state (all variable values)
- `suggestion`: Actionable suggestion for next steps

**Important:** The `last_state_number` and `failed_trace_line` may differ because TLC can generate multiple states for the same trace line (e.g., when processing messages).

### 3. Error (`status: "error"`)

TLC encountered an error other than trace mismatch (e.g., syntax error, configuration error).

```json
{
  "status": "error",
  "message": "TLC reported an error",
  "raw_output": "... full TLC output ...",
  "success": true
}
```

**Fields:**
- `raw_output`: Full TLC output for manual inspection

---

## Usage Examples

### Example 1: Basic Validation

```python
result = run_trace_validation(
    spec_file="Traceetcdraft.tla",
    config_file="Traceetcdraft.cfg",
    trace_file="../traces/basic.ndjson",
    work_dir="/path/to/spec"
)

if result["status"] == "success":
    print("Trace validation passed!")
elif result["status"] == "trace_mismatch":
    print(f"Failed at trace line {result['failed_trace_line']}")
    print(result["suggestion"])
```

### Example 2: Validation with Custom Timeout

```python
result = run_trace_validation(
    spec_file="Traceetcdraft.tla",
    config_file="Traceetcdraft.cfg",
    trace_file="../traces/long_trace.ndjson",
    work_dir="/path/to/spec",
    timeout=600  # 10 minutes for long traces
)
```

---

## Workflow: From Validation to Debugging

### Step 1: Run Initial Validation

```python
result = run_trace_validation(
    spec_file="Traceetcdraft.tla",
    config_file="Traceetcdraft.cfg",
    trace_file="../traces/leader_transfer.ndjson",
    work_dir="/path/to/spec"
)
```

### Step 2: Check Result

If `status == "success"`: Done! The trace is valid.

If `status == "trace_mismatch"`: Proceed to debugging.

### Step 3: Use Suggestion for Debugging

The `suggestion` field tells you exactly how to proceed:

```
"Trace validation failed at trace line 107. Use run_trace_debugging
with breakpoint condition 'TLCGet(\"level\") = 112' to debug."
```

### Step 4: Debug with run_trace_debugging

```python
result = run_trace_debugging(
    spec_file="Traceetcdraft.tla",
    config_file="Traceetcdraft.cfg",
    trace_file="../traces/leader_transfer.ndjson",
    work_dir="/path/to/spec",
    breakpoints=[
        {
            "line": 528,  # TraceNext entry point
            "condition": 'TLCGet("level") = 112',
            "description": "TraceNext at failing state"
        }
    ]
)
```

See [Debugging Guide](debugging_guide.md) for detailed debugging techniques.

---

## Understanding the Output

### What is `last_state_number`?

This is the TLC state number in the counterexample trace. Use it for breakpoint conditions:

```python
condition = f'TLCGet("level") = {result["last_state_number"]}'
```

### What is `failed_trace_line`?

This is the value of `l` in the spec - the trace log line number that failed validation. Use it to:

1. Inspect the trace file at that line:
   ```bash
   sed -n '107p' trace.ndjson | jq .
   ```

2. Understand what event caused the failure

### Why might they differ?

- `last_state_number = 112` means TLC reached state 112
- `failed_trace_line = 107` means in state 112, the spec was trying to match trace line 107

This can happen when:
- Multiple TLC states are generated for the same trace line (e.g., processing pending messages)
- The trace has duplicate or merged events

---

## Best Practices

### 1. Always Start with run_trace_validation

Before using the more complex `run_trace_debugging`, always run `run_trace_validation` first:
- It's faster (no debugger overhead)
- It gives you the exact failure point
- It provides a ready-to-use breakpoint condition

### 2. Use the Suggestion Field

The `suggestion` field is designed for AI agents. It provides:
- The exact trace line that failed
- The exact breakpoint condition to use
- Clear next steps

### 3. Inspect the Last State

The `last_state` field contains all variable values at the failure point. Look for:
- `l` - current trace line being validated
- `state` - node states (Leader, Follower, Candidate)
- `currentTerm` - term numbers
- `log` - log entries
- `messages` - pending messages

### 4. Check the Trace File

After getting `failed_trace_line`, always check the actual trace content:

```bash
# View the failing line
sed -n '107p' trace.ndjson | jq .

# View context (5 lines before and after)
sed -n '102,112p' trace.ndjson | jq -c .
```

---

## Common Issues

### Issue 1: Timeout

If validation times out, increase the timeout:

```python
result = run_trace_validation(
    ...,
    timeout=600  # Increase to 10 minutes
)
```

### Issue 2: JAR Files Not Found

If TLC JAR files are not found, specify them explicitly:

```python
result = run_trace_validation(
    ...,
    tla_jar="/path/to/tla2tools.jar",
    community_jar="/path/to/CommunityModules-deps.jar"
)
```

### Issue 3: Error Status with Syntax Error

If `status == "error"` and `raw_output` shows syntax errors, fix the spec first:

```python
# Use validate_spec_syntax to check for syntax errors
result = validate_spec_syntax(
    spec_file="Traceetcdraft.tla",
    config_file="Traceetcdraft.cfg",
    work_dir="/path/to/spec"
)
```

---

## Summary

| Task | Tool |
|------|------|
| Initial trace validation | `run_trace_validation` |
| Quick pass/fail check | `run_trace_validation` |
| Detailed debugging with breakpoints | `run_trace_debugging` |
| Expression evaluation | `run_trace_debugging` |
| Variable inspection | `run_trace_debugging` |

**Workflow:**
1. Run `run_trace_validation` first
2. If success: done
3. If trace_mismatch: use the `suggestion` to run `run_trace_debugging`
4. Follow the [Debugging Guide](debugging_guide.md) for detailed debugging
