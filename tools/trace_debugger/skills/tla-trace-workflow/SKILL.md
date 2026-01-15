---
name: tla-trace-workflow
description: "TLA+ Trace Validation workflow. Use when: (1) validating if a trace matches a TLA+ spec, (2) debugging trace validation failures (TLC reports 'Temporal properties were violated' or validation stops unexpectedly), (3) fixing spec/trace inconsistencies after root cause is identified."
---

# TLA+ Trace Validation Workflow

This skill guides you through validating traces against TLA+ specifications and debugging validation failures.

## Core Concepts (MUST REMEMBER)

### Variable `l` Semantics

```
l = N means "currently validating TraceLog[N]"
NOT "already validated N lines"
```

- When `l=29`, the spec is attempting to validate TraceLog[29]
- If validation fails at this point, TraceLog[29] is the failing line
- TraceLog is 1-indexed (TraceLog[1] = first line of trace file)

### TLCGet("level") vs `l`

**ALWAYS use `TLCGet("level")` in breakpoint conditions, NOT `l`.**

| Aspect | `l` | `TLCGet("level")` |
|--------|-----|-------------------|
| Scope | Only in Trace wrapper spec | Available everywhere |
| Files | Only works in `Trace*.tla` | Works in base spec too |
| Breakpoint condition | May fail silently | Always works |

**Correct:**
```python
"condition": 'TLCGet("level") = 29'
```

**Wrong:**
```python
"condition": "l = 29"  # May not work in base spec files!
```

### `logline` Definition

```tla
logline == TraceLog[l]  -- This is a DEFINITION, not a variable
```

- `logline` always equals `TraceLog[l]` in current state
- Cannot be assigned or modified
- Changes automatically when `l` changes

### Breakpoint Hit Semantics

```
Breakpoint hit = TLC is ATTEMPTING to evaluate this line
Breakpoint hit != Condition at this line is TRUE
```

- A line can be hit but still evaluate to FALSE
- Action calls (like `AppendEntries(i,j,range)`) get hit even when the action returns FALSE internally
- To know if a condition is TRUE, you MUST inspect variable values

### Conjunction Short-Circuit Evaluation

```tla
Action ==
    /\ Condition1    -- Line A: Evaluated first
    /\ Condition2    -- Line B: Only if A is TRUE
    /\ Condition3    -- Line C: Only if A and B are TRUE
```

- TLC evaluates conditions top to bottom
- If a condition is FALSE, subsequent conditions are not evaluated
- Decreasing hit counts indicate filtering: `Line A: 100 hits → Line B: 50 hits → Line C: 0 hits`

---

## Available Tools

| Tool | Purpose | When to Use |
|------|---------|-------------|
| `run_trace_validation` | Quick validation check | First step, always |
| `run_trace_debugging` | Set breakpoints, collect statistics | After validation fails |
| `get_trace_info` | Check trace file info | Before validation |
| `validate_spec_syntax` | Check spec syntax | If TLC reports syntax errors |
| `run_trace_validation_parallel` | Check against multiple traces | After proposed bug fix |
| `clean_traces` | Delete generated files | Final cleanup |

---

## Workflow

### Phase 1: Validation

**Goal:** Determine if trace matches spec

**Tool:** `run_trace_validation`

**Outputs:**
- `status: "success"` → Done, trace is valid
- `status: "trace_mismatch"` → Go to Phase 2
- `status: "error"` → Check syntax with `validate_spec_syntax`

**Key fields for trace_mismatch:**
- `failed_trace_line`: The `l` value - which trace line failed
- `last_state_number`: Use this for breakpoint condition: `TLCGet("level") = {last_state_number}`
- `suggestion`: Ready-to-use debugging hint

**Read `references/validation.md` for detailed guidance.**

### Phase 2: Debugging

**Goal:** Locate the exact condition that failed

**Tool:** `run_trace_debugging`

**Methodology: Layered Debugging (Coarse → Fine)**

1. **Coarse-grained localization**: Set breakpoints at major branches to identify which code path is relevant
2. **Fine-grained localization**: Set breakpoints at each condition in the relevant branch
3. **Variable inspection**: Use `evaluate` or `collect_variables` to understand WHY a condition failed

**Key patterns:**
- Decreasing hit counts show short-circuit filtering
- First line with 0 hits is where failure occurs
- If last hit is an action call, the action failed internally → debug inside that action

**Read `references/debugging.md` for detailed methodology.**

### Phase 3: Fix

**Goal:** Fix the spec or trace to resolve inconsistency

**First, identify the error type:**

| Error Type | Description | Action |
|------------|-------------|--------|
| **Inconsistency Error** | Spec is objectively wrong about system behavior | Fix spec, read system code for evidence |
| **Abstraction Gap** | Spec is correct but at different abstraction level | **STOP and ask user for guidance** |

**If uncertain about error type:** Treat it as an Abstraction Gap and ask the user.

**For Inconsistency Errors:**
1. Read system source code to understand actual behavior
2. Find corresponding code location as evidence for your fix
3. Fix the **base spec** (e.g., `etcdraft.tla`), avoid modifying trace comparison logic
4. Verify with `run_trace_validation_parallel`
5. Document in `fix_log.md` in the spec directory

**For Abstraction Gaps:**
1. Understand what the spec models vs what the system does
2. **STOP and ask user** - explain the gap and list possible strategies:
   - Option A: Modify spec to support system's behavior
   - Option B: Modify trace comparison logic
   - Option C: Modify system instrumentation
3. Wait for user guidance before proceeding

**Read `references/fix.md` for detailed workflow and fix_log.md format.**

### Phase 4: Cleanup

The user may request not to clean up the generated files. Otherwise, run `clean_traces`.

---

## Quick Reference

### run_trace_validation Response (trace_mismatch)

```json
{
  "status": "trace_mismatch",
  "failed_trace_line": 107,
  "last_state_number": 112,
  "suggestion": "Use run_trace_debugging with condition 'TLCGet(\"level\") = 112'"
}
```

### run_trace_debugging Request

```python
run_trace_debugging(
    spec_file="Trace*.tla",
    config_file="Trace*.cfg",
    trace_file="path/to/trace.ndjson",
    work_dir="/absolute/path",
    breakpoints=[
        {"line": 522, "condition": 'TLCGet("level") = 112', "description": "TraceNext entry"},
        {"line": 489, "condition": 'TLCGet("level") = 112', "description": "SomeAction branch"}
    ],
    # Optional: evaluate expressions at a breakpoint
    evaluate={
        "breakpoint_line": 489,
        "expressions": ["i", "j", "logline.event.msg.type"]
    }
)
```

### run_trace_debugging Response

```json
{
  "statistics": {
    "total_hits": 150,
    "breakpoints": [
      {"line": 522, "hit_count": 100, "was_hit": true},
      {"line": 489, "hit_count": 0, "was_hit": false}
    ],
    "never_hit": [{"line": 489, "description": "SomeAction branch"}]
  },
  "evaluated_expressions": [
    {"expression": "i", "result": "1"},
    {"expression": "j", "result": "2"}
  ]
}
```

### run_trace_validation_parallel Response (trace_mismatch)

```json
{
  "status": "trace_mismatch",
  "passed": 5,
  "failed": 1,
  "failures": {
    "trace_1.ndjson": "Use run_trace_debugging with condition 'TLCGet(\"level\") = 112'"
  }
}
```

---

## Common Mistakes to Avoid

| Mistake | Correct Approach |
|---------|------------------|
| Using `l = N` in breakpoint conditions | Use `TLCGet("level") = N` |
| Assuming breakpoint hit means condition is TRUE | Always inspect variable values |
| Stopping when an action call is hit | If action is last hit, debug INSIDE the action |
| Setting breakpoints without conditions | Always use `TLCGet("level") = N` to focus |
| Diving deep immediately | Start with coarse-grained localization first |

---

## When to Read References

- **Starting Phase 1?** → Read `references/validation.md`
- **Validation failed, starting Phase 2?** → Read `references/debugging.md`
- **Found root cause, need to fix?** → Read `references/fix.md`
