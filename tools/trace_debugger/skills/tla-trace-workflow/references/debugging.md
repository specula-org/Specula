# Phase 2: Debugging Trace Validation Failures

This document provides detailed methodology for debugging trace validation failures.

## Core Principle: Layered Debugging

**Don't try to find the root cause all at once.**

1. **Coarse-grained localization** - Identify which branch/function is relevant
2. **Fine-grained localization** - Find the specific failing condition
3. **Variable inspection** - Understand WHY the condition failed

Each layer answers a specific question. Decide the next layer based on current findings.

---

## Tool: run_trace_debugging

### Parameters

| Parameter | Required | Description |
|-----------|----------|-------------|
| `spec_file` | Yes | TLA+ spec file name |
| `config_file` | Yes | TLC config file name |
| `trace_file` | Yes | Trace file path |
| `work_dir` | Yes | Working directory (absolute path) |
| `breakpoints` | Yes | List of breakpoints |
| `timeout` | No | Timeout in seconds (default: 300) |
| `evaluate` | No | Expression evaluation config |
| `collect_variables` | No | Variable collection config |

### Breakpoint Object

```python
{
    "line": 522,                              # Required: line number
    "file": "etcdraft_progress.tla",          # Optional: defaults to spec_file
    "condition": 'TLCGet("level") = 29',      # Optional: when to trigger
    "description": "TraceNext entry"          # Optional: for reporting
}
```

### Evaluate Object

```python
{
    "breakpoint_line": 327,                   # Required: which breakpoint
    "breakpoint_file": "Traceetcdraft.tla",   # Optional: match specific file
    "expressions": ["i", "j", "logline.event.msg.type"]  # Required: what to evaluate
}
```

### Collect Variables Object

```python
{
    "breakpoint_line": 327,
    "breakpoint_file": "Traceetcdraft.tla",   # Optional
    "variables": ["i", "j", "state[i].currentTerm"],
    "max_samples": 5                          # Optional: default 10
}
```

### Response

```json
{
  "statistics": {
    "total_hits": 150,
    "breakpoints": [
      {"file": "Trace.tla", "line": 522, "description": "...", "hit_count": 100, "was_hit": true},
      {"file": "Trace.tla", "line": 327, "description": "...", "hit_count": 0, "was_hit": false}
    ],
    "never_hit": [{"file": "Trace.tla", "line": 327, "description": "..."}]
  },
  "execution_time": 45.2,
  "evaluated_expressions": [
    {"expression": "i", "result": "1", "file": "Trace.tla", "line": 327}
  ],
  "collected_variables": [
    {"sample_index": 0, "file": "Trace.tla", "line": 327, "variables": {"i": "1", "j": "2"}}
  ]
}
```

---

## Step 1: Coarse-Grained Localization

### Goal

Answer: **Which branch/function in the spec is responsible for validating this trace line?**

### Method

Set breakpoints at key entry points and major branches:

```python
# From validation: failed_trace_line=107, last_state_number=112
breakpoints = [
    {"line": 522, "condition": 'TLCGet("level") = 112', "description": "TraceNext entry"},
    {"line": 480, "condition": 'TLCGet("level") = 112', "description": "TraceNextNonReceiveActions"},
    {"line": 512, "condition": 'TLCGet("level") = 112', "description": "TraceNextReceiveActions"},
    {"line": 489, "condition": 'TLCGet("level") = 112', "description": "SendAppendEntriesRequest branch"},
    {"line": 487, "condition": 'TLCGet("level") = 112', "description": "Commit branch"},
    {"line": 483, "condition": 'TLCGet("level") = 112', "description": "BecomeLeader branch"},
]
```

**CRITICAL:** Always use `TLCGet("level") = N` (not `l = N`) - it works in all files.

### Analyze Results

```
Results:
  Line 522 (TraceNext entry):              1 hit  ✓
  Line 480 (TraceNextNonReceiveActions):   1 hit  ✓
  Line 489 (SendAppendEntriesRequest):     1 hit  ✓  ← This branch was taken
  Line 487 (Commit branch):                0 hits ✗
  Line 512 (TraceNextReceiveActions):      0 hits ✗

Conclusion: Problem is in the SendAppendEntriesRequest branch
```

- **Hit branches** = relevant code paths
- **Unhit branches** = irrelevant, can ignore

---

## Step 2: Fine-Grained Localization

### Goal

Answer: **Within the relevant branch, which specific condition failed?**

### Method

Set breakpoints at each condition in the identified branch:

```tla
\* Example: AppendEntriesIfLogged function (Lines 323-328)
AppendEntriesIfLogged(i, j, range) ==
    /\ LoglineIsMessageEvent("SendAppendEntriesRequest", i, j)  \* 323
    /\ logline.event.msg.type = "MsgApp"                        \* 324
    /\ range[1] = logline.event.msg.index + 1                   \* 325
    /\ range[2] = range[1] + logline.event.msg.entries          \* 326
    /\ AppendEntries(i, j, range)                               \* 327
    /\ ValidateAfterAppendEntries(i, j)                         \* 328
```

```python
breakpoints = [
    {"line": 323, "condition": 'TLCGet("level") = 112', "description": "LoglineIsMessageEvent check"},
    {"line": 324, "condition": 'TLCGet("level") = 112', "description": "msg.type check"},
    {"line": 325, "condition": 'TLCGet("level") = 112', "description": "range[1] check"},
    {"line": 326, "condition": 'TLCGet("level") = 112', "description": "range[2] check"},
    {"line": 327, "condition": 'TLCGet("level") = 112', "description": "AppendEntries call"},
    {"line": 328, "condition": 'TLCGet("level") = 112', "description": "ValidateAfter call"},
]
```

### Analyze Hit Pattern

```
Results:
  Line 323: 18 hits  ← Tried 18 different (i,j,range) combinations
  Line 324: 18 hits  ← All 18 passed message event check
  Line 325: 18 hits  ← All 18 passed type check
  Line 326: 18 hits  ← All 18 passed range[1] check
  Line 327: 1 hit    ← AppendEntries was called (entered)
  Line 328: 0 hits   ← AppendEntries returned FALSE
```

### Identify Failure Point

**Pattern: Decreasing hit counts (short-circuit evaluation)**

```
Line A: 100 hits
Line B: 50 hits   ← 50 failed at A
Line C: 20 hits   ← 30 failed at B
Line D: 0 hits    ← First zero = failure point
```

**Case 1: Last hit is an ACTION CALL**

```tla
/\ SomeCondition        -- Line B: 50 hits
/\ SomeAction(i, j)     -- Line C: 20 hits  ← ACTION CALL (capitalized)
/\ AnotherCondition     -- Line D: 0 hits
```

**Meaning:** The action was called 20 times but failed internally every time.

**Next step:** Set breakpoints INSIDE `SomeAction` to find internal failure.

**Case 2: Last hit is a CONDITION**

```tla
/\ SomeCondition        -- Line B: 50 hits
/\ i /= j               -- Line C: 20 hits  ← CONDITION
/\ AnotherCondition     -- Line D: 0 hits
```

**Meaning:** 20 attempts satisfied Line C, all failed at Line D.

**Next step:** At Line C, inspect variables to understand why Line D fails.

### How to Distinguish Action Calls from Conditions

| Type | Examples |
|------|----------|
| **Condition** | `i /= j`, `range[1] <= range[2]`, `state[i] = Leader`, `x \in S` |
| **Action call** | `AppendEntries(i, j, range)`, `Send([type \|-> ...])`, `LET ... IN ...` |

General rule: Capitalized operators or obvious function calls are actions.

---

## Step 3: Dive Into Action Internals

### When to Use

If Step 2 finds that an **action call** is the last hit (i.e., entered but failed), you need to debug inside that action.

### Method

Set breakpoints inside the called action:

```tla
\* AppendEntriesInRangeToPeer in etcdraft_progress.tla
AppendEntriesInRangeToPeer(subtype, i, j, range) ==
    /\ i /= j                                                   \* 436
    /\ range[1] <= range[2]                                     \* 437
    /\ state[i] = Leader                                        \* 438
    /\ j \in GetConfig(i) \union GetOutgoingConfig(i) \union ...  \* 439
    /\ (subtype = "heartbeat" \/ ~IsPaused(i, j))               \* 443
    /\ LET ... IN /\ Send(...) /\ ...                           \* 444+
```

```python
# Note: Different file! Must specify file parameter
# Use TLCGet("level") because l is not visible in this file
condition = 'i = 1 /\\ j = 2 /\\ TLCGet("level") = 112'

breakpoints = [
    {"file": "etcdraft_progress.tla", "line": 436, "condition": condition, "description": "i /= j"},
    {"file": "etcdraft_progress.tla", "line": 437, "condition": condition, "description": "range check"},
    {"file": "etcdraft_progress.tla", "line": 438, "condition": condition, "description": "state = Leader"},
    {"file": "etcdraft_progress.tla", "line": 439, "condition": condition, "description": "j in Config"},
    {"file": "etcdraft_progress.tla", "line": 443, "condition": condition, "description": "heartbeat/pause"},
]
```

### Analyze Results

```
Results:
  Line 436: 204 hits  ← All attempts check i /= j
  Line 437: 136 hits  ← 68 failed at i /= j
  Line 438: 106 hits  ← 30 failed at range check
  Line 439: 0 hits    ← All 106 failed at state = Leader

Conclusion: state[i] != Leader when expected
```

---

## Step 4: Variable Inspection

### Goal

Answer: **WHY did this condition fail? What are the actual variable values?**

### Using `evaluate`

More powerful - can evaluate arbitrary expressions including operator parameters.

```python
result = run_trace_debugging(
    ...,
    breakpoints=[
        {"line": 438, "condition": 'i = 1 /\\ TLCGet("level") = 112', "description": "Before config check"}
    ],
    evaluate={
        "breakpoint_line": 438,
        "expressions": [
            "i",
            "j",
            "state[i]",                    # Check actual state
            "GetConfig(i)",                # Check config set
            "j \\in GetConfig(i)",         # Verify the failing condition
            "GetOutgoingConfig(i)",
            "GetLearners(i)"
        ]
    }
)
```

**Output:**

```json
{
  "evaluated_expressions": [
    {"expression": "i", "result": "1"},
    {"expression": "j", "result": "2"},
    {"expression": "state[i]", "result": "StateFollower"},
    {"expression": "GetConfig(i)", "result": "{\"1\"}"},
    {"expression": "j \\in GetConfig(i)", "result": "FALSE"},
    {"expression": "GetOutgoingConfig(i)", "result": "{}"},
    {"expression": "GetLearners(i)", "result": "{}"}
  ]
}
```

**Root cause found:** `state[i] = StateFollower` (expected Leader), and `j=2` is not in `GetConfig(i)`.

### Using `collect_variables`

Simpler - collects values of specified variables at each breakpoint hit.

```python
result = run_trace_debugging(
    ...,
    breakpoints=[
        {"line": 438, "condition": 'TLCGet("level") = 112'}
    ],
    collect_variables={
        "breakpoint_line": 438,
        "variables": ["i", "j", "state[i].currentTerm"],
        "max_samples": 5
    }
)
```

### evaluate vs collect_variables

| Feature | `collect_variables` | `evaluate` |
|---------|---------------------|------------|
| Global variables | Yes | Yes |
| Operator parameters (i, j) | No | Yes |
| Arbitrary expressions | No | Yes |
| Complex conditions | No | Yes |

**Recommendation:** Use `evaluate` for debugging. It's more powerful.

---

## Hit Pattern Analysis

### Pattern 1: Gradual Decrease

```
Line A: 100 hits
Line B: 80 hits
Line C: 50 hits
Line D: 20 hits
Line E: 0 hits   ← Failure point
```

**Meaning:** Each condition filters out some attempts. Failure is at Line E.

### Pattern 2: Sudden Drop to Zero

```
Line A: 100 hits
Line B: 100 hits
Line C: 100 hits
Line D: 0 hits   ← All 100 failed here
```

**Meaning:** All attempts pass A, B, C but fail at D.

### Pattern 3: Action Call Then Zero

```
Line A: 100 hits
Line B: 50 hits
Line C (action call): 10 hits
Line D: 0 hits
```

**Meaning:** Action at Line C was called 10 times, all returned FALSE.

**Next step:** Debug INSIDE the action.

### Pattern 4: Single Hit Then Zero

```
Line A: 1 hit
Line B: 0 hits
```

**Meaning:** Only one attempt, failed at Line B.

---

## Debugging Checklist

### Before Starting

- [ ] Have validation result with `failed_trace_line` and `last_state_number`
- [ ] Checked trace file at `failed_trace_line` to understand the event
- [ ] Will use `TLCGet("level") = {last_state_number}` in all breakpoint conditions

### For Each Layer

- [ ] Clear question this layer should answer
- [ ] Breakpoints set at relevant locations with conditions
- [ ] Analyzed hit count pattern
- [ ] Identified "last success" and "first failure" positions
- [ ] If last hit is action call → need to debug inside that action
- [ ] If last hit is condition → inspect variables to understand why next condition fails

### Variable Inspection

- [ ] Used `evaluate` to check relevant expressions
- [ ] Compared actual values with expected values
- [ ] Identified root cause (spec bug vs trace bug)

---

## Common Debugging Scenarios

### Scenario 1: Wrong Branch Taken

**Symptom:** Expected action has 0 hits, unexpected action has hits.

**Investigation:**
1. Check trace file - what event should this be?
2. Check event type matching in spec
3. May be a mapping issue between trace event names and spec action names

### Scenario 2: All Conditions Hit, Action Fails

**Symptom:**
```
Line 323: 18 hits
Line 324: 18 hits
Line 325: 18 hits
Line 327 (action): 1 hit
Line 328: 0 hits
```

**Investigation:**
1. Action was called but failed internally
2. Set breakpoints inside the action
3. Find which internal condition failed

### Scenario 3: Parameter Mismatch

**Symptom:** Condition checking parameters has 0 hits.

**Investigation:**
1. Use `evaluate` to check actual parameter values
2. Compare with trace file values
3. May be index/field name mismatch

### Scenario 4: State Inconsistency

**Symptom:** State check (like `state[i] = Leader`) fails unexpectedly.

**Investigation:**
1. Check `state[i]` actual value
2. Check trace history - when should this have changed?
3. May be missing state update in earlier trace lines

---

## Iterative Refinement

**Key principle:** Debug layer by layer, not all at once.

```
Round 1: Coarse localization
    → Found: Problem in SendAppendEntriesRequest branch

Round 2: Fine localization in that branch
    → Found: AppendEntries action fails

Round 3: Inside AppendEntries
    → Found: Line 439 (j in Config) fails

Round 4: Variable inspection at Line 438
    → Found: GetConfig(i) = {"1"}, but j = 2

Root cause: Node 2 not in config when expected
```

Each round narrows down the problem. Don't skip layers.
