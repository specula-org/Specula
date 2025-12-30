# Background Knowledge: Trace Validation Framework and Debugger

This document provides essential background knowledge for debugging trace validation failures in TLA+ specifications.

## 1. TLA+ Trace Validation Fundamentals

### 1.1 Core Variable Semantics

#### The `l` Variable

```
l: Current trace line being validated
  - l=N means "currently validating TraceLog[N]"
  - NOT "already validated N lines"
  - After successful validation: l' = N+1 (transition to next state)
```

**Example:**
```
State i (l=29):
  → Execute TraceNext
  → Validate TraceLog[29]
  → If successful: StepToNextTrace sets l' = 30
  → State i+1 (l=30)

If validation fails:
  → Cannot execute StepToNextTrace
  → Cannot transition to next state
  → TLC stops at State i
```

#### The `logline` Definition

```tla
VARIABLE l
logline == TraceLog[l]  -- This is a DEFINITION, not a variable
VARIABLE pl
```

**Key Points:**
- `logline` is a **derived definition**, not an independent state variable
- `logline == TraceLog[l]` means logline always equals TraceLog[l]
- When `l` changes, `logline` automatically updates
- `logline` cannot be assigned or modified directly

**Usage in actions:**
- Unprimed `logline` refers to current state's value (based on current `l`)
- To reference next state: use `TraceLog[l']` (not `logline'`)

#### The `TraceLog` Sequence

```
TraceLog: Sequence of trace events from JSON file
  - Indexing starts at 1 (TLA+ sequences are 1-indexed)
  - TraceLog[1] = First line of JSON file
  - TraceLog[N] = Nth line of JSON file
  - TraceLog[0] does NOT exist
```

**Definition:**
```tla
OriginTraceLog ==
    SelectSeq(ndJsonDeserialize(JsonFile), LAMBDA l: "event" \in DOMAIN l)

TraceLog ==
    TLCEval(IF "MAX_TRACE" \in DOMAIN IOEnv
            THEN SubSeq(OriginTraceLog, 1, atoi(IOEnv.MAX_TRACE))
            ELSE OriginTraceLog)
```

### 1.2 State Transition Model

#### Successful Validation Path

```
Initial State (State 0):
  l = 1
  logline = TraceLog[1]

State 0 → State 1:
  1. Execute TraceNext
  2. logline = TraceLog[1] (validate first trace line)
  3. Check all conditions
  4. If success: StepToNextTrace, l' = 2
  5. Enter State 1 with l = 2

State 1 → State 2:
  1. logline = TraceLog[2] (validate second trace line)
  2. Check all conditions
  3. If success: l' = 3
  4. Enter State 2 with l = 3

...and so on
```

#### Failed Validation Path

```
State N-1 (l=N):
  1. logline = TraceLog[N]
  2. Execute TraceNext
  3. Check all conditions
  4. Some condition FAILS
  5. Cannot execute StepToNextTrace
  6. Cannot generate State N
  7. TLC stops with "M states generated" where M = N
```

### 1.3 Interpreting TLC Output

```
Example: "29 states generated, 0 states left on queue"

This means:
  - Successfully generated State 0 through State 28
  - State 0: l=1
  - State 1: l=2
  - ...
  - State 28: l=29

  - Attempted to generate State 29 from State 28
  - State 28 has l=29, so validating TraceLog[29]
  - Validation of TraceLog[29] FAILED
  - Could not transition to l=30
  - TLC stopped
```

**Key Insight:** If TLC reports "N states generated", the failure occurs when validating `TraceLog[N]`, not TraceLog[N+1].

## 2. TLA+ Language Semantics

### 2.1 Conjunction (AND) in Actions

```tla
ActionName ==
    /\ Condition1    -- Line A
    /\ Condition2    -- Line B
    /\ Condition3    -- Line C
    /\ SubAction     -- Line D
```

**Critical Understanding:**
- This is **NOT** sequential execution (not A→B→C→D)
- This is **simultaneous** satisfaction of all conditions (A ∧ B ∧ C ∧ D)
- ALL conditions must be TRUE for the action to succeed
- If ANY condition is FALSE, the entire action fails

**Debugger Implications:**
- Hitting a breakpoint at Line A means TLC is **attempting** to evaluate Line A
- It does **NOT** mean:
  - Condition1 is TRUE
  - Lines B, C, D will be executed
- To know if a condition is TRUE, you must **inspect the value** at that breakpoint

### 2.2 Existential Quantification

```tla
\E i,j \in Server : \E b,e \in Range : Action(i,j,b,e)
```

**Semantics:**
- TLC tries **all possible combinations** of (i, j, b, e)
- If **at least one** combination makes Action TRUE, the entire expression is TRUE
- If **all combinations** fail, the entire expression is FALSE

**Debugger Behavior:**
- A breakpoint inside Action will be hit **multiple times** (once per combination)
- Each hit may have different values of (i, j, b, e)
- Hitting the breakpoint N times means TLC tried N different combinations
- Never hitting subsequent lines means all N combinations failed some condition

### 2.3 Definition vs. Variable

```tla
VARIABLE x           -- x is a state variable
foo == expression    -- foo is a DEFINITION (constant expression)
```

**Differences:**
- **Variable**: Independent state that can be assigned (`x' = value`)
- **Definition**: Derived expression, always computed from current state
- **logline** is a definition, so it always reflects `TraceLog[l]` in the current state

## 3. Debugger Breakpoint Semantics

### 3.1 What "Breakpoint Hit" Means

```
Breakpoint hit at Line X = TLC is attempting to evaluate Line X
Breakpoint hit ≠ Condition at Line X is TRUE
```

**Example:**
```
Function call:
  Line 323: /\ LoglineIsMessageEvent("SendAppendEntriesRequest", i, j)
  Line 324: /\ logline.event.msg.type = "MsgApp"
  Line 325: /\ range[1] = logline.event.msg.index + 1
  Line 327: /\ AppendEntries(i, j, range)

Breakpoint statistics:
  Line 323: 18 hits  → TLC tried 18 different (i,j,range) combinations
  Line 327: 0 hits   → Line 327 never executed (Lines 323-326 conditions failed)
```

**Interpretation:**
- Line 323 hit 18 times: TLC entered this function 18 times
- Line 327 hit 0 times: **None** of the 18 attempts passed all conditions (323-326)

### 3.2 Conditional Breakpoints

**Syntax:**
```python
breakpoint = {
    "line": 323,
    "condition": "l = 29 /\\ i = 1 /\\ j = 2"
}
```

**Why Essential:**
- Same code line executes at different `l` values
- Same function called with different parameters (i, j, range)
- Without conditions: too much noise, cannot focus on specific scenario

**Best Practices:**
- Use `l = N` to focus on a specific trace line validation
- Add parameter constraints to focus on specific combinations
- Combine multiple conditions with `/\\` (AND) or `\\/` (OR)

## 4. Common Pitfalls

### 4.1 Misunderstanding `l` Semantics

❌ **WRONG:** "l=29 means successfully validated 29 lines, now validating line 30"

✅ **CORRECT:** "l=29 means currently validating TraceLog[29] (the 29th line)"

**Impact:** Leads to debugging the wrong trace line

### 4.2 Confusing Breakpoint Hit with Condition Success

❌ **WRONG:** "Line 323 hit 18 times means the condition passed 18 times"

✅ **CORRECT:** "Line 323 hit 18 times means TLC **attempted** 18 combinations, but may have failed at 324, 325, or 326"

**Impact:** Misidentifies where the failure occurs

### 4.3 Assuming Sequential Execution

❌ **WRONG:** "Lines execute in order: 323 → 324 → 325 → 326 → 327"

✅ **CORRECT:** "All lines (323-327) must be simultaneously TRUE; TLC may evaluate in any order"

**Impact:** Wrong expectations about execution flow

### 4.4 Not Inspecting Variable Values

❌ **WRONG:** Setting breakpoint and seeing it hit, then assuming condition is TRUE

✅ **CORRECT:** Setting breakpoint, inspecting variable values, then evaluating condition manually

**Impact:** Missing the actual reason for failure

## 5. Essential Knowledge Checklist

Before debugging trace validation, an agent should know:

- [ ] What `l=N` means (currently validating TraceLog[N])
- [ ] `logline` is a definition, not a variable
- [ ] TraceLog indexing starts at 1
- [ ] How to interpret "M states generated" (validated TraceLog[1] through TraceLog[M])
- [ ] Conjunction is simultaneous satisfaction, not sequential execution
- [ ] Breakpoint hit means "attempting to evaluate", not "condition is TRUE"
- [ ] Existential quantifiers cause multiple breakpoint hits with different parameter values
- [ ] Must inspect variable values to determine why a condition failed
- [ ] Never assume variables have expected values; always verify

## 6. Quick Reference

### State Correspondence Table

| TLC Output | State Number | l Value | Validating Line |
|------------|--------------|---------|-----------------|
| State 0 | 0 | 1 | TraceLog[1] |
| State 1 | 1 | 2 | TraceLog[2] |
| State N-1 | N-1 | N | TraceLog[N] |
| "N states generated" | 0 to N-1 | 1 to N | Failed at TraceLog[N] |

### Validation Success/Failure

```
Success:
  Current state: l = N
  → Validate TraceLog[N]
  → All conditions TRUE
  → StepToNextTrace: l' = N+1
  → Next state: l = N+1

Failure:
  Current state: l = N
  → Validate TraceLog[N]
  → Some condition FALSE
  → Cannot execute StepToNextTrace
  → No next state generated
  → TLC stops with "N states generated"
```

### Debugging Decision Tree

```
TLC reports "N states generated"
  ↓
Failed to validate TraceLog[N]
  ↓
Set breakpoints in TraceNext branches with condition "l = N"
  ↓
Identify which branch is relevant (e.g., SendAppendEntriesRequest)
  ↓
Set breakpoints at each condition in that branch
  ↓
Identify last successful condition and first failed condition
  ↓
At first failed condition, inspect variable values
  ↓
Determine why condition is FALSE
```
