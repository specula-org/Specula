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
Initial State (State 1):
  l = 1
  logline = TraceLog[1]

State 1 → State 2:
  1. Execute TraceNext
  2. logline = TraceLog[1] (validate first trace line)
  3. Check all conditions
  4. If success: StepToNextTrace, l' = 2
  5. Enter State 2 with l = 2

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
  - Successfully generated State 1 through State 29
  - State 1: l=1
  - State 2: l=2
  - ...
  - State 29: l=29

  - Attempted to generate State 30 from State 29
  - State 29 has l=29, so validating TraceLog[29]
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

## 3. TLCGet("level") and State Depth

### 3.1 Understanding TLCGet("level")

`TLCGet("level")` is a TLC built-in function that returns the **depth of the current state** in the state graph.

**Definition:**
- State depth = number of transitions from the initial state
- Initial state: `TLCGet("level") = 0` (or 1, depending on TLC version)
- After first transition: `TLCGet("level") = 1`
- After N transitions: `TLCGet("level") = N`

**In Trace Validation context:**
- Trace Validation validates trace lines sequentially
- Each Next action corresponds to validating one trace line
- `TLCGet("level")` increments after each state is computed

**Example correspondence:**
```
Initial state (State 1):
  l = 1, TLCGet("level") = 0

After validating TraceLog[1] (State 2):
  l = 2, TLCGet("level") = 1

After validating TraceLog[N-1] (State N):
  l = N, TLCGet("level") = N-1
```

**Important:** During the transition from State N to State N+1 (when validating TraceLog[N]):
- `l = N` (currently validating this trace line)
- `TLCGet("level") = N` (just computed State N)
- Therefore, use `TLCGet("level") = N` to breakpoint when validating TraceLog[N]

### 3.2 Update Timing of TLCGet("level")

Understanding when `TLCGet("level")` updates is crucial for using it in breakpoint conditions.

**Key Principle: TLCGet("level") returns the number of computed states, which increments after each state**

**Execution phases:**

1. **Action Evaluation Phase** (when breakpoints hit):
   - TLC is evaluating a Next action from state S_N to generate S_{N+1}
   - `TLCGet("level")` returns `N` (N states have been computed)
   - If validating TraceLog[29] (l=29), then `TLCGet("level") = 29`

2. **State Generation Phase** (after action succeeds):
   - TLC constructs a new state S_{N+1}
   - Now level = N+1 (N+1 states have been computed)
   - S_{N+1}.l = l' (new l value from the action)

**Example timeline:**
```
Current state: S_29 (l=29, level=28)
  ↓
Evaluate Next action to validate TraceLog[29]
  → During evaluation: TLCGet("level") = 29
  → All breakpoints hit with TLCGet("level") = 29
  ↓
Action succeeds
  ↓
Generate new state: S_30 (l=30, level=29)
  → Now TLCGet("level") = 30 (in the new state)
```

**Implication for debugging:**
- When validating TraceLog[N] (l=N), use `TLCGet("level") = N` in breakpoint conditions
- The level updates **after** the entire action completes, not during evaluation

## 4. Debugger Breakpoint Semantics

### 4.1 What "Breakpoint Hit" Means

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
  Line 327: 1 hit    → AppendEntries action was called/entered
```

**Interpretation:**
- Line 323 hit 18 times: TLC entered this function 18 times with different parameter combinations
- Line 327 hit 1 time: AppendEntries action was called/entered (even though it returned FALSE)
- Since Line 327 is an **action call**, it gets hit even when the action fails internally
- Since Line 327 is the last hit (subsequent lines have 0 hits), the action was entered but failed internally
- **Next step**: Set breakpoints INSIDE AppendEntries to find which internal condition failed

**IMPORTANT:** Actions that return FALSE still count as "hit" at their call site. Only conditions that evaluate to FALSE are not hit.

### 4.2 Conditional Breakpoints

**Syntax:**
```python
breakpoint = {
    "line": 436,
    "condition": 'i = 1 /\\ j = 2 /\\ TLCGet("level") = 29'
}
```

**Why Essential:**
- Same code line executes at different trace depths
- Same function called with different parameters (i, j, range)
- Without conditions: too much noise, cannot focus on specific scenario

**Best Practices:**
- **Use `TLCGet("level") = N`** to focus on a specific trace line validation (recommended)
- Add parameter constraints to focus on specific combinations
- Combine multiple conditions with `/\\` (AND) or `\\/` (OR)

**Important: Use TLCGet("level") instead of `l`**

While `l` represents the trace line number in Trace Validation specs, it may not be accessible in all execution contexts:

```python
# ❌ May not work in all contexts
"condition": "l = 29"

# ✅ Works everywhere - recommended
"condition": 'TLCGet("level") = 29'
```

**Why:**
- The variable `l` is defined in the Trace wrapper spec (e.g., `Traceetcdraft_progress.tla`)
- When breakpoints hit inside the base spec (e.g., `etcdraft_progress.tla`), `l` may not be in scope
- `TLCGet("level")` is a TLC built-in function, accessible from any file or context
- In Trace Validation, `TLCGet("level")` corresponds to the trace line number

## 5. Common Pitfalls

### 5.1 Misunderstanding `l` Semantics

❌ **WRONG:** "l=29 means successfully validated 29 lines, now validating line 30"

✅ **CORRECT:** "l=29 means currently validating TraceLog[29] (the 29th line)"

**Impact:** Leads to debugging the wrong trace line

### 5.2 Confusing Breakpoint Hit with Condition Success

❌ **WRONG:** "Line 323 hit 18 times means the condition passed 18 times"

✅ **CORRECT:** "Line 323 hit 18 times means TLC **attempted** 18 combinations, but may have failed at 324, 325, or 326"

**Impact:** Misidentifies where the failure occurs

### 5.3 Assuming Sequential Execution

❌ **WRONG:** "Lines execute in order: 323 → 324 → 325 → 326 → 327"

✅ **CORRECT:** "All lines (323-327) must be simultaneously TRUE; TLC evaluates them using short-circuit evaluation (typically top to bottom)"

**Impact:** Wrong expectations about execution flow

### 5.4 Not Inspecting Variable Values

❌ **WRONG:** Setting breakpoint and seeing it hit, then assuming condition is TRUE

✅ **CORRECT:** Setting breakpoint, inspecting variable values, then evaluating condition manually

**Impact:** Missing the actual reason for failure

### 5.5 Using `l` in Breakpoint Conditions

❌ **WRONG:** Using `l = 29` in breakpoint conditions for all files

✅ **CORRECT:** Using `TLCGet("level") = 29` which works in all contexts

**Impact:** Breakpoints may never trigger if `l` is not in scope

## 6. Essential Knowledge Checklist

Before debugging trace validation, an agent should know:

- [ ] What `l=N` means (currently validating TraceLog[N])
- [ ] `logline` is a definition, not a variable
- [ ] TraceLog indexing starts at 1
- [ ] How to interpret "M states generated" (validated TraceLog[1] through TraceLog[M])
- [ ] **Use `TLCGet("level") = N` instead of `l = N` in breakpoint conditions**
- [ ] What `TLCGet("level")` returns (current state depth) and when it updates
- [ ] Conjunction uses short-circuit evaluation (earlier conditions filter later ones)
- [ ] Breakpoint hit means "attempting to evaluate", not "condition is TRUE"
- [ ] Action calls get "hit" even when they return FALSE; check inside the action
- [ ] Existential quantifiers cause multiple breakpoint hits with different parameter values
- [ ] Must inspect variable values to determine why a condition failed
- [ ] Never assume variables have expected values; always verify

## 7. Quick Reference

### State Correspondence Table

| TLC Output | State Number | l Value | TLCGet("level") | Validating Line |
|------------|--------------|---------|-----------------|-----------------|
| State 1 | 1 | 1 | 0 | Initial state |
| State 2 | 2 | 2 | 1 | Validated TraceLog[1] |
| State N | N | N | N-1 | Validated TraceLog[N-1] |
| "N states generated" | 1 to N | 1 to N | 0 to N-1 | Failed at TraceLog[N] |

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
Set breakpoints in TraceNext branches with condition 'TLCGet("level") = N'
  ↓
Identify which branch is relevant (e.g., SendAppendEntriesRequest)
  ↓
Set breakpoints at each condition in that branch (use TLCGet("level") = N)
  ↓
Observe breakpoint hit counts (decreasing counts show short-circuit evaluation)
  ↓
Identify the last hit line:
  - If it's an action call → The action was entered but failed internally
  - If it's a condition → The next line's condition failed
  ↓
If action call: Set breakpoints INSIDE the action to find internal failure
If condition: Inspect variables to see why the next condition failed
  ↓
Determine why condition is FALSE
```

### Interpreting Breakpoint Hit Patterns

**Pattern 1: Decreasing hits (short-circuit evaluation)**
```
Line A: 100 hits
Line B: 50 hits
Line C: 20 hits
Line D: 0 hits  ← First zero

Interpretation:
- 50 attempts failed at Line B's condition
- 30 attempts failed at Line C's condition
- All attempts failed before reaching Line D
```

**Pattern 2: Last hit is an action call**
```
Line A (condition):   100 hits
Line B (condition):   50 hits
Line C (action call): 20 hits  ← Last non-zero
Line D (condition):   0 hits

Interpretation:
- The action at Line C was called 20 times
- All 20 calls failed internally
- Next step: Set breakpoints INSIDE the action
```

**Pattern 3: Last hit is a condition**
```
Line A (condition): 100 hits
Line B (condition): 50 hits
Line C (condition): 20 hits  ← Last non-zero
Line D (condition): 0 hits

Interpretation:
- 20 attempts satisfied Line C
- All 20 failed at Line D's condition
- Next step: At Line C, inspect variables to see why Line D fails
```
