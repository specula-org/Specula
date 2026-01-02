# Trace Validation Debugging Guide

This document describes how to systematically debug TLA+ Trace Validation failures.

## Core Principles

**Layered Debugging: From Coarse to Fine, Layer by Layer**

Don't try to find the root cause all at once. Instead:
1. Start with coarse-grained localization of the problem scope
2. Then dive into fine-grained problem details
3. Finally examine the specific failure reason

**Tool Usage Principles:**
- Tools should NOT "auto-layer" or "auto-set breakpoints"
- Agents should proactively decide where to set breakpoints based on current findings
- Each layer of debugging answers a specific question

---

## Step 1: Understand the Problem

### 1.1 Interpret TLC Output

```
Example TLC output:
"29 states generated, 0 states left on queue"
Error: Invariant TraceMatched is violated
```

**Key Questions:**
- How many states did TLC generate? (e.g., 29)
- What does this mean?
  - State 1: l=1
  - State 29: l=29
  - Failed to generate State 30 from l=29
- **Which trace line failed validation?**
  - Answer: TraceLog[29] (NOT TraceLog[30]!)

### 1.2 Check the Trace File

```bash
# View the failing line (e.g., line 29)
sed -n '29p' trace.ndjson | jq .

# View surrounding lines for context
sed -n '27,31p' trace.ndjson | jq -c .
```

**Understand:**
- What event is this line? (SendAppendEntriesRequest, Commit, etc.)
- Which nodes are involved? (from, to)
- What are the key parameters? (index, entries, term)

---

## Step 2: Coarse-Grained Localization (Find the Relevant Code Branch)

### 2.1 Goal

Answer the question: **Which branch/function in the spec is responsible for validating this line?**

### 2.2 Method

**Set breakpoints at key entry points and branches:**

```python
# Example: Assuming failure at TraceLog[29] (TLC generated 29 states)
breakpoints = [
    (522, "TraceNext entry"),           # TraceNext entry point
    (480, "TraceNextNonReceiveActions"),  # Non-receive message branch
    (512, "TraceNextReceiveActions"),     # Receive message branch

    # Specific event branches
    (489, "SendAppendEntriesRequest branch"),
    (487, "Commit branch"),
    (483, "BecomeLeader branch"),
]

# All breakpoints use the same condition
# Important: Use TLCGet("level") instead of l, as l may not be visible in some files
condition = 'TLCGet("level") = 29'
```

**After running, check:**
- Which breakpoints were hit?
- Which breakpoints were not hit?

**Conclusion:**
- Hit branches = relevant code paths
- Unhit branches = irrelevant, can be ignored

### 2.3 Example

```
Results:
  Line 522 (TraceNext entry):              1 hit  ✅
  Line 480 (TraceNextNonReceiveActions):   1 hit  ✅
  Line 489 (SendAppendEntriesRequest):     1 hit  ✅
  Line 487 (Commit branch):                0 hits ❌
  Line 512 (TraceNextReceiveActions):      0 hits ❌

Conclusion:
  Problem is in the SendAppendEntriesRequest branch
```

---

## Step 3: Fine-Grained Localization (Find the Failing Condition)

### 3.1 Goal

Answer the question: **Within the relevant code branch, which condition failed?**

### 3.2 Method

**Set breakpoints at each condition statement in the relevant branch:**

Assuming Step 2 identified the problem in the `AppendEntriesIfLogged` function (Lines 323-328):

```tla
AppendEntriesIfLogged(i, j, range) ==
    /\ LoglineIsMessageEvent("SendAppendEntriesRequest", i, j)  -- 323
    /\ logline.event.msg.type = "MsgApp"                        -- 324
    /\ range[1] = logline.event.msg.index + 1                   -- 325
    /\ range[2] = range[1] + logline.event.msg.entries          -- 326
    /\ AppendEntries(i, j, range)                               -- 327
    /\ ValidateAfterAppendEntries(i, j)                         -- 328
```

**Set breakpoints:**
```python
breakpoints = [
    (323, 'TLCGet("level") = 29', "AppendEntriesIfLogged entry"),
    (327, 'TLCGet("level") = 29', "AppendEntries call"),
    (328, 'TLCGet("level") = 29', "ValidateAfterAppendEntries call"),
]
```

**After running, check:**
```
Results:
  Line 323: 18 hits  ✅
  Line 327: 1 hit    ✅ ← Action was called
  Line 328: 0 hits   ❌

Conclusion:
  - Line 323 was called 18 times (18 different i,j,range combinations)
  - Line 327 was hit 1 time (AppendEntries action was called/entered)
  - Line 328 was never executed (AppendEntries action failed)
  - **Key:** Line 327 is an action call, it gets hit even if the action returns FALSE
  - Problem is inside the AppendEntries action
```

**Important:** Line 327 is an action call (`AppendEntries(i, j, range)`):
- Action calls get hit even if the action fails internally (returns FALSE)
- Line 327: 1 hit means the action was entered
- Line 328: 0 hits means the action failed, the whole function cannot continue
- **Next step: Need to set breakpoints inside the AppendEntries action**

---

## Step 4: Dive Into Function Internals (If Needed)

### 4.1 When to Dive Deeper

If Step 3 finds that a **function call** never succeeded (e.g., Line 327's `AppendEntries(i, j, range)`), and all previous conditions are satisfied, then you need to dive into the function internals.

### 4.2 Method

**Set breakpoints inside the called function:**

Assuming `AppendEntries` calls `AppendEntriesInRangeToPeer` (in etcdraft_progress.tla):

```tla
AppendEntriesInRangeToPeer(subtype, i, j, range) ==
    /\ i /= j                                                   -- 436
    /\ range[1] <= range[2]                                     -- 437
    /\ state[i] = Leader                                        -- 438
    /\ j \in GetConfig(i) \union GetOutgoingConfig(i) \union ... -- 439
    /\ (subtype = "heartbeat" \/ ~IsPaused(i, j))               -- 443
    /\ LET ... IN /\ Send(...) /\ ...                           -- 444-502
```

**Set breakpoints:**
```python
# Note: This function is in a different file (etcdraft_progress.tla)
# Must use TLCGet("level") because l is not visible in this file
condition = 'i = 1 /\\ j = 2 /\\ TLCGet("level") = 29'

breakpoints = [
    ("etcdraft_progress.tla", 436, condition, "i /= j"),
    ("etcdraft_progress.tla", 437, condition, "range[1] <= range[2]"),
    ("etcdraft_progress.tla", 438, condition, "state[i] = Leader"),
    ("etcdraft_progress.tla", 439, condition, "j in Config/Learners"),
    ("etcdraft_progress.tla", 443, condition, "heartbeat or ~IsPaused"),
    ("etcdraft_progress.tla", 474, condition, "Send operation"),
]
```

**After running, check:**
```
Results:
  Line 436: 204 hits  ✅
  Line 437: 136 hits  ✅
  Line 438: 106 hits  ✅
  Line 439: 0 hits    ❌  ← First line never hit
  Line 443: 0 hits    ❌
  Line 474: 0 hits    ❌

Conclusion (using short-circuit evaluation pattern):
  - Line 436 was evaluated 204 times (all attempts check this condition)
  - 68 attempts failed at Line 436 (204 - 136 = 68)
  - 30 attempts failed at Line 437 (136 - 106 = 30)
  - 106 attempts passed Line 438, but all failed at Line 439
  - **Key finding**: All attempts stopped at Line 439 (no attempts passed Line 439)
  - Problem is at Line 439's condition: j \in GetConfig(...)
```

**Important Understanding: Short-Circuit Evaluation**

TLA+'s `/\` operator uses short-circuit evaluation, like C++'s `&&`:
- Later conditions are only evaluated if all previous conditions are TRUE
- Decreasing hit counts (204 → 136 → 106 → 0) show this process
- The first 0 hits line is the failure point

### 4.3 Key Pattern: How to Identify the Failure Point

**Breakpoint Hit Pattern (Short-Circuit Evaluation):**
```
Line A: 100 hits
Line B: 50 hits
Line C: 20 hits  ← Last non-zero hit
Line D: 0 hits   ← First 0 hits
Line E: 0 hits
Line F: 0 hits
```

**Identification Method: Find the last non-zero hit line (Line C), determine its type**

**Case 1: Line C is an action call**
```tla
/\ SomeCondition        -- Line B: 50 hits
/\ SomeAction(i, j)     -- Line C: 20 hits  ← Action call
/\ AnotherCondition     -- Line D: 0 hits
```

**Characteristics:**
- Line C's code looks like `SomeAction(params)` or `LET ... IN action`
- It's a function/operator call, not a simple condition check

**Conclusion:**
- Action was called/entered 20 times
- All 20 calls failed internally (returned FALSE)
- Line D was not executed because Line C failed

**Next step:**
- Set breakpoints **inside** the action (using the same condition)
- Find which internal condition failed

**Case 2: Line C is a condition statement**
```tla
/\ SomeCondition        -- Line B: 50 hits
/\ i /= j               -- Line C: 20 hits  ← Simple condition
/\ AnotherCondition     -- Line D: 0 hits
```

**Characteristics:**
- Line C is a simple condition check (equality, inequality, set membership, etc.)
- Not a function call

**Conclusion:**
- 20 attempts passed Line C's condition
- All 20 attempts failed at Line D's condition

**Next step:**
- Set breakpoint at Line C (or when breakpoint triggers)
- Check variable values to see why Line D's condition is not satisfied

**How to Distinguish Action Calls from Condition Statements:**

Look at the TLA+ source code:
```tla
/\ i /= j                                     -- Condition statement
/\ range[1] <= range[2]                       -- Condition statement
/\ state[i] = Leader                          -- Condition statement
/\ AppendEntriesInRangeToPeer(i, j, range)    -- Action call ← Note capitalization
/\ Send([type |-> "MsgApp", ...])             -- Action call
```

General rule:
- **Condition statements**: Comparisons, membership tests, boolean expressions
- **Action calls**: Capitalized operators, or obvious function calls

---

## Step 5: Examine Failure Reasons

### 5.1 Goal

Answer the question: **Why did this condition fail? What are the values of related variables?**

### 5.2 Method

**Set breakpoint at the line before the failing condition, check variable values:**

Assuming Step 4 identified the problem at Line 439 (`j \in GetConfig(i) \union GetOutgoingConfig(i) \union GetLearners(i)`), we should set a breakpoint at Line 438:

```python
# Breakpoint at Line 438 (line before Line 439)
# Use TLCGet("level") and parameter conditions
breakpoint = {
    "file": "etcdraft_progress.tla",
    "line": 438,
    "condition": 'i = 1 /\\ j = 2 /\\ TLCGet("level") = 29'
}

# When breakpoint hits, check variables
i_val = get_variable_value(frame_id, "i")
j_val = get_variable_value(frame_id, "j")

# Evaluate Line 439's condition
config = evaluate_expression(frame_id, f'GetConfig({i_val})')
outgoing = evaluate_expression(frame_id, f'GetOutgoingConfig({i_val})')
learners = evaluate_expression(frame_id, f'GetLearners({i_val})')
union = evaluate_expression(frame_id,
    f'GetConfig({i_val}) \\union GetOutgoingConfig({i_val}) \\union GetLearners({i_val})')

# Check if j is in the set
j_in_set = evaluate_expression(frame_id,
    f'{j_val} \\in GetConfig({i_val}) \\union GetOutgoingConfig({i_val}) \\union GetLearners({i_val})')

print(f"i={i_val}, j={j_val}")
print(f"GetConfig({i_val}) = {config}")
print(f"GetOutgoingConfig({i_val}) = {outgoing}")
print(f"GetLearners({i_val}) = {learners}")
print(f"Union = {union}")
print(f"j in Union? {j_in_set}")
```

### 5.3 Example Output

```
i=1, j=2
GetConfig(1) = {"1"}
GetOutgoingConfig(1) = {}
GetLearners(1) = {}
Union = {"1"}
j in Union? FALSE  ❌

Problem: j=2 is not in the Union set!
```

**Root cause discovered:**
- When l=29, GetConfig(1) only contains node 1 itself
- j=2 is not in the set, so the condition fails
- This is a configuration state issue

---

## Step 6: Verify and Expand

### 6.1 Verify Assumptions

After finding a potential cause, you should verify:

**Compare successful and failed cases:**
```python
# Check GetConfig(1) at l=28 (success)
# vs l=29 (failure)

# Check at both l=28 and l=29
for level in [28, 29]:
    # Set breakpoint condition: l = level
    # Check GetConfig(1) value
    # Compare differences
```

**Check multiple different (i, j) combinations:**
```python
# Don't just check i=1, j=2
# Also check i=1, j=3; i=2, j=1, etc.

# See if all combinations fail
# Or only specific combinations fail
```

### 6.2 Expand Investigation

If you need to understand "why GetConfig(1) only has {1}", you may need to:
- Check earlier states (l=1, l=2, ...)
- See how the configuration was modified
- Check ChangeConf, ApplyConfChange events

---

## Methodology Summary

### General Debugging Flow

```
1. Understand the Problem
   ├─ Interpret TLC output (which l value failed?)
   ├─ View trace file (what event is this line?)
   └─ Clarify the question to answer

2. Coarse-Grained Localization
   ├─ Set breakpoints at main branch entry points
   ├─ Determine which branch was executed
   └─ Narrow down the problem scope

3. Fine-Grained Localization
   ├─ Set breakpoints at each condition in the relevant branch
   ├─ Find "last success" and "first failure" lines
   └─ Determine the specific failure point

4. Dive Into Functions (if needed)
   ├─ If failure point is a function call, enter the function
   ├─ Repeat step 3 (set breakpoints inside the function)
   └─ Find the internal failure point

5. Examine Failure Reasons
   ├─ Set breakpoint at the line before the failing condition
   ├─ Check all related variable values
   ├─ Evaluate the failing condition's expression
   └─ Understand why the condition is FALSE

6. Verify and Expand
   ├─ Compare successful and failed cases
   ├─ Check multiple different parameter combinations
   └─ If needed, trace back to earlier states
```

### Key Techniques

#### 1. Use Breakpoint Statistics Instead of Single-Stepping

**Not Recommended:**
```python
# Step through one by one
for i in range(1000):
    step_in()
    check_location()
```

**Recommended:**
```python
# Set multiple breakpoints at once, run, collect statistics
breakpoints = [(323, ...), (327, ...), (328, ...)]
run_and_collect_statistics()

# Output:
# Line 323: 18 hits
# Line 327: 0 hits   ← Directly see the problem here
```

**Reason:**
- Single-stepping is too slow, low information density
- Breakpoint statistics give a global view at once
- Easier to spot patterns and regularities

#### 2. Layer by Layer, Not All at Once

**Don't:**
```python
# Set breakpoints everywhere at once
breakpoints = [
    (323, ...), (327, ...), (328, ...),  # Layer 1
    (436, ...), (437, ...), (438, ...), (439, ...),  # Layer 2
    (474, ...), (489, ...), (493, ...),  # Layer 3
]
```

**Should:**
```python
# Round 1: Only Layer 1 breakpoints
breakpoints_layer1 = [(323, ...), (327, ...), (328, ...)]
result1 = run_and_check()

# If Line 327 not hit, problem is between 323-327
# Round 2: Dive into function called at Line 327 (Layer 2)
breakpoints_layer2 = [(436, ...), (437, ...), (438, ...), (439, ...)]
result2 = run_and_check()

# If Line 439 not hit, problem is between 438-439
# Round 3: Check variables at Line 438
```

**Reason:**
- Each layer answers a specific question
- Avoid information overload
- Decide next layer strategy based on previous layer results

#### 3. Conditional Breakpoints Filter Noise

**Scenario:**
- Same line executes at different trace depths
- Same function called multiple times with different parameters

**Solution:**
```python
# Only focus on specific trace depth (recommended to use TLCGet("level"))
condition = 'TLCGet("level") = 29'

# Only focus on specific parameter combinations
condition = 'i = 1 /\\ j = 2 /\\ TLCGet("level") = 29'

# Combine multiple conditions
condition = 'i = 1 /\\ range[1] = 6 /\\ range[2] = 7 /\\ TLCGet("level") = 29'
```

**Important: Why use TLCGet("level") instead of l**
- `l` is a variable defined in the Trace wrapper spec
- When breakpoints are in the base spec (e.g., etcdraft_progress.tla), `l` may not be in scope
- `TLCGet("level")` is a TLC built-in function, available in all files and contexts
- During the transition validating TraceLog[N] (l=N), `TLCGet("level") = N`, so TLCGet("level") can precisely locate

#### 4. Check Variables, Don't Assume

**Don't assume:**
```python
# "Line 438 was hit, so state[i] = Leader must be TRUE"
# ❌ Wrong! Breakpoint hit doesn't mean condition is TRUE
```

**Should verify:**
```python
# At Line 438 breakpoint
i_val = get_variable_value(frame_id, "i")
state_i = evaluate_expression(frame_id, f'state["{i_val}"]')
condition = (state_i == "StateLeader")

print(f"state[{i_val}] = {state_i}, condition = {condition}")
```

---

## Common Pitfalls

### Pitfall 1: Misunderstanding l Semantics

❌ **Wrong understanding:** "l=29 means 29 lines have been validated, now validating line 30"

✅ **Correct understanding:** "l=29 means currently validating line 29 (TraceLog[29])"

**Consequence:** Looking at the wrong trace line, leading to debugging in the wrong direction.

### Pitfall 2: Confusing Breakpoint Hit with Condition Satisfaction

❌ **Wrong understanding:** "Line 323 hit 18 times means the condition passed 18 times"

✅ **Correct understanding:** "Line 323 hit 18 times means TLC **attempted** 18 times, but all may have failed"

**Consequence:** Mistakenly believe the condition is satisfied, not checking subsequent failure reasons.

### Pitfall 3: Assuming Sequential Execution

❌ **Wrong understanding:** "Code executes in order: Line 323 → 324 → 325 → 326 → 327"

✅ **Correct understanding:** "All lines must be TRUE simultaneously; TLC uses short-circuit evaluation (typically top to bottom)"

**Consequence:** Wrong expectations about execution flow, leading to setting breakpoints in wrong positions.

### Pitfall 4: Diving Into Details Too Early

❌ **Wrong approach:** Setting breakpoints on every line inside functions from the start

✅ **Correct approach:** First coarse-grained localization to relevant branches, then layer by layer

**Consequence:** Information overload, cannot focus on key points, waste time.

---

## Debugging Checklist

Before starting debugging, confirm you have:

- [ ] Understood l semantics (l=N means currently validating TraceLog[N])
- [ ] Know logline is a definition, not a variable
- [ ] Know TraceLog indexing starts at 1
- [ ] Can interpret TLC output (what "M states generated" means)
- [ ] Understand conjunction is simultaneous satisfaction, not sequential execution
- [ ] Know breakpoint hit doesn't mean condition is TRUE
- [ ] Ready for layered debugging, not diving deep all at once

For each layer of debugging, confirm you:

- [ ] Clearly defined the question this layer should answer
- [ ] Set appropriate conditional breakpoints (filter out noise)
- [ ] Collected breakpoint statistics (not single-stepping)
- [ ] Identified "last success" and "first failure" positions
- [ ] Checked actual values of related variables (not assuming)
- [ ] Understood why a certain condition failed
- [ ] Decided whether to dive deeper or expand investigation next

---

## Summary

**Core Idea: Layered Debugging**
- Don't try to find the root cause all at once
- Each layer answers a specific question
- Decide next layer strategy based on current layer findings

**Key Tool: Breakpoint Statistics**
- Set multiple breakpoints at once
- Collect hit statistics
- Identify "first failure" position

**Essential Skill: Variable Inspection**
- Don't assume variable values
- Check actual values at key positions
- Understand why conditions are FALSE

**Most Important:**
- Be patient, systematically dive layer by layer
- Peel back layer by layer, you will eventually find the inconsistency
- Let data (breakpoint statistics, variable values) guide your next action
