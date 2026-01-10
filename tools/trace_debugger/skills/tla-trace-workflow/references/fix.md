# Phase 3: Fixing Spec/Trace Inconsistencies

This document provides guidance for fixing issues identified during debugging.

## Overview

After Phase 2 (Debugging), you should know:
1. Which trace line failed validation
2. Which specific condition in the spec failed
3. What the actual variable values were vs expected values

**Before fixing, you must first identify the error type.** Different error types require different fix strategies.

---

## Error Classification

### Type 1: Inconsistency Error (Spec Bug)

**Definition:** The spec and the system are genuinely inconsistent. The spec has incorrect modeling.

**Examples:**
- A condition uses `< 1` but the system uses `<= 1`
- An action branch is missing or incorrectly structured
- State transitions don't match system behavior
- Field mappings are wrong

**Characteristics:**
- The spec is objectively wrong about how the system works
- The spec needs to be fixed to match the system's actual behavior

### Type 2: Abstraction Gap

**Definition:** The spec is not wrong, but there's a gap between the abstraction level of the spec and the system, making trace validation fail.

**Examples:**
- System supports multi-node config changes in one log entry; spec only supports one node at a time
- System has optimizations that combine multiple operations; spec models them separately
- System has implementation details not modeled in spec
- Timing or ordering differences due to abstraction

**Characteristics:**
- The spec is correct at its abstraction level
- The gap exists because spec and system operate at different granularities
- Multiple valid fix strategies exist

---

## Fix Principles

### Principle 1: Identify Error Type First

Before making any changes, determine which type of error you're dealing with:

1. **Ask yourself:** Is the spec objectively wrong about system behavior, or is it just at a different abstraction level?
2. **If uncertain:** Read the system code to understand the actual behavior
3. **Classify correctly** before proceeding - wrong classification leads to wrong fixes

**If still uncertain about error type:** Treat it as an Abstraction Gap and ask the user for clarification.

### Principle 2: For Inconsistency Errors - Fix the Spec

**Fix location priority:**
1. **Base spec** (e.g., `etcdraft.tla`) - modeling logic
2. **Trace comparison logic** (e.g., `Traceetcdraft.tla`) - only when absolutely necessary

**Why avoid modifying trace comparison logic?**
- Modifying comparison logic may cause **false positives** (validation passes but spec is still wrong)
- Our goal is to get a **high-quality spec** that can find bugs
- The spec itself should accurately model the system

**Only modify trace comparison logic when there is no other option.** When you do, document the reason clearly.

**Before modifying:**
1. **Read the system source code** to understand the actual behavior
2. **Find the corresponding code location** that proves your fix is correct
3. **Document the evidence** (file path, line number, code snippet)

### Principle 3: For Abstraction Gaps - Ask for Guidance

**When you identify an abstraction gap, STOP and ask the user.**

**Why?**
- Multiple valid fix strategies exist:
  - Modify spec logic to support the system's behavior
  - Modify trace comparison logic to bridge the gap
  - Modify system instrumentation to change trace generation
- The choice depends on **design decisions about abstraction granularity**
- Agent lacks the experience to make these architectural decisions

**How to report to user:**
1. Describe the gap clearly
2. Explain what the spec models vs what the system does
3. List possible fix strategies
4. Ask for guidance on which approach to take

### Principle 4: Document Every Fix

**After each fix, write to `fix_log.md` in the spec directory.**

**Content should include:**
- Date and trace file that revealed the issue
- Error type (Inconsistency Error or Abstraction Gap)
- Brief description of the inconsistency
- Fix strategy chosen
- Files modified

**Keep it concise** - just enough for the user to review.

---

## Fix Workflow

### For Inconsistency Errors

```
1. Identify Error Type
   └── Confirm it's an inconsistency error (spec is objectively wrong)

2. Understand Root Cause
   ├── Which spec condition/action is wrong?
   └── What is the correct behavior?

3. Read System Code
   ├── Find the corresponding system code
   ├── Understand the actual implementation
   └── Identify evidence for your fix

4. Make the Fix
   ├── Modify base spec (preferred) or trace comparison logic (if necessary)
   ├── Make minimal, focused changes
   └── Don't refactor unrelated code

5. Verify
   ├── Run validate_spec_syntax
   ├── Run run_trace_validation on failing trace
   └── Test with other traces for regression

6. Document
   └── Write to fix_log.md
```

### For Abstraction Gaps

```
1. Identify Error Type
   └── Confirm it's an abstraction gap (spec is correct but at different level)

2. Understand the Gap
   ├── What does the spec model?
   ├── What does the system do?
   └── Why is there a gap?

3. Read System Code
   ├── Understand the system's actual behavior
   └── Identify what creates the gap

4. STOP and Ask User
   ├── Report the gap clearly
   ├── List possible fix strategies:
   │   ├── Option A: Modify spec to support system's behavior
   │   ├── Option B: Modify trace comparison logic
   │   └── Option C: Modify system instrumentation
   └── Wait for user guidance

5. After User Guidance
   ├── Implement the chosen strategy
   ├── Verify the fix
   └── Document in fix_log.md
```

---

## fix_log.md Format

Create or append to `fix_log.md` in the spec directory:

```markdown
## [YYYY-MM-DD] - [Brief Title]

**Trace:** `path/to/trace.ndjson`
**Error Type:** Inconsistency Error / Abstraction Gap

**Issue:**
[Brief description of what was inconsistent]

**Root Cause:**
[What caused the inconsistency - reference system code if applicable]

**Fix:**
[What was changed and why]

**Files Modified:**
- `filename.tla`: [brief description of change]
```

**Example:**

```markdown
## YYYY-MM-DD - Incorrect term comparison in RequestVote

**Trace:** `../traces/leader_election.ndjson`
**Error Type:** Inconsistency Error

**Issue:**
RequestVote rejected valid votes because term comparison used `>` instead of `>=`.

**Root Cause:**
System code in `raft/raft.go:1234` accepts votes when `msg.Term >= r.Term`, but spec used `msg.term > currentTerm[i]`.

**Fix:**
Changed condition from `msg.term > currentTerm[i]` to `msg.term >= currentTerm[i]`.

**Files Modified:**
- `etcdraft.tla`: Line 456, fixed term comparison in HandleRequestVoteRequest
```

---

## Summary

| Error Type | Fix Location | Action |
|------------|--------------|--------|
| Inconsistency Error | Base spec (preferred) | Fix spec to match system, document evidence |
| Abstraction Gap | Depends on user guidance | STOP and ask user for direction |

**Remember:**
- Always identify error type first
- For inconsistency errors: read system code, fix spec, document
- For abstraction gaps: stop and ask user
- Document every fix in fix_log.md
