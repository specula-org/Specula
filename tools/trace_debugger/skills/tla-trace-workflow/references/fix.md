# Phase 3: Fixing Spec/Trace Inconsistencies

This document provides guidance for fixing issues identified during debugging.

> **Note:** This is a placeholder document. Detailed fix patterns will be added as common issues are identified and documented.

## Overview

After Phase 2 (Debugging), you should know:
1. Which trace line failed validation
2. Which specific condition in the spec failed
3. What the actual variable values were vs expected values

The fix depends on the root cause:

| Root Cause | Fix Location |
|------------|--------------|
| Spec bug | TLA+ specification |
| Trace bug | Trace generation code |
| Mapping issue | Event-to-action mapping |
| Missing handling | Add new case to spec |

---

## Common Fix Patterns

### Pattern 1: Missing Action Branch

**Symptom:** Trace event has no matching action in spec.

**Fix:**
1. Add a new disjunct to `TraceNext` for the event type
2. Define the corresponding action
3. Ensure action matches trace event semantics

### Pattern 2: Incorrect Field Mapping

**Symptom:** Field name in trace doesn't match spec expectation.

**Fix:**
1. Check trace JSON field names
2. Update spec to use correct field path (e.g., `logline.event.msg.index` vs `logline.event.index`)

### Pattern 3: Index Off-by-One

**Symptom:** Index validation fails, values differ by 1.

**Fix:**
1. Determine if trace uses 0-based or 1-based indexing
2. Adjust spec accordingly (add/subtract 1 in mapping)

### Pattern 4: State Precondition Not Met

**Symptom:** State check fails (e.g., `state[i] = Leader` is FALSE).

**Investigation:**
1. Check if earlier trace events should have updated state
2. May need to add/fix state update in earlier action

### Pattern 5: Configuration Mismatch

**Symptom:** Node membership check fails (e.g., `j \in GetConfig(i)`).

**Investigation:**
1. Check if configuration change events are handled
2. Verify config update timing in trace vs spec

---

## Fix Workflow

### Step 1: Confirm Root Cause

Before fixing, verify your hypothesis:
- Re-run debugging with additional breakpoints if needed
- Check multiple similar trace events
- Ensure the issue is consistent

### Step 2: Make Minimal Fix

- Fix only what's needed
- Don't refactor unrelated code
- Keep changes focused

### Step 3: Verify Fix

After making changes:
1. Run `validate_spec_syntax` to check for syntax errors
2. Run `run_trace_validation` on the original failing trace
3. Test with other traces to ensure no regression

### Step 4: Document

If the fix reveals a common pattern:
- Document it in this file
- Include example symptoms and solutions

---

## To Be Added

The following sections will be added as patterns are identified:

- [ ] Detailed examples of each fix pattern
- [ ] Common etcdraft-specific fixes
- [ ] Raft protocol inconsistency patterns
- [ ] Trace generation guidelines
- [ ] Spec writing best practices for trace validation
