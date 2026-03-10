## Bug Confirmation and Reproduction Guide

### Phase 1: Code Audit

Before attempting reproduction, you **must** first confirm the bug's validity by reading the source code.

1. **Locate the relevant code**: Find the specific functions and lines mentioned in the bug report. Read these functions in full and understand their context.
2. **Trace the call chain**: Starting from public APIs or entry points, trace the path to the buggy code. Confirm whether this path is reachable during normal usage.
3. **Check for existing safeguards**: Check whether callers already have precondition checks, lock guards, or other mechanisms that prevent this bug from being triggered in practice. If they do, the bug is a false positive — report it and stop.
4. **Construct a trigger scenario**: Describe in words a concrete sequence of events that could naturally occur at the user/system level and would reach the buggy code path. If you cannot construct one, the bug is likely a false positive.

Only proceed to Phase 2 after completing the above steps and being confident the bug is real.

### Phase 2: Low-Invasiveness Reproduction

The core principle: **simulate a real-world trigger, not bypass normal flows to poke the bug directly.**

**Prohibited approaches:**
- Pre-populating data structures with illegal or inconsistent state, then calling a function to "prove" it can't handle it
- Directly calling internal/private functions, skipping normal entry-point checks
- Manually constructing inputs that could never occur through normal flows
- Modifying the code under test to create the bug (e.g., commenting out validation logic)

**Correct approaches:**
- Trigger through the system's public interfaces or normal entry points
- For concurrency bugs, reproduce via real concurrent scenarios (multi-thread/multi-process). Small delays may be inserted into the code under test to widen the race window, but the logic must not be altered
- For protocol bugs, trigger via sequences of messages that are legitimate but adversarial. The messages themselves must pass the system's normal validation
- The reproduction program should compile and run independently, without requiring special environments beyond the test framework
- The success criterion must be observable anomalous behavior (crash, deadlock, data inconsistency, safety property violation), not "some intermediate variable has an unexpected value"

**Criteria for successful reproduction:**
- The bug is triggered without modifying the core logic of the system under test
- The trigger path is consistent with real-world usage scenarios
- The reproduction is deterministic, or triggers with significant probability across multiple runs
- The erroneous behavior caused by the bug is clearly observable

**If reproduction fails:**
- Explain what approaches were attempted and why they failed
- Analyze whether the bug itself is a false positive, or whether the trigger conditions are difficult to satisfy in the current test environment
- Do not lower the bar of reproduction authenticity just to claim "reproduction succeeded"
