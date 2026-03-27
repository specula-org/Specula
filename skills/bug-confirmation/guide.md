## Bug Confirmation and Reproduction Guide

### Phase 1: Code Audit

Before attempting reproduction, you **must** first confirm the bug's validity by reading the source code.

1. **Locate the relevant code**: Find the specific functions and lines mentioned in the bug report. Read these functions in full and understand their context.
2. **Trace the call chain**: Starting from public APIs or entry points, trace the path to the buggy code. Confirm whether this path is reachable during normal usage.
3. **Check for existing safeguards**: Check whether callers already have precondition checks, lock guards, or other mechanisms that prevent this bug from being triggered in practice. If they do, the bug is a false positive — report it and stop.
4. **Construct a trigger scenario**: Describe in words a concrete sequence of events that could naturally occur at the user/system level and would reach the buggy code path. If you cannot construct one, the bug is likely a false positive.

Only proceed to Phase 1.5 after completing the above steps and being confident the code path is reachable.

### Phase 1.5: Developer Intent Investigation

A bug is defined by the developers' own requirements and expectations — not by the researcher's intuition about what should be correct. Before investing effort in reproduction, investigate what the developers themselves believe about this behavior.

**What to investigate:**

1. **Issue tracker**: Search for open and closed issues, PRs, and discussions mentioning the relevant code, function names, or the behavior in question. Developers may have already discussed this exact scenario.
2. **Commit messages and PR discussions**: Use `git log` and `git blame` on the affected code. Read the commit messages and linked PRs to understand why the code was written this way. Look for statements of intent ("this is a trade-off", "we accept this because...", "this should be safe even if...").
3. **Code comments and documentation**: Look for comments near the code (TODOs, FIXMEs, "known issue", "by design", "trade-off"), as well as design documents, RFCs, or architecture docs in the repository.
4. **Test cases**: Check what the existing tests assert. Tests encode developer expectations — if a test explicitly sets up the scenario you found and asserts the current behavior, the developers likely consider it correct.

**How to use what you find:**

- **Developer says "we know about this, it's a deliberate trade-off"** → Classify as NOT a bug unless you can show their trade-off analysis is flawed (e.g., they accepted a liveness cost but didn't realize it also affects safety).
- **Developer says "this should be safe even under condition X"** → If your counterexample shows it is NOT safe under condition X, this IS a bug — the developers' own stated requirement is violated.
- **No developer commentary found** → Fall back to code quality analysis: assess whether the behavior constitutes a bug based on established engineering standards (e.g., violating API contracts, ignoring error returns, TOCTOU races, missing atomicity). These are bugs by any reasonable standard regardless of developer intent. Note the absence of developer evidence in your report and explain which engineering principle the code violates.

The two symmetric cases above are the key insight: developer intent can both _dismiss_ a finding that looks like a bug to a researcher, and _validate_ a finding that a researcher would have dismissed. Always let the evidence speak.

**Report what you find**: Whether the investigation confirms or refutes the bug, include a brief summary of the developer evidence in your final report. This makes the finding credible and actionable.

Only proceed to Phase 2 after completing the above steps and being confident the bug is real and that developers would consider it a bug.

### Phase 2: Low-Invasiveness Reproduction (MANDATORY for new bugs)

**Phase 2 is MANDATORY for every NEW bug** — i.e., bugs that do not correspond to an existing JIRA ticket, CVE, or previously reported issue. A new bug without a reproduction test is unverified speculation, not a confirmed finding.

**Known/historical bugs** (those matching an existing JIRA ticket) do NOT require reproduction — the existing ticket serves as confirmation. Classify them and move on.

**For every new bug, you MUST**:
1. Write a self-contained reproduction test to `repro/test_bug<N>_<name>.py` (or `.js`, `.rs`, `.go` etc.)
2. Actually EXECUTE the test and record the output
3. Report the result honestly: REPRODUCED (bug triggered) or REPRODUCTION FAILED (bug not triggered, explain why)

"Code audit only" is NOT an acceptable final status for new bugs. If you skip reproduction for a new bug, the finding is considered unverified.

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
- The reproduction test file MUST still exist in `repro/` with the failed attempt code and a comment explaining why it didn't trigger

**Output requirements (non-negotiable for new bugs):**
- For each NEW confirmed bug: one executable test file in `repro/test_bug<N>_*.{py,js,rs,go,c,sh}`
- The test must have been actually executed (not just written)
- The confirmed-bugs.md must reference each test file and its execution result
- If new bugs exist but zero reproduction tests exist, the confirmation is INVALID
- Known/historical bugs do not require reproduction files
