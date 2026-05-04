## Bug Confirmation and Reproduction Guide

### Phase 0: System-Level Consequence Test

Before auditing reachability or reproducing, decide whether the finding is a bug or a path deviation. This filter is cheap and catches the most common false positive.

**Apply three filters. All must pass.**

1. **Path ≠ bug.** "The function deviates from its inferred contract" or "an unexpected execution path is reachable" is not a bug on its own. Internal helpers commonly assume preconditions their callers already enforce; a violation of an LLM-inferred postcondition that no test exercises is not a contract violation. Ask: does this deviation produce a *system-level consequence* — crash, deadlock, data corruption, safety/liveness violation, or wrong reply to a client? If the worst case is "an internal value is unexpected, but the surrounding code already validates / clamps / re-checks before any external effect", stop. Path deviation, not bug.

2. **Name the observable harm.** Write one sentence describing what a user, operator, or other system component would see go wrong. "Returns Err in a branch that's never taken" is not harm. "Two replicas commit different values for the same slot" is harm. If you can't name the symptom, the finding is not yet a bug.

3. **Check whether the developers consider the contract binding.** Skim issue/PR discussions, code comments, and tests near the suspect code. If developers explicitly say "this is by design / defensive / shouldn't happen / caller's responsibility", treat the finding as a path deviation unless you can show that their reasoning is wrong (e.g., the caller they're trusting doesn't actually validate). If developers have written tests that *assert* the current behavior, that's strong evidence they consider it correct.

**Common false-positive shapes to filter out at this phase:**

- Defensive-programming returns (`if x == nil { return ErrInvalid }` in a function whose only callers always pass non-nil) — the function is robust, not buggy.
- "Unreachable" branches that LLM analysis flagged because it couldn't prove unreachability — verify with caller analysis before reporting.
- Race windows that don't corrupt observable state because a downstream check absorbs the inconsistency.
- "Function violates inferred postcondition X" where X was synthesized by an LLM and no test or caller depends on X.

If the finding passes all three filters, proceed to Phase 1. If it fails any filter, stop here and record the finding as a path deviation in the report — note which filter rejected it and why. Do not silently drop the finding; the rejection itself is information for evaluating the bug-finding pipeline.

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

**Escalation ladder — start low-invasiveness, escalate if needed:**

Your goal is to either **prove the bug exists** (trigger it) or **prove it doesn't** (explain why it's impossible to trigger). You must reach one of these conclusions. "I tried once and it didn't trigger" is NOT a conclusion.

1. **Level 0 — Pure black-box**: Use only public APIs, normal operations, no failpoints. Try this first.
2. **Level 1 — Timing assistance**: Add `sleep()` calls or use system-provided test hooks (e.g., `configureFailPoint`, `FAIL_POINT_DEFINE`) to widen race windows. The system logic is unchanged; you're only controlling timing.
3. **Level 2 — State injection**: Directly inject the pre-condition state (e.g., insert a document that mimics a crash-recovery scenario) and verify the buggy code path handles it incorrectly. Clearly document that this is a state-injection test, not an end-to-end trigger.
4. **Level 3 — Minimal code modification**: Add a small delay (`usleep`, `sleep`) inside the system's source code at the exact crash window location to make the race deterministic. Document the modification precisely.

Start at Level 0. If it doesn't trigger, analyze WHY (what timing/state condition is missing?), then escalate to the next level. Each escalation must be explained. **Do not stop at Level 0 failure.**

**Verify you triggered the RIGHT bug:**

After triggering anomalous behavior, verify it matches the MC counterexample. Compare:
- The sequence of operations matches the MC trace (same actions, same order)
- The violated invariant is the same one MC found
- The root cause is the same code path MC identified

If you triggered a DIFFERENT bug than what MC found, report it separately but continue trying to trigger the original MC bug.

**Evidence requirements:**

When reporting REPRODUCED, you MUST include:
- The exact command used to run the test
- The actual output (copy-paste from terminal, not paraphrased)
- Which line(s) of output demonstrate the bug was triggered
- Comparison with expected (correct) behavior

When reporting REPRODUCTION FAILED after exhausting the escalation ladder:
- Which levels you attempted (0 through 3)
- For each level: what you tried, what happened, why it didn't trigger
- Your conclusion: is the bug real but hard to trigger, or is it a false positive?

**If reproduction fails:**
- Explain what approaches were attempted at each escalation level and why they failed
- Analyze whether the bug itself is a false positive, or whether the trigger conditions are difficult to satisfy in the current test environment
- Do not lower the bar of reproduction authenticity just to claim "reproduction succeeded"
- The reproduction test file MUST still exist in `repro/` with the failed attempt code and a comment explaining why it didn't trigger

**Output requirements (non-negotiable for new bugs):**
- For each NEW confirmed bug: one executable test file in `repro/test_bug<N>_*.{py,js,rs,go,c,sh}`
- The test must have been actually executed (not just written)
- The confirmed-bugs.md must include **actual test output** (copy-paste) as evidence, not just a status label
- If new bugs exist but zero reproduction tests exist, the confirmation is INVALID
- Known/historical bugs do not require reproduction files

## Additional References

For additional examples beyond the built-in ones, see the [Specula case-studies repository](https://github.com/specula-org/specula-case-studies) which contains 60+ completed case studies across distributed systems, consensus protocols, and concurrent data structures.
