# Phase 3: Mandatory Reproduction Attempt

**Every bug must attempt reproduction.** New, known, or historical — no exemption. Work through the escalation ladder; either trigger the bug or mark it REPRODUCTION FAILED with an honest reason.

The status REPRODUCTION FAILED is a valid final status when the escalation ladder is exhausted. It does NOT invalidate the finding — it is information for the reader about how confident we are the bug manifests in real execution. The bug claim still stands on its code audit and developer-intent evidence (Phase 1).

For every bug, you MUST:

1. Write a self-contained reproduction test to `repro/test_bug<N>_<name>.{py,js,rs,go,c,sh}`
2. Actually EXECUTE the test and record the output
3. Walk the escalation ladder strictly in order (Level 0 → 1 → 2 → 3); document at each level what was tried and what happened
4. Report one of two final statuses:
   - **REPRODUCED** — bug triggered; include level reached, the exact command, and observable evidence
   - **REPRODUCTION FAILED** — escalation ladder exhausted; include what was attempted at each level and a reasoned conclusion about why it didn't trigger

"Code audit only" is NOT a permitted status. Every finding's entry in `confirmed-bugs.md` must show evidence of a reproduction attempt (the test file in `repro/` and the recorded output).

## Core principle

**Simulate a real-world trigger, not bypass normal flows to poke the bug directly.**

### Prohibited approaches

- Pre-populating data structures with illegal or inconsistent state, then calling a function to "prove" it can't handle it
- Directly calling internal/private functions, skipping normal entry-point checks
- Manually constructing inputs that could never occur through normal flows
- Modifying the code under test to create the bug (e.g., commenting out validation logic)

### Correct approaches

- Trigger through the system's public interfaces or normal entry points
- For concurrency bugs, reproduce via real concurrent scenarios (multi-thread/multi-process). Small delays may be inserted into the code under test to widen the race window, but the logic must not be altered
- For protocol bugs, trigger via sequences of messages that are legitimate but adversarial. The messages themselves must pass the system's normal validation
- The reproduction program should compile and run independently, without requiring special environments beyond the test framework
- The success criterion must be observable anomalous behavior (crash, deadlock, data inconsistency, safety property violation), not "some intermediate variable has an unexpected value"

### Criteria for successful reproduction

- The bug is triggered without modifying the core logic of the system under test
- The trigger path is consistent with real-world usage scenarios
- The reproduction is deterministic, or triggers with significant probability across multiple runs
- The erroneous behavior caused by the bug is clearly observable

## Escalation ladder — strict, in order

Your goal is to either **prove the bug manifests** (trigger it) or **prove the escalation ladder is exhausted** (document each level's attempt and outcome). "I tried once and it didn't trigger" is NOT a conclusion.

1. **Level 0 — Pure black-box.** Use only public APIs, normal operations, no failpoints. Always start here.
2. **Level 1 — Timing assistance.** Add `sleep()` calls or use system-provided test hooks (e.g., `configureFailPoint`, `FAIL_POINT_DEFINE`) to widen race windows. The system logic is unchanged; you're only controlling timing.
3. **Level 2 — State injection.** Directly inject the pre-condition state (e.g., insert a document that mimics a crash-recovery scenario) and verify the buggy code path handles it incorrectly. Clearly document that this is a state-injection test, not an end-to-end trigger.
4. **Level 3 — Minimal code modification.** Add a small delay (`usleep`, `sleep`) inside the system's source code at the exact crash window location to make the race deterministic. Document the modification precisely.

Walk the ladder strictly in order. Escalate ONLY when the current level genuinely failed; document why. **Do not stop at Level 0 failure.** If Level 3 also fails, the final status is REPRODUCTION FAILED — document the four attempts.

For known/historical bugs that already have a working reproduction in the upstream tree, you may re-use or adapt that reproduction as your test — start at the level matching the upstream reproduction's invasiveness. Cite the upstream reproduction.

## Verify you triggered the RIGHT bug

After triggering anomalous behavior, verify it matches the MC counterexample (or the code-review claim). Compare:

- The sequence of operations matches the MC trace (same actions, same order)
- The violated invariant is the same one MC found
- The root cause is the same code path the finding identified

If you triggered a DIFFERENT bug than what the finding described, report it separately but continue trying to trigger the original.

## Evidence requirements

When reporting REPRODUCED, you MUST include:

- The escalation level reached (0/1/2/3)
- The exact command used to run the test
- The actual output (copy-paste from terminal, not paraphrased)
- Which line(s) of output demonstrate the bug was triggered
- Comparison with expected (correct) behavior

When reporting REPRODUCTION FAILED:

- The four levels attempted (0 through 3); for each: what was tried, what happened, why it didn't trigger
- Your conclusion: is the bug real but hard to trigger (timing-sensitive, requires specific cluster topology, needs a fault not in the test framework), or do you now believe it's a false positive given the failed escalation?
- Whether you still believe the bug stands on code audit alone — and the evidence supporting that

## Output requirements

- For each bug: one executable test file in `repro/test_bug<N>_*.{py,js,rs,go,c,sh}`
- The test must have been actually executed (not just written); the output must be captured
- The `confirmed-bugs.md` entry must include the actual test output (copy-paste) as evidence, not just a status label
- REPRODUCTION FAILED entries still get a `repro/` file — the file contains the attempt code at each escalation level and a comment explaining why each level didn't trigger
- The final per-bug status is one of: REPRODUCED / REPRODUCTION FAILED / FALSE POSITIVE / NEEDS MORE INFO
