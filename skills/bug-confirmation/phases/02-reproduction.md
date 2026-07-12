# Phase 2: Mandatory Reproduction Attempt

**This phase decides the verdict.** Phase 1 only gathered evidence (in `investigation.md`) and judged nothing (except the code-review × known drop). Here you attempt reproduction, then choose exactly ONE verdict from the decision table (`guide.md`) using the Phase-1 investigation record **plus** the reproduction result together.

**Every bug must attempt reproduction.** New, known, or historical — no exemption. Work through the escalation ladder; either you trigger the live harm (→ `REPRODUCED`) or you do not.

**When you cannot reproduce the live harm of a REAL defect, it is exactly one of three — pick by WHY it did not manifest, never a vague "reproduction failed":**
- **`ENV_LIMITED`** — the defect is real and *would* harm in production, but THIS environment cannot trigger it (needs a real cluster / hardware / timing). Requires a SOUND argument that production exhibits it, naming the exact env limitation. It is not a blanket "stands on code audit".
- **`MASKED`** — the defect is real but a safeguard / downstream mechanism (sync / loopback / resend / guard) / a discarded output / a *separate* bug currently masks the harm, so it does not bite today. Name the mask (prove it fires — see below).
- **`PENDING REPAIR`** — (MC only) the counterexample is a spec / fault-model / invariant artifact: the CE needs something the real code cannot do, or flags a benign state. Emit a repair request (see "When a counterexample is an artifact").

(A finding that is not a real defect at all is `FALSE POSITIVE`; one you genuinely cannot judge is `NEEDS MORE INFO`. Neither is a "reproduction failed" bucket.)

For every bug, you MUST:

1. Write a self-contained reproduction test to `repro/test_bug<N>_<name>.{py,js,rs,go,c,sh}`
2. Actually EXECUTE the test and record the output
3. Walk the escalation ladder strictly in order (Level 0 → 1 → 2 → 3); document at each level what was tried and what happened
4. Choose exactly one final outcome from the decision table and include the evidence it requires

"Code audit only" is NOT a permitted status. Every finding's entry in `confirmed-bugs.md` must show evidence of a reproduction attempt (the test file in `repro/` and the recorded output).

## Core principle

**Simulate a real-world trigger, not bypass normal flows to poke the bug directly.**

### Prohibited

- Pre-populating data structures with illegal or inconsistent state, then calling a function to "prove" it can't handle it
- Directly calling internal/private functions, skipping normal entry-point checks
- Manually constructing inputs that could never occur through normal flows
- Modifying the core logic of the system under test to create the bug (e.g., commenting out validation logic)

### Required

- Trigger through the system's public interfaces or normal entry points; the trigger path must be consistent with real-world usage scenarios
- For concurrency bugs, reproduce via real concurrent scenarios (multi-thread/multi-process). Small delays may be inserted into the code under test to widen the race window, but the logic must not be altered
- For a **memory-ordering / happens-before** claim specifically, a native run on a strong-memory host (x86/TSO) can neither confirm nor refute it — acquire/release/relaxed all behave as if sequentially consistent there, so a green run proves nothing. Use a weak-memory model checker (Relacy / Loom / CDSChecker / `herd`) with **positive and negative controls** (weaken the ordering and show the race then appears), or give an explicit `[atomics.fences]`-level argument. Do not rest the verdict on a TSO run
- When the finding's mechanism spans **multiple operations or code paths** (create / update / delete, several triggers, error vs happy path), exercise **each** before settling — especially the **delete / cleanup / crash-recovery paths**, where durable-state bugs hide. A verdict read from only one path (e.g. update) can wrongly land `MASKED` / `FALSE POSITIVE` while another path (e.g. delete) is a live `REPRODUCED`
- For protocol bugs, trigger via sequences of messages that are legitimate but adversarial. The messages themselves must pass the system's normal validation
- The reproduction program should compile and run independently, without requiring special environments beyond the test framework
- The reproduction is deterministic, or triggers with significant probability across multiple runs
- The success criterion must be observable anomalous behavior (crash, deadlock, data inconsistency, safety property violation), not "some intermediate variable has an unexpected value"

## Escalation ladder — strict, in order

Your goal is to either **prove the bug manifests** (trigger it) or **prove the escalation ladder is exhausted** (document each level's attempt and outcome). "I tried once and it didn't trigger" is NOT a conclusion.

1. **Level 0 — Pure black-box.** Use only public APIs, normal operations, no failpoints. Always start here.
2. **Level 1 — Timing assistance.** Add `sleep()` calls or use system-provided test hooks (e.g., `configureFailPoint`, `FAIL_POINT_DEFINE`) to widen race windows. The system logic is unchanged; you're only controlling timing.
3. **Level 2 — State injection.** Inject the pre-condition state and verify the buggy code path handles it incorrectly. The injected state MUST be one the real system can actually reach: show the real-API call sequence that produces it, or cite the exact model-counterexample step it instantiates. Injecting a state the real system can never reach (an impossible / hand-built pre-condition — e.g. two peers simultaneously in a mutually-exclusive role, a mock that emits a value a real peer never sends, **or feeding an input/channel whose only producer is dead code**) is unsound and does not reproduce anything. When that unreachability is the finding's real story, route it: an **MC finding** means the counterexample needs a state the code cannot reach — hand back to repair (`FAULT_MODEL` / `SPEC_REPAIR`, see below); a **code-review finding** is a FALSE POSITIVE. Clearly document that this is a state-injection test, not an end-to-end trigger.
4. **Level 3 — Minimal code modification.** Add a small delay (`usleep`, `sleep`) inside the system's source code at the exact crash window location to make the race deterministic. Document the modification precisely.

Walk the ladder strictly in order. Escalate ONLY when the current level genuinely failed; document why. **Do not stop at Level 0 failure.** If Level 3 also fails, document the attempts and choose the final verdict from the decision table.

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

When reporting ENV_LIMITED:

- The four levels attempted (0 through 3); for each: what was tried, what happened, why it didn't trigger
- Your conclusion: is the bug real but hard to trigger (timing-sensitive, requires specific cluster topology, needs a fault not in the test framework), or do you now believe it's a false positive given the failed escalation?
- Whether you can give a SOUND argument that the consequence still occurs in production despite the failed trigger (naming the environment limitation that blocks it here) — or whether, absent that argument and any reachable consequence, it is a FALSE POSITIVE (code-review) / a model-repair signal (MC)

## When a counterexample is an artifact — hand back to repair (confirmation loop)

Reproduction failing is not always a statement about the bug — sometimes it is a statement about the **spec**. If the escalation ladder did not trigger the bug *because the counterexample requires something the implementation cannot actually do*, the finding is not dropped: it is handed back to Phase 3 for a scoped repair (`PENDING REPAIR`). Phase 3 repairs the spec and re-runs model checking; the fresh output is then confirmed normally by another pass of this skill — there is no separate re-check. This is the confirmation-loop back-edge.

Emit a repair request (write `repair-requests/RR-NNN.md`, `status: OPEN`, per `references/repair-request-format.md`) **only when you can cite** which of these holds:

- **SPEC_REPAIR** — a step the counterexample requires is impossible at the code level: the model under-models a guard or branch the implementation has. Cite the missing guard (`file:line`). This is the common case — an over-permissive action, or an overfit repair that survived convergence.
- **FAULT_MODEL** — the counterexample depends on an injected fault that is not in the system's failure model, or a fault modeled with the wrong semantics. Cite the failure-model evidence.
- **INVARIANT** — the path reproduces but has no observable consequence, AND developer-intent evidence (Phase 1, Step 2) shows the implementation does not promise the violated property. Cite the evidence.

If the path reaches the bad state but a **downstream mechanism masks the consequence** (a guard, a sync/loopback/resend that later resolves it, a discarded output, or a separate bug that carries the harm), first PROVE that mechanism actually fires (extend the repro to assert it — do not assume it). If it does, distinguish two cases: (a) the **code has a real defect** but the mask currently prevents live harm → status `MASKED` (a finding — real anomaly, would bite if the mask were removed; name the mask), NOT FALSE POSITIVE; (b) the **code is correct** and only the MC invariant over-flagged a benign state → hand back to repair as `INVARIANT`. If you cannot prove the mask fires, the consequence stands (REPRODUCED).

**A citation is mandatory.** If you cannot cite the missing guard / inadmissible fault / unpromised property, do not emit a request — fall back to ENV_LIMITED (you believe it is real but hard to trigger) or NEEDS MORE INFO (you cannot tell). "I couldn't trigger it" is never, by itself, grounds for a repair request.

When you emit a request: set the finding's `confirmed-bugs.md` status to `PENDING REPAIR (RR-NNN)` and stop processing that finding — the loop returns it to you in re-check.

## Output requirements

- For each bug: one executable test file in `repro/test_bug<N>_*.{py,js,rs,go,c,sh}`
- The test must have been actually executed (not just written); the output must be captured
- The `confirmed-bugs.md` entry must include the actual test output (copy-paste) as evidence, not just a status label
- ENV_LIMITED entries still get a `repro/` file — the file contains the attempt code at each escalation level and a comment explaining why each level didn't trigger
- The final per-bug status is one of: REPRODUCED / ENV_LIMITED / MASKED / FALSE POSITIVE / NEEDS MORE INFO. `MASKED` is a **finding** (real defect, consequence masked today) — surfaced, not a false positive. A finding handed back to repair is recorded as **PENDING REPAIR (RR-NNN)**; after Phase 3 repairs the spec and re-runs MC, the fresh confirmation pass re-decides it (a repaired artifact simply disappears from the new output). If the repair loop is exhausted, the orchestrator files the request under `deferred/` and marks the finding `DEFERRED` — that is not your verdict to write.
