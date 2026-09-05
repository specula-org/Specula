# Update-Focused Model Checking

Use the installed Specula **validation-workflow** skill for trace/MC convergence and the installed **tla-checking-workflow** skill for TLC execution, counterexample analysis, classification, and fixes. Do not restate those methods here.

## Entry Gate

Begin only after the fresh new-version trace suite passes. First run the standard `MC.cfg` convergence round from the main validation workflow. Any semantic spec or invariant repair returns to full fresh trace validation before model checking continues.

For `NO_MODEL_CHANGE`, when semantic artifacts are byte-identical and fresh trace validation passes, retain the prior model-checking evidence and stop. Do not create an empty `Update.tla` or rerun an unchanged state space merely to exercise this chapter.

## Incremental Campaign

For `MODEL_CHANGE_REQUIRED`, run in this order:

1. **Full update check** — check update properties over complete `MCNext` using the generated full config. This is the guard against interactions omitted by focused models.
2. **Concrete focused check** — run the generated `AffectedActions \/ InteractionActions` configs so TLC spends its state budget on the changed mechanism and its high-risk unchanged producers, consumers, retries, faults, persistence, and recovery.
3. **Open and discharge checks** — when `EnvUpdate` exists, run the open config and the discharge config. Treat an open result as provisional until omitted real context Actions satisfy the rely/frame obligation.
4. **Scenario hunts** — run the generated update Scenario configs with the BFS/simulation strategy from the main checking workflow. Each Scenario needs a reachability canary or witness; a property that passes only because its update interaction is unreachable is not coverage.
5. **Final full check** — rerun the standard full model and full update properties after every repair made during focused checking.

These are independent TLC campaigns. They restrict or widen the enabled Action set; they do not impose a single execution order. Scenario-specific monitors may observe a producer/affected/consumer path, but must not redefine reference behavior.

Do not reduce bounds on update-relevant Actions or faults merely to make BFS deeper. Reduce unrelated domains when justified, then use the main workflow's simulation follow-up for depth.

## Counterexamples and Back-Edges

Apply the main checking workflow's classification unchanged. Incremental model checking adds only these routing rules:

- A violation of a new or revised property is not automatically an invariant problem; a faithful updated model may have exposed an implementation bug.
- A focused-only violation must also be admitted by full current reference behavior, or have a valid open/discharge basis, before it becomes a finding.
- A finding is update-related only when its path crosses an affected Action, depends on updated setup/assumptions/state, or demonstrates that the update moved or removed a prior mask. Attribution does not change whether the bug is real.
- Any Case A/B repair that changes semantic artifacts returns to the complete fresh trace suite, then restarts every affected campaign above.
- Save actual Case C counterexamples and continue the remaining campaigns. Pass them to `../reproduction/01-confirm-counterexample.md`; do not reproduce a Scenario with no violation.

## Completion

Finish only when standard trace/MC convergence holds, every selected update Scenario is reachable, full/concrete/open/discharge campaigns have explicit outcomes, no Case A/B remains unresolved, and the final full checks have been rerun. Record timeout or resource exhaustion as limited coverage, never as a pass.
