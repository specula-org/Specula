# Validation 2: Update-Focused Scenarios and Traces

Use the prior scenario suite as the regression base, then add the smallest set of scenarios needed to exercise the update and its interactions. Do not replace broad regression coverage with update-only tests.

## 1. Rerun Prior Scenarios on the New Version

Run compatible prior harness scenarios against the new implementation and collect fresh traces. Archived old-version traces remain immutable evidence; they are not substitutes for executing the new code.

- Fresh traces from prior scenarios check that unchanged behavior still conforms to the updated or unchanged reference.
- An archived trace that crosses intentionally removed behavior may be marked superseded with source evidence; do not weaken the new model to accept it.
- A prior scenario that no longer builds or reaches its target needs a concrete source-drift disposition, not silent removal.

## 2. Add Update Scenarios

For every selected update Scenario, obtain a real execution that targets the corresponding source path and model Actions. Reuse a suitable fresh new-version trace when available; add a scenario when existing executions leave a specific behavior, timing, or observation gap. A spec repair alone does not require a new scenario. Cover, when supported by the implementation:

```text
old producer -> affected Action -> old consumer
old context -> affected Action -> crash/recovery
old Action -> affected Action -> old Action
affected Action -> retry/timeout/configuration change
affected Action -> affected Action
```

Each scenario must name:

- the `AffectedActions` and concrete `InteractionActions` it should emit;
- the mandatory update fields and post-state consequence to observe;
- the real test entry point and fault/timing control, if any;
- which old property, revised property, or new interaction property it informs.

Do not force an implementation sequence that cannot occur through normal APIs merely to imitate a model path.

## 3. Category-Specific Trace Quality

For Category A, preserve the real linear event order and collect the message/state fields needed to distinguish the changed path.

For Category B, follow the installed **harness-generation** timebox method: per-thread writers, tight real intervals, post-state capture outside the interval, preprocessing, and genuine cross-thread overlap. The target interaction is a partial-order constraint, not an artificial total order.

## 4. Coverage Gate

Before trace validation:

- every affected event appears in at least one fresh new-version trace, or has a cited environment limitation;
- every high-risk producer/consumer/fault interaction appears in at least one scenario;
- mandatory update fields are present and non-vacuous;
- prior regression scenarios still have explicit fresh-run outcomes;
- Category B has genuine overlap and contention rather than serialized traces.

Record uncovered Actions as validation gaps. Do not count a scenario name, test file, or empty trace as coverage.
