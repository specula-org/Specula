# Chapter 2: Generate the Complete New Reference Suite

Read and follow the installed Specula **spec-generation** skill for all touched artifacts. Start from the prior suite and revise it into the complete semantic model of the new source revision, correcting implementation-backed inconsistencies in the relevant old abstraction as needed.

## 1. Keep One Behavioral Source of Truth

Put every change that determines how the new implementation behaves into the reference suite:

- constants, variable declarations, message/record shape, and state representation;
- module assumptions, setup, environment constraints, and fault semantics;
- helpers/operators and every affected caller;
- `Init`, `Next`, action guards/effects, atomicity, persistence, and recovery;
- MC wrappers/counters/constraints/configs;
- Trace wrappers, post-state checks, silent actions, and instrumentation fields.

Do not defer difficult semantics to `Update.tla`. `Update.tla` is a checking lens over this completed model.

## 2. Update in Dependency Order

Work in this order, revisiting earlier steps whenever later reasoning reveals a gap:

1. declarations, type/structural predicates, constants, assumptions, and variable groups;
2. `Init` and setup/recovery initialization;
3. changed helpers and all semantic callers;
4. changed Actions and every parallel/special/general code path implementing the same mechanism;
5. unaffected Actions that must initialize, preserve, or consume new/changed state;
6. `Next`, reachability, fairness, and common properties;
7. MC wrappers, counters, constraints, standard cfg, and Scenario hunt cfgs;
8. Trace event wrappers, `ValidatePostState`, silent transitions, and instrumentation mapping;
9. brief coverage audit and source annotations.

Use the existing source-faithfulness rules: model the implementation rather than the intended paper algorithm; preserve real atomicity boundaries; split actions where code paths or interleaving windows diverge.

Preserve old behavior whose abstraction remains valid. Every semantic edit needs evidence from the source change, its interactions, an existing model/implementation mismatch, or a justified property correction. Do not preserve a known modeling defect solely because the corresponding code is unchanged. Prioritize defects affecting the update or its verification; record independent defects for separate work.

Reuse the meaning of an abstraction, not just its assignments or guards. Check that the relevant action preconditions and state meanings remain consistent through production, consumption, and recovery. An unchanged concrete field need not mean an unchanged abstract value. Adjust variables or action boundaries when necessary to preserve that meaning, then update all dependent reference, MC, Trace, and Update definitions. Choose a semantically sufficient repair; changed line count and reuse of the original representation are not correctness criteria. Keep intentional abstractions explicit and appropriate to the properties being checked.

## 3. Property Placement

- Keep unchanged reference properties and continue checking them.
- Remove stale cfg enablement for a property whose old definition no longer represents the new version.
- Put new or revised update-specific properties in `Update.tla` during Chapter 4.
- Keep general structural/type properties needed to validate the complete reference in the reference suite.

Never weaken a still-promised property merely because the new model violates it. Record the violation candidate for later validation; at generation time, make the model faithful and the property evidence-based.

## 4. Preserve Three-Way Traceability

At each changed reference location, add a concise comment after the corresponding `Update.tla` name is known:

```tla
\* UPDATE-MAP
\* code: src/path/file.ext:<line-range-or-symbol>
\* update: Update!<focus-operator>
```

Retain the normal Specula `file:line` source annotations inside changed logic blocks. The mapping comment supplements them; it does not replace source-faithful annotations.

For assumptions, setup, variables, or helpers that are not redefined in `Update.tla`, point to the `Update.tla` section that explains their effect on Affected Actions, Interaction Actions, or update properties.

## 5. Generation Preflight

Before Chapter 3:

- validate the syntax of every changed TLA+ module;
- inspect actual cfg names and enabled properties rather than relying on intent;
- ensure every declared variable is initialized and constrained by every applicable Action;
- ensure new/replaced Actions are reachable from the selected `Next` relation;
- ensure Trace/instrumentation field names and trigger points agree.

If `instrumentation-spec.md` declares an update identity or post-state field mandatory, the corresponding Trace wrapper must require and validate it. Do not make a required field optional merely because the old harness has not yet been rebased; Part 2 updates the harness.

Use SANY, variable-assignment checks, and static cfg/operator resolution. Do not launch BFS, simulation, trace replay, or even shallow TLC exploration as a generation preflight. Part 2 and Part 3 own executable validation.
