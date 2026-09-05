# Chapter 5: Generation Completeness Review

This is a semantic reread, not a request to emit a dependency graph, checklist artifact, or JSON contract. Assume the Agent can reason directly over the source and TLA+; use these prompts to prevent premature completion.

## 1. Reread the Original Diff

After all generation edits, reread the complete old/new source diff and the changed functions in context. For each semantic change, ask where else the same condition, value, state, message, assumption, or atomicity boundary participates.

Do not equate one code hunk with one spec edit. Do not stop after changing the first matching Action.

Also inspect the final spec diff against the prior suite. Every semantic edit must be required by the source update, its dependency closure, or an evidence-backed property change. Remove collateral edits to unchanged Action boundaries, message production/consumption, retry behavior, or old special paths.

## 2. Close the Reference Semantics

Verify all relevant surfaces directly in the actual files:

- constants, declarations, record/message fields, variable groups, assumptions, and type predicates;
- `Init`, restore/setup paths, and every required initial value;
- every helper caller and every special/general call site implementing the mechanism;
- every Action that reads, writes, preserves, sends, persists, retries, or recovers affected state;
- real atomicity/interleaving boundaries;
- `Next`, fairness, Action reachability, and removal of stale alternatives;
- preserved and structural properties;
- MC wrappers, counters, constraints, enabled cfg entries, and Scenario hunt coverage;
- Trace wrappers, post-state checks, silent actions, event fields, capture timing, and instrumentation mapping.
- equality of old/new projected post-state sets for every branch classified `NO_MODEL_CHANGE`;
- agreement between mandatory instrumentation fields and non-vacuous Trace checks.

If the review exposes a missing edit, revise the reference and repeat the affected checks. A syntactically valid partial update is not complete.

## 3. Close the Update Focus

Verify:

- every directly changed reference Action is represented in `AffectedActions`;
- every high-risk producer/consumer/fault interaction identified by analysis is concrete in `InteractionActions`;
- every other reference Action capable of changing update-visible state or enablement is either concrete or covered by `EnvUpdate`;
- all generated properties are evidence-backed and enabled by a real cfg;
- discharge obligations name real omitted Actions and include correct frame conditions;
- source, reference, and `Update.tla` mappings are bidirectional and point to existing definitions;
- focused specs do not claim to replace full reference validation.

## 4. Reconcile Analysis and Artifacts

Reopen the updated modeling brief and analysis report. Ensure every selected update Scenario has corresponding model state/actions/properties/configs, and every excluded behavior has an explicit scope rationale. Remove stale recommendations that the final model no longer follows.

## 5. Stop Conditions

For `MODEL_CHANGE_REQUIRED`, finish only when:

- the complete reference suite is updated and syntax/config preflights pass;
- `Update.tla` and its required cfgs exist and reference real MC/base definitions;
- the completeness reread found no unresolved semantic gap;
- no trace validation, TLC campaign, simulation, confirmation, or reproduction has been started.

For `NO_MODEL_CHANGE`, finish only when:

- evidence shows the update is outside the modeled behavior/property scope at the existing granularity;
- every changed branch has equal old/new post-state sets after projection onto the existing model vocabulary;
- semantic spec artifacts remain unchanged;
- no empty or documentary `Update.tla` was created;
- the rationale is recorded in the existing brief/report for later validation.
