# Chapter 5: Generation Completeness Review

This is a semantic reread, not a request to emit a dependency graph, checklist artifact, or JSON contract. Assume the Agent can reason directly over the source and TLA+; use these prompts to prevent premature completion.

## 1. Reread the Original Diff

After all generation edits, reread the complete old/new source diff and the changed functions in context. For each semantic change, ask where else the same condition, value, state, message, assumption, or atomicity boundary participates.

Do not equate one code hunk with one spec edit. Do not stop after changing the first matching Action.

Also inspect the final spec diff against the prior suite. Apply Chapter 2's repair criteria: every semantic edit needs an implementation or property justification. Record source-driven updates and repairs of old model defects separately. Remove unsupported behavior changes while retaining justified repairs, even where the source code is unchanged.

## 2. Close the Reference Semantics

Completeness means both expressing the new behavior and keeping old behavior valid in new or refined contexts. Review in both directions:

- **Source to model:** follow the operation from its entry through the changed code to its observable result. Check semantically distinct caller contexts, including surrounding guards and side effects, before generalizing a local conclusion to the whole operation.
- **Model to source:** in states introduced or affected by the update, inspect the alternatives enabled by the complete `Next`. Can an old Action bypass, interrupt, or complete the new path in a way the implementation cannot? Include Actions that affect shared control state or enablement without mentioning new variables. Adding a more specific Action does not override an older one.

Try to construct a distinguishing execution: a legal implementation path the model cannot represent, or a model path unsupported by the implementation. Before calling it a defect, account for the chosen scope, atomicity, and intentional abstraction; different step counts or representations alone are not errors. Use concrete mismatches to guide repairs and later checks, not as a reason to expand every model or disable every overlapping Action.

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

Recheck the assumptions behind reused Actions and state representations, including why each affected behavior is enabled and what later consumers infer from its results. Consistent definitions across the suite are necessary, but their shared interpretation must also agree with the implementation. Record any intentional abstraction and its limits rather than treating agreement among generated artifacts as independent confirmation.

If the review exposes a missing edit, revise the reference and repeat the affected checks. A syntactically valid partial update is not complete.

## 3. Close the Update Focus

When `Update.tla` is used, verify:

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

- evidence shows the source update leaves modeled behavior and correctness requirements unchanged at the chosen granularity;
- every changed branch has equal old/new post-state sets after projection onto the existing model vocabulary;
- semantic spec artifacts remain unchanged, or every model repair is separately justified and the affected generation checks above pass;
- no empty or documentary `Update.tla` was created;
- the rationale is recorded in the existing brief/report for later validation.

Repair-only work proceeds through validation and applicable model checking; a no-change source disposition does not waive those checks for modified semantic artifacts.
