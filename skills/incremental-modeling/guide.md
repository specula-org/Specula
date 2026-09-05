# Incremental Modeling Workflow

Treat the prior Specula run as semantic evidence and the new source as the implementation to verify. Keep one complete current reference suite, reuse proven CI assets, and focus new validation effort on the update and its interactions with unchanged behavior.

The workflow has four parts under `references/`: `generation/`, `validation/`, `model-checking/`, and `reproduction/`. Execute them in that order.

## Inputs

Require:

- the old and new source revisions, or an exact diff plus both source trees;
- the prior `.specula-output/`, including its modeling brief, analysis report, specs, instrumentation mapping, traces, validation history, findings, and reproductions when present;
- a separate working copy for the new artifacts. Never overwrite the prior run.

If the prior spec has not completed trace/model convergence, say so in the analysis and treat its conclusions as provisional.

Preserve correct system semantics rather than the old model's text. Prior validation provides evidence within its coverage; it does not make every old abstraction correct. Recheck the assumptions and state meanings on which the update depends, and actively repair implementation-backed inconsistencies within the modeling scope. Prioritize repairs needed for the update and its interactions; record independent issues for separate work. Chapter 2 defines the repair criteria.

## Reuse the Existing Specula Methods

Read and apply the relevant parts of the existing skills rather than restating them here:

- For evidence, Scenario construction, exclusions, category-specific reasoning, and modeling granularity, read and apply the installed Specula **code-analysis** skill. Follow its category routing when the update changes or stresses distributed/concurrent boundaries.
- For code-faithful base/MC/Trace/instrumentation edits, source annotations, action splitting, and cfg coverage, read and apply the installed Specula **spec-generation** skill. Read its referenced generation documents for every artifact type touched by the update.
- For reusing or modifying the prior harness and collecting fresh traces, read and apply only the relevant parts of the installed Specula **harness-generation** skill.
- For running and debugging trace validation, follow the installed Specula **tla-trace-workflow** skill rather than duplicating its debugger methodology here.
- For full trace/MC convergence, follow the installed Specula **validation-workflow** skill with the incremental ordering and gates defined here.
- For counterexample confirmation and reproduction, follow the installed Specula **bug-confirmation** skill.

Do not rerun full-project archaeology by default. Reuse the old run and investigate history/issues only where the update introduces uncertainty, changes a known mechanism, or invalidates prior evidence.

## Decision Gate: Does the Model Need to Change?

Run Chapter 1 before making any semantic spec edit. It must end with exactly one disposition:

- `NO_MODEL_CHANGE`: the source update changes neither behavior nor correctness requirements at the modeling scope and granularity. Record the evidence and exclusion rationale. When no model repair is needed, skip Chapters 2–4 and run the no-change completion checks in Chapter 5.
- `MODEL_CHANGE_REQUIRED`: the update changes modeled behavior, assumptions/setup, atomicity, or correctness requirements. Continue through Chapters 2–5.

Do not create `Update.tla` merely to document a no-change decision. Do not proceed with reference edits while the disposition is still unresolved.

The disposition describes the source delta, not whether spec files changed. An existing model defect may require repair even with `NO_MODEL_CHANGE`; record that repair separately in the analysis and changelog without relabeling the source delta. Follow the affected generation and validation chapters for the repair. Reopen the disposition only if new evidence changes the assessment of the source delta.

## Part 1: Generation

First execute the decision chapter:

1. `references/generation/01-update-reconnaissance.md` — perform the short analysis needed to choose scope and modeling granularity.

Then branch:

- For `NO_MODEL_CHANGE` without a repair, execute only the no-change completion checks in `references/generation/05-completeness-review.md`. For a repair, apply Chapters 2, 3, and 5 and update existing checking views as needed; repair-only work can use ordinary MC configs without creating `Update.tla`.
- For `MODEL_CHANGE_REQUIRED`, execute the remaining chapters in order:

2. `references/generation/02-reference-model-generation.md` — draft the complete new reference suite.
3. `references/generation/03-update-focused-analysis.md` — use the explicit draft to derive deeper invariants, Scenarios, and interactions; revise the reference as needed.
4. `references/generation/04-update-model-generation.md` — generate `Update.tla` and focused/open checking configs without duplicating reference behavior.
5. `references/generation/05-completeness-review.md` — reread the source diff and close every affected spec surface.

When defining `EnvUpdate` or discharge obligations, also read `references/generation/modular-verification.md`.

Use one continuous reasoning process: analyze briefly, draft the reference update, analyze the now-explicit update interactions, revise the reference, generate `Update.tla`, and perform the completion pass. Do not turn these chapters into separate lossy handoffs or require a JSON change contract.

Do not state either disposition, even as a placeholder, before the Chapter 1 decision gate is complete.

## Semantic Ownership

- `base.tla`, `MC.tla`, and `Trace.tla` own the complete new-version behavior.
- `Update.tla` references the updated MC/reference Actions, selects interacting context, and defines update-specific properties and focused/open specs.
- Do not copy a changed Action body into `Update.tla`. Fix the reference Action and alias/wrap its MC form.
- Put assumptions, setup, variables, helpers, `Init`, `Next`, and action semantics directly in the reference suite.
- Keep unchanged properties in the reference. Put new or revised update properties in `Update.tla`; ensure stale replaced properties are not still enabled by old cfgs.

## Required Outputs

For `MODEL_CHANGE_REQUIRED`, produce:

- updated `modeling-brief.md` and `analysis-report.md` with evidence-backed update Scenarios;
- complete updated `spec/base.tla`, `base.cfg`, `MC.tla`, MC/hunt cfgs, `Trace.tla`, `Trace.cfg`, `instrumentation-spec.md`, and `brief-coverage.md`;
- `spec/Update.tla` plus the update-specific cfgs needed for full-property, concrete-focused, open-focused, and discharge checking;
- three-way source comments connecting changed code, changed reference locations, and the corresponding `Update.tla` focus.

For `NO_MODEL_CHANGE`, record the evidence and modeling-scope rationale in the existing analysis/brief. Preserve semantic artifacts unless an implementation-backed repair is needed; document and validate any repair through the same loop. Do not generate an empty `Update.tla`.

## Part 2: Validation

Run the validation chapters in order:

1. `references/validation/01-reuse-prior-harness.md` — rebase the prior CI harness onto the new source with the smallest evidence-backed changes.
2. `references/validation/02-update-focused-scenarios.md` — rerun prior scenarios and add focused traces for affected Actions and high-risk interactions.
3. `references/validation/03-trace-validation-loop.md` — debug with local feedback and related repair batches, revisiting generation when evidence changes the model.
4. `references/validation/04-validation-completeness.md` — verify harness provenance, update coverage, trace quality, and regression closure.

`NO_MODEL_CHANGE` still enters validation: run the reused harness against the new implementation and validate fresh traces against the current reference. A mismatch may expose either a missed source change or an existing model defect; distinguish them using both revisions. Semantic repairs require renewed validation and applicable model checking even when the source disposition remains `NO_MODEL_CHANGE`.

For repair-only work, apply the validation coverage requirements to the repaired Actions and their interactions identified in the analysis, whether or not `Update.tla` is used.

## Part 3: Model Checking

Read `references/model-checking/01-update-focused-checking.md`. It delegates ordinary convergence, TLC operation, and counterexample classification to the installed Specula skills, while defining the incremental full/focused/open/discharge order and validation back-edge.

## Part 4: Reproduction

When Part 3 produces an actual counterexample, enter through `references/reproduction/01-confirm-counterexample.md`. That file adds only incremental provenance and old/new control guidance; the installed Specula **bug-confirmation** skill owns investigation, reproduction, verdicts, and repair requests.

## Current Stop Boundary

Generation may run syntax and static configuration preflights only. Validation may build the reused harness, collect/replay traces, and run bounded local semantic diagnostics as described in Validation 3. Model-checking campaigns begin only after the initial validation gate; subsequent repairs use the local-feedback loop and final regression gate. Reproduction begins only with an actual counterexample.
