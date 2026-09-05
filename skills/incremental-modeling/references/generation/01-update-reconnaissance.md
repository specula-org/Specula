# Chapter 1: Update Reconnaissance

Use the existing `code-analysis` methodology selectively. The old run already contains system reconnaissance, history, scope, and Scenarios; this pass determines what the new revision invalidates or introduces before editing TLA+.

## 1. Establish Exact Inputs

- Identify the old and new source revisions exactly.
- Read the complete diff, then read every changed function in both revisions with its callers, callees, tests, and downstream consumers.
- Read the old `modeling-brief.md`, `analysis-report.md`, base/MC/Trace specs, validation changelog, findings, confirmed dispositions, reproductions, and repair history relevant to the changed mechanism.
- Preserve the old system category unless the update changes the concurrency or communication architecture. If it does, reapply the category routing from the installed Specula **code-analysis** skill.

Do not infer protocol importance from diff size. A one-line guard can be model-critical; a large refactor can be outside the current abstraction.

## 2. Decide Scope and Granularity

Before editing TLA+, determine:

- the implementation behavior before and after the update;
- whether that behavior is inside the old modeling scope and at the old abstraction granularity;
- the state, messages, assumptions, setup, atomicity boundaries, and externally visible consequences directly changed;
- prior Scenarios/findings whose mechanism, reachability, mask, or consequence may have changed;
- likely reference surfaces to revisit, without treating the first matches as a complete list.

Project every changed behavioral branch onto the existing model vocabulary. Excluding an internal mechanism, phase, state, or discriminator excludes its representation, not its effects on variables, messages, Actions, or properties already present in the reference. When a hidden discriminator selects different visible effects, preserve the concrete effects' nondeterministic union unless distinguishing the hidden state is necessary for correctness.

Check that the reused abstraction still expresses the relevant implementation behavior. An unchanged code path can become important to a new interaction, and an old simplification can already be wrong. Treat the existing vocabulary as a starting point: when evidence requires a different representation or action boundary within the modeling scope, explain the reason and revise it through Chapter 2.

For `NO_MODEL_CHANGE`, show that the old and new projected post-state sets are equal for every changed behavioral branch. A difference in any existing modeled state, message, enablement condition, atomicity boundary, or promised property requires `MODEL_CHANGE_REQUIRED`, even when the concrete cause is otherwise excluded.

Choose one disposition:

- `NO_MODEL_CHANGE`: neither modeled behavior nor modeled correctness requirements change;
- `MODEL_CHANGE_REQUIRED`: update the complete reference suite and generate `Update.tla`.

Do not emit either label as an interim placeholder. Choose once the projection and call-path checks are complete.

For `NO_MODEL_CHANGE`, verify the conclusion against the scope and all changed call paths. Record why every projected result is unchanged. Separately record any discovered defect in the old model; its repair does not make the source delta model-relevant. Follow the repair route in [the workflow guide](../../guide.md).

## 3. Prepare the First Reference Draft

For `MODEL_CHANGE_REQUIRED`, update the existing analysis artifacts just enough to guide the first model draft:

- state the changed mechanism and evidence;
- identify the intended model granularity;
- identify obvious declarations/Actions/setup that must change;
- list old Scenarios whose assumptions need rechecking;
- preserve explicit exclusions.

Do not attempt to finish all invariants and interaction Scenarios before modeling. Chapter 2 makes the changed state and action boundaries explicit; Chapter 3 then performs the deeper update-focused analysis.
