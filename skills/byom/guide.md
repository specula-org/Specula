# Bring Your Own Model Workflow

Continue the normal Specula workflow from user-provided verification artifacts. Treat the supplied path and the target-specific instructions as flexible inputs: they may contain one model file, a directory of partial artifacts, or assets for several targets.

## Shared Rules

1. Inspect the supplied path and the target-specific instructions. Identify only the assets that belong to the current target; if ownership is ambiguous, stop and explain what the user must clarify.
2. Never modify the original supplied path. Copy adopted artifacts into the target's `.specula-output/` workspace and make later changes only there.
3. Reuse every supplied artifact that already performs the required job. Verify that it is usable, but do not recreate it merely to match Specula's usual implementation style.
4. During the initial inventory and Scenario analysis, do not make semantic changes to supplied artifacts. Add missing artifacts or adapters around them. Once the normal validation and repair workflows begin, they may revise workspace copies as usual.
5. Do not require a manifest or fixed input layout. Infer relationships from the artifacts, target source, and user instructions. Record uncertainty instead of guessing.

## Phase 2: Adopt and Complete the Specification

1. Inventory supplied models, invariants, configs, trace-validation wrappers, instrumentation mappings, harnesses, traces, and replay instructions.
2. Read the installed **code-analysis** skill and use only its relevant Scenario-discovery guidance for a focused pass. Analyze only behaviors and interactions related to the supplied model. Do not repeat the full Phase 1 analysis or silently expand the model's scope.
3. Write a concise `modeling-brief.md` that records the supplied scope and the focused Scenario supplement. Record out-of-model Scenarios as coverage gaps rather than changing the supplied model during this phase.
4. Copy usable specification artifacts into `spec/`. Read and follow the installed **spec-generation** skill only for missing Phase 2 responsibilities, including any required MC/Trace wrappers, configs, coverage audit, or instrumentation mapping. Preserve supplied implementations when they already satisfy those responsibilities.
5. Finish with the ordinary Phase 2 output contract so the standard harness phase can consume the workspace.

## Phase 2.5: Adopt and Complete the Harness

1. Inspect supplied instrumentation, harness code, run commands, and traces before creating anything.
2. Read and follow the installed **harness-generation** skill only for missing or unusable Phase 2.5 responsibilities. Prefer adapting supplied tooling over replacing it.
3. If usable traces are already present, adopt them and proceed without rerunning the harness by default. Run the harness when needed to diagnose a problem, refresh missing evidence, or make the traces consumable.
4. Fix instrumentation, harness, and trace-adaptation problems in the workspace when the normal harness workflow calls for it. Never change files at the original supplied path.
5. Finish with the ordinary Phase 2.5 output contract so the standard validation workflow can start.

## Phase Ownership

This skill changes how the current pipeline phase reuses supplied artifacts. It does not authorize the current agent to execute any additional pipeline phase.

1. Complete only the phase assigned by the launcher prompt.
2. References to other skills borrow the methodology needed for the current phase; they do not authorize performing the referenced skill's phase.
3. Stop after satisfying the current phase's output contract. The pipeline launches each later phase separately.
4. Use the existing **validation-workflow**, **bug-confirmation**, repair loop, and **bug-classification** without changing their methodology when the launcher assigns those phases. They may modify the adopted workspace copies under their normal rules.

## Final Modification Report

Only when the launcher explicitly assigns the final reporting responsibility, compare the original supplied path with the final target workspace and write `.specula-output/byom-modification-report.md` after confirmation, repair, and classification finish.

Keep the report short and include:

- supplied assets reused without modification;
- supplied assets modified in the workspace and why;
- verification assets added by Specula and why;
- relationships that could not be determined reliably.

State explicitly when nothing supplied was modified. This is an agent-produced comparison report, not a mechanically complete patch. Do not modify any verification artifact while preparing it.
