Assess invariant maintenance for the supplied adjacent source update, then test your own proposed edits with executed concrete-state evidence. Work only from the inputs in the current directory; do not browse, use the network, use other agents, or consult experiment history.

Inputs: old/source, new/source, update.patch, old/spec. The old suite is the asset being maintained. Initial extraction is not your task.

Tools available in this directory:
- TLC: `java -cp /tmp/tools/tla2tools.jar:/tmp/tools/CommunityModules-deps.jar tlc2.TLC ...` (SANY: `tla2sany.SANY`).
- Go (offline, dependencies preinstalled): to build or test a source tree, copy it under `evidence/` first, then `cp /tmp/godeps/go.mod.template <tree>/go.mod && cp /tmp/godeps/go.sum <tree>/` and run `go test -vet=off -run <Name> ./...` inside it. Never modify old/source, new/source, or old/spec themselves.

## Phase 1: first judgment (no execution)

Read the update, relevant old properties/observers and code contracts/tests. Decide which old properties should be retained, changed, or removed and which additional properties are required. A source behavior change does not by itself change the correctness requirement. Correct code may still pass an old property that has become too weak. An implementation violating a still-required property is not grounds for weakening it.

Do not regenerate every property unless necessary. Make an explicit decision for each affected old property and update-related correctness obligation. Separate semantic requirement changes, representational/observer migrations, repairs of pre-existing property defects, and unchanged requirements. Include unaffected safety controls to make false edits observable.

Write out/decision.initial.json with:
- overall decision and concise reason;
- entries: property name or proposed name, keep/modify/add/remove/unresolved, semantic or representation change, source/test/contract evidence, proposed expression or precise predicate, and a concrete state/transition on which the old and proposed properties could disagree;
- important updated behaviors already covered by existing properties, with the actual property/observer explanation;
- suspected implementation/model defects that must not be hidden by property edits;
- unresolved obligations.

Write this file before running any command. It is frozen: do not edit it afterwards.

## Phase 2: executed evidence

For every semantic modify/add/remove that concerns the update (and any other edit you are unsure of), make the disagreement concrete and execute it. Prioritize: the update-related semantic edits first; stop adding checks once each such edit has its evidence.

1. **Separating state, evaluated by TLC.** Write the proposed definitions into `evidence/Proposed.tla` (for example a copy of old/spec/base.tla with the edits applied). Build the witness as constant expressions for the spec's variables and evaluate the actual old and proposed definitions with TLC, for example:
   `Old == INSTANCE base WITH raft <- R0, disk <- D0, ..., history <- H0, quality <- Q0`
   `New == INSTANCE Proposed WITH ...` and `ASSUME PrintT(<<Old!Prop, New!Prop>>)`, or a one-state spec checked with the property as an invariant. Evaluate the TLA+ definitions themselves, not a Python or prose translation. Include helper/observer changes: identical predicate text is not necessarily identical meaning. Keep newly forbidden old behavior in the comparison domain instead of restricting it to states the new implementation reaches.
2. **Non-vacuous observations.** Many properties quantify over history or quality records. A witness whose relevant records are empty proves nothing. Populate the records from a real mapped pre/post state and inputs, and say how. If an observer lacks a needed field, propose and test the observer migration separately rather than choosing a truth value.
3. **Code observation.** Where the witness concerns implementation behavior, drive the real old and/or new code to the corresponding pre-state with a small Go test in a copy of the tree (reuse existing test helpers) and record what the code does. Use explicit `not_representable` or `unknown` rather than inventing a result.
4. **Controls.** For a legitimate relaxation, also construct a nearby forbidden observation (an obligation that must still be violated) and check that the proposed property still rejects it. For a strengthening, check a legitimate allowed control and that the intended forbidden behavior is rejected.
5. **Adjudication.** The candidate and old properties are not trusted oracles. Do not reject a candidate merely because the current implementation violates it; the implementation might be buggy. Use contracts, design comments and expected tests to decide what should be allowed.

Then revise your decisions where the evidence shows they were wrong.

## Outputs

- out/decision.json: the final decisions, same fields as the initial file, plus for each entry `evidence_ids` and `changed_from_initial` (with the reason when true).
- out/evidence.json: a list with one record per executed check: `id`, `property`, `kind` (relaxation, strengthening, semantic, control, observer), `state` (the witness, and how its records were populated), `old_property` and `proposed_property` (each with `claimed` and `tlc` truth values), `code_observation` (old/new behavior, test file, command, result, or not_representable/unknown), `requirement_evidence`, `verdict` (accepted, revised, rejected, unresolved), `note`, and the paths of the TLA+/Go files and logs under `evidence/`.
- out/decision.md: concise and readable, including what changed between the initial and final decisions and why.

It is acceptable to retain properties when they already express the needed contract; it is not acceptable to claim completeness merely because no edit was proposed.
