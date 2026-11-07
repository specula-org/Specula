Assess invariant maintenance for the supplied adjacent source update. This is a fresh, independent first judgment before validation feedback. Work only from /workspace inputs; do not browse, use other agents, or consult experiment history.

Inputs: old/source, new/source, update.patch, old/spec. The old suite is the asset being maintained. Initial extraction is not your task. Read the update, relevant old properties/observers and code contracts/tests. Decide which old properties should be retained, changed, or removed and which additional properties are required. A source behavior change does not by itself change the correctness requirement. Correct code may still pass an old property that has become too weak. An implementation violating a still-required property is not grounds for weakening it.

Do not regenerate every property unless necessary. Make an explicit decision for each affected old property and update-related correctness obligation. Separate semantic requirement changes, representational/observer migrations, repairs of pre-existing property defects, and unchanged requirements. Include unaffected safety controls to make false edits observable.

Produce out/decision.json with:
- overall decision and concise reason;
- entries: property name or proposed name, keep/modify/add/remove/unresolved, semantic or representation change, source/test/contract evidence, proposed expression or precise predicate, and a concrete state/transition on which the old and proposed properties could disagree;
- important updated behaviors already covered by existing properties, with the actual property/observer explanation;
- suspected implementation/model defects that must not be hidden by property edits;
- unresolved obligations.

Also write out/decision.md, concise and readable. Do not execute tests or TLC or change code/spec in this call. The initial output will be frozen, then another phase will execute its witnesses against old/new models and source. It is acceptable to retain properties when they already express the needed contract; it is not acceptable to claim completeness merely because no edit was proposed.
