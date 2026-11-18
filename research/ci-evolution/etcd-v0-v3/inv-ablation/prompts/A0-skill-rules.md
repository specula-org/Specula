Assess invariant maintenance for the supplied adjacent source update. Work only from the inputs in the current directory; do not browse, use other agents, or consult experiment history.

Inputs: old/source, new/source, update.patch, old/spec. The old suite is a TLA+ model with its properties and model-checking configurations, maintained by an incremental CI. In this call, handle only the properties: decide which old properties should be kept, revised, added, or removed for the new source version.

Follow these rules from the Specula incremental-modeling procedure:

Property placement:
- Keep unchanged reference properties and continue checking them.
- Remove stale cfg enablement for a property whose old definition no longer represents the new version.
- Never weaken a still-promised property merely because the new model violates it. Record the violation candidate for later validation; make the property evidence-based.

Classify properties as:
- preserved old properties whose justification must be rechecked;
- revised properties such as `Inv_new` when the system's guarantee changed or evidence shows the old formulation was incorrect;
- newly introduced safety/liveness properties;
- interaction properties that observe the changed behavior through an old consumer;
- structural properties needed to keep focused checking meaningful.

Do not weaken a still-promised property merely because the draft violates it. The later validation phase decides whether a violation is a model issue, property issue, or implementation bug. Check that the selected properties can expose wrong interactions, rather than relying only on properties that restate the draft's assumptions. Every property must cite its source/reference evidence.

Produce out/decision.json with:
- overall decision and concise reason;
- entries: property name or proposed name, keep/modify/add/remove/unresolved, semantic or representation change, source/test/contract evidence, and proposed expression or precise predicate;
- important updated behaviors already covered by existing properties, with the actual property/observer explanation;
- suspected implementation/model defects that must not be hidden by property edits;
- unresolved obligations.

Also write out/decision.md, concise and readable. Do not execute tests or TLC or change code/spec in this call.
