# Validation 3: Trace Validation Loop

Follow the installed Specula **tla-trace-workflow** skill for validation, layered debugging, and evidence-backed fixes. This chapter defines only the incremental ordering and back-edges.

## 1. Validate in Information Order

1. Validate one short fresh trace that reaches an affected Action.
2. Validate fresh interaction traces for producer/consumer/fault Scenarios.
3. Validate fresh traces regenerated from the prior regression scenarios.
4. Once the related repairs stabilize, run the trace workflow's parallel validation over every retained fresh new-version trace.

For Category B, validation succeeds only when some legal timebox interleaving fully consumes the trace. A deadlocked or pruned ordering rejects only that ordering. Look for a full-consumption witness while retaining the semantic and field checks; disabling deadlock detection alone is not a success criterion. Without such a witness, an unfinished search leaves conformance unresolved.

## 2. Classify Before Editing

For each failure, identify which evidence is wrong:

- **Harness/capture mismatch**: event name, field, identity, timing, ID mapping, preprocessing, or scenario setup disagrees with the real action. Fix the responsible layer; reprocess retained raw events when sufficient, otherwise recollect the affected traces.
- **Replay configuration mismatch**: finite domains or replay bounds cannot represent the recorded execution, including simultaneously live abstract identities. Adjust the replay configuration to the observed need, without changing implementation limits, removing field checks, or automatically expanding unrelated MC campaigns.
- **Reference/Trace modeling issue**: the new implementation can take a transition that the current reference or wrapper does not faithfully express. Fix the behavioral owner in the reference first, then update MC/Trace/Update mappings.
- **Legitimately obsolete archived behavior**: an old-version trace traverses behavior intentionally removed by the update. Preserve and disposition the archived trace; fresh new-version traces remain the gate.
- **Abstraction gap**: apply the main trace workflow's evidence test. Bridge it only when doing so preserves bug-finding value.

A trace mismatch alone is not a code-bug verdict. Do not force the model to an intended paper algorithm, and do not weaken post-state checks to make a trace pass.

Before deferring a failed replay, localize the blocked guard/state and perform bounded, evidence-directed checks of replay configuration and trace interpretation. A prior "abstraction gap" label is a hypothesis, not a current diagnosis; other passing scenarios do not resolve the failure. If the investigation must stop within the available budget, record what was checked, what remains unresolved, and why further work was deferred. Do not relabel an unexplained mismatch as harmless limited coverage.

Passing traces establish conformance for the observed executions; they do not validate every behavior the model permits. For the update's important assumptions and any model repair, use source-backed boundary scenarios and check that logged values have the intended abstract meaning. Do not derive a Trace expectation solely from the reference assignment it is meant to validate. Investigate contradictions even when the old suite used the same interpretation.

## 3. Repair with Local Feedback

Any semantic repair reopens the affected Generation chapters, but related edits may form one repair batch rather than triggering full replay after each edit:

- repair the complete reference and all dependent wrappers/configs;
- recheck Affected/Interaction Actions, `EnvUpdate`, properties, and source mappings;
- apply the generation completeness review to the batch, including its effects on unchanged behavior.

Start with a source-to-model comparison that distinguishes a correct repair from a plausible wrong one: relevant guards, effects, and observable results. For executable feedback, prefer the original failing trace or a short retained trace that exercises the repaired behavior. A bounded local check of the actual TLA+ operators can help resolve a specific semantic uncertainty; do not copy their logic into a separate test model. Synthetic states are diagnostic inputs, not implementation traces or evidence of reachability.

Choose feedback by what it can reveal, not by a fixed test count. Broaden replay when shared state, trace interpretation, or uncertain dependencies make a local selection unreliable. Local checks guide the next edit; they do not establish full convergence or replace required update coverage.

Model-only repairs do not require a fresh implementation run when the source/build and scenario/capture assumptions still match the retained new-version traces. Reprocess raw events if that faithfully repairs the mapping; recollect only affected traces when captured information is missing or invalid. Add a real scenario or probe only to resolve a specific remaining uncertainty or required coverage gap. Do not weaken a required field check to avoid collection.

For a prior `NO_MODEL_CHANGE` disposition, compare the mismatch with both source revisions. A missed change in projected implementation behavior reopens the Chapter 1 decision gate. An existing model defect requires repair and renewed validation, while the source-delta disposition remains unchanged. Record the reason separately so file changes are not mistaken for implementation changes.

## 4. Full Regression on the Stable Candidate

After related repairs stabilize, replay the complete retained new-version suite against that candidate. This is required before initial model-checking campaign entry and, if later repairs invalidate it, again before final convergence. Reuse a completed full replay when its checked semantics, trace set, and capture assumptions still apply; do not rerun solely because another workflow boundary was reached. A failure reopens the affected repair batch.

Record repairs, local checks, pending regression, and the final full-suite outcome concisely in `spec/changelog.md`. Bind each retained trace's outcome to the model/configuration actually checked; one completion log does not establish full-suite validation. Unresolved required replays or unvalidated key effects prevent full validation, even if the implementation tests passed or the workflow process exited normally. Keep archived old-version evidence distinct from retained new-version traces, and do not reuse results invalidated by later edits.
