# Validation 3: Trace Validation Loop

Follow the installed Specula **tla-trace-workflow** skill for validation, layered debugging, and evidence-backed fixes. This chapter defines only the incremental ordering and back-edges.

## 1. Validate in Information Order

1. Validate one short fresh trace that reaches an affected Action.
2. Validate fresh interaction traces for producer/consumer/fault Scenarios.
3. Validate fresh traces regenerated from the prior regression scenarios.
4. Run the trace workflow's parallel validation over every retained fresh new-version trace.

For Category B, validation succeeds only when some legal timebox interleaving fully consumes the trace. Do not diagnose a single pruned ordering as a mismatch.

## 2. Classify Before Editing

For each failure, identify which evidence is wrong:

- **Harness/capture mismatch**: event name, field, identity, timing, ID mapping, preprocessing, or scenario setup disagrees with the real action. Fix the harness or mapping and recollect the trace.
- **Reference/Trace modeling issue**: the new implementation can take a transition that the current reference or wrapper does not faithfully express. Fix the behavioral owner in the reference first, then update MC/Trace/Update mappings.
- **Legitimately obsolete archived behavior**: an old-version trace traverses behavior intentionally removed by the update. Preserve and disposition the archived trace; fresh new-version traces remain the gate.
- **Abstraction gap**: apply the main trace workflow's evidence test. Bridge it only when doing so preserves bug-finding value.

A trace mismatch alone is not a code-bug verdict. Do not force the model to an intended paper algorithm, and do not weaken post-state checks to make a trace pass.

Passing traces establish conformance for the observed executions; they do not validate every behavior the model permits. For the update's important assumptions and any model repair, use source-backed boundary scenarios and check that logged values have the intended abstract meaning. Do not derive a Trace expectation solely from the reference assignment it is meant to validate. Investigate contradictions even when the old suite used the same interpretation.

## 3. Reopen Generation When Evidence Changes

Any semantic base/MC/Trace fix reopens the affected Generation chapters:

- repair the complete reference and all dependent wrappers/configs;
- recheck Affected/Interaction Actions, `EnvUpdate`, properties, and source mappings;
- rerun the generation completeness review;
- recollect any trace whose event schema or capture timing changed;
- restart validation from the first affected trace, then rerun the full fresh suite.

For a prior `NO_MODEL_CHANGE` disposition, compare the mismatch with both source revisions. A missed change in projected implementation behavior reopens the Chapter 1 decision gate. An existing model defect requires repair and renewed validation, while the source-delta disposition remains unchanged. Record the reason separately so file changes are not mistaken for implementation changes.

Record every harness, trace, and semantic fix concisely in `spec/changelog.md`, distinguishing archived-trace disposition from fresh-trace validation.
