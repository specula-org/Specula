# Reproduction Entry: Confirm an Incremental Counterexample

This is a thin entry point. Read and follow the installed Specula **bug-confirmation** skill completely for investigation, reproduction, verdicts, evidence, and repair requests. Do not duplicate its escalation ladder or output formats here.

## Preconditions

- An actual TLC counterexample exists. A Scenario, code suspicion, or model-checking run with no violation is not an MC finding.
- The finding names its violated property, saved TLC output/trace, current source revision, reference Actions, and update Scenario.
- A focused-only violation must also be admitted by full current reference behavior, or be supported by a valid open/discharge argument. Otherwise return it to model-checking repair before reproduction.
- Trace validation and model-checking evidence identify the current suite used to produce the finding.

## Incremental Context

Before delegating, attach only the evidence the main skill needs:

- the changed source sites and source-reference-Update mappings;
- the affected and interacting Actions in the counterexample;
- relevant prior finding/reproduction/repair lineage from the old run;
- whether the update introduced a new mechanism, moved an old mechanism, removed a mask, or merely made an existing path reachable.

Confirm and reproduce against the new implementation revision. When the same test and environment are compatible with the old revision, run it as a control to distinguish introduced, newly exposed, and pre-existing behavior. The old-version control strengthens attribution but does not replace reproduction on the new version.

## Delegate and Preserve Verdict Boundaries

Use the main **bug-confirmation** workflow to:

1. investigate code reachability and developer/known-status evidence;
2. attempt reproduction through the real interface and its escalation ladder;
3. verify that the observed sequence, consequence, invariant, and code path match this counterexample;
4. emit the standard verdict and artifacts;
5. issue a cited repair-request draft when the finding is a spec, invariant, or fault-model artifact.

Never classify a new invariant violation as a model defect merely because it appears after the update. A faithful new model may have exposed a real implementation bug. Conversely, a syntactically valid focused counterexample is not a bug until code reachability and consequence are established.

Accept MC counterexamples only. Do not discover or enqueue standalone code-review findings.
