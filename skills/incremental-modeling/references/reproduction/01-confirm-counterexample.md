# Reproduction Entry: Confirm an Incremental Counterexample

First run the lightweight lookup in the installed **bug-confirmation** skill’s `references/issue-reuse.md`. Reuse reliably matched conclusions with unchanged dependencies and premises before entering investigation or reproduction. This is a thin entry point for the remaining work. Read and follow the installed Specula **bug-confirmation** skill completely for investigation, reproduction, verdicts, evidence, and repair requests. Do not duplicate its escalation ladder or output formats here.

## Preconditions

- For a new finding, an actual TLC counterexample exists. A Scenario, code suspicion, or model-checking run with no violation is not an MC finding. Prior bug and warning findings enter when their historical conclusion cannot be reused, even if this run finds no new counterexample.
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

Reanalyze only prior issues with changed dependencies/premises, new consequences, or uncertain identity. Start from the applicable existing analysis and reproduction materials and record the current disposition under the same issue ID. Skip the known-code-review pre-filter when rechecking an already confirmed finding. When the update fixes a prior defect, record `FIXED` in the CI verdict with source and fresh test/control evidence.

## Delegate and Preserve Verdict Boundaries

Use the main **bug-confirmation** workflow to:

1. investigate code reachability and developer/known-status evidence;
2. attempt reproduction through the real interface and its escalation ladder;
3. verify that the observed sequence, consequence, invariant, and code path match this counterexample;
4. emit the standard verdict and artifacts;
5. issue a cited repair-request draft when the finding is a spec, invariant, or fault-model artifact.

Never classify a new invariant violation as a model defect merely because it appears after the update. A faithful new model may have exposed a real implementation bug. Conversely, a syntactically valid focused counterexample is not a bug until code reachability and consequence are established.

Accept new MC counterexamples and prior bug and warning findings for rechecking. Do not discover or enqueue new standalone code-review findings.
