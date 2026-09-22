# Reproduction Entry: Confirm Incremental Findings

This is a thin entry point. Read and follow the installed Specula **bug-confirmation** skill completely for investigation, reproduction, verdicts, evidence, and repair requests. Do not duplicate its escalation ladder or output formats here.

## Preconditions

- Collect code-review Scenarios in the current `modeling-brief.md`, as in one-shot runs. Record actual MC counterexamples in `spec/bug-report.md` and the standard `spec/findings.json` format; use an empty findings list when MC found no violation. A Scenario with no counterexample remains code-review-sourced.
- Each MC finding names its violated property, saved TLC output/trace, current source revision, reference Actions, and update Scenario. A focused-only violation must also be admitted by full current reference behavior, or have a valid open/discharge argument.
- Match persistent findings before expensive confirmation. Reuse applicable historical conclusions without repeating reproduction. Preserve the main bug-confirmation workflow's code-review × already-reported pre-filter.

## Incremental Context

Before delegating, attach only the evidence the main skill needs:

- the changed source sites and source-reference-Update mappings;
- the affected and interacting Actions in the counterexample;
- relevant prior finding/reproduction/repair lineage from the old run;
- whether the update introduced a new mechanism, moved an old mechanism, removed a mask, or merely made an existing path reachable.

Confirm and reproduce against the new implementation revision. When the same test and environment are compatible with the old revision, run it as a control to distinguish introduced, newly exposed, and pre-existing behavior. The old-version control strengthens attribution but does not replace reproduction on the new version.

## Delegate and Preserve Verdict Boundaries

After completing validation and model checking, call `request_bug_confirmation` and follow its yield instruction. The controller runs the same candidate consolidation, per-finding confirmation, optional debate, and aggregation as one-shot runs while this conversation waits. It uses the main **bug-confirmation** workflow to:

1. investigate code reachability and developer/known-status evidence;
2. attempt reproduction through the real interface and its escalation ladder;
3. verify that the observed sequence, consequence, and code path match the counterexample or code-review claim;
4. emit the standard verdict and artifacts;
5. issue a cited repair-request draft when the finding is a spec, invariant, or fault-model artifact.

Never classify a new invariant violation as a model defect merely because it appears after the update. A faithful new model may have exposed a real implementation bug. Conversely, a syntactically valid focused counterexample is not a bug until code reachability and consequence are established.

On continuation, read `spec/confirmation-report.md` and the referenced per-finding evidence. Handle cited model/invariant repair requests in the main conversation, revalidate the affected behavior, and request confirmation again when needed. Keep stable finding IDs and completed evidence. Use the resulting dispositions in `spec/final-result.json`; retain the evidence it cites under the supported artifact directories.
