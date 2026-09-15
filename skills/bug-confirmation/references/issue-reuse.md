# Reuse Unresolved CI Issues

Avoid paying again for completed analysis and verification. **As soon as any candidate defect appears, do a lightweight lookup before complex code analysis, counterexample diagnosis, developer-history research, or reproduction work.** This applies to every discovery stage and to both MC and code-review candidates.

Use the current CI target's `.specula-output` as `--work` below. The helper is `specula issues` (or `"$SPECULA_ROOT/specula" issues` inside a pipeline). If no unresolved-issue index exists, continue the normal workflow. Upstream-only known reports continue through the existing known-status policy; they receive no new shortcut here.

## Lookup First

```bash
specula issues --work /path/to/target/.specula-output lookup --query ReceiveReply --query ReplySafety
```

Use already available source paths/symbols, model Actions, invariant names, and the observed symptom. The helper returns at most five short summaries by default. Read a matched record with `show --id ID`; open only its relevant evidence. Do not load the whole index or read all old reports. A shared ID, invariant, title, or site alone does not establish the same defect. If a quick comparison cannot establish the same mechanism and consequence, proceed with normal analysis rather than turning matching into another investigation.

For a reliable match, run `check --id ID`. It compares the recorded source/model dependencies and checks historical evidence integrity. Then briefly check the recorded premises, including reachability, configuration, environment limits, and masking mechanisms. File hashes do not decide these semantic questions. An unrecorded dependency, unclear premise, new consequence, or changed relevant logic requires targeted reanalysis. Changes outside the recorded dependencies do not invalidate all old findings.

If the same mechanism/consequence and premises still apply:

```bash
specula issues --work /path/to/target/.specula-output reuse --id MC-1 --reason 'Same mechanism and consequence; the recorded configuration and reachability premises remain applicable.'
```

Replace the example reason with the actual brief applicability basis. Reuse keeps the stable issue ID and the original classification and evidence limits. Skip completed investigation, reproduction development/execution, and repeated classification. The helper writes a run-bound receipt; CI validates it again against the final source/model and merges it into `ci-verdict.json`, even if the issue was not rediscovered. If later edits invalidate it, remove its current `spec/issue-reuse/ID.json` receipt and reanalyze that issue.

Before finishing a CI update, page through the unresolved summaries with `lookup --limit 5 --offset N` without a query. Each prior issue needs either an applicable reuse receipt or a current disposition. Absence of a new counterexample is not a fix. Reuse does not disable invariants or replace validation/checking of the updated model and its interactions.

## Record Completed Work Once

After confirmation finishes, persist only unresolved `REPRODUCED`, `ENV_LIMITED`, and `MASKED` findings. Save identity, cause, trigger, consequence, classification, premises, relevant source/model/invariant dependencies, and selected evidence. Do not persist false positives, model/invariant repair issues, or incomplete investigations in this registry.

Write a proposal to `spec/issue-input/ID.json` in an incremental run. A one-shot confirmation worker writes only its own `confirmation/ID/issue.json`; the controller registers it after the final confirmation verdict, including debate. Use the existing analysis to fill it; do not launch another analysis just to produce metadata. The CI controller captures dependencies from the frozen pre-instrumentation source and the final model.

Allocate an unused ID for a new defect, even when its local MC number collides with an old issue. When reanalysis updates an existing historical issue, include `"revises": "<record_sha256 from show>"` in the proposal to identify that prior record explicitly. Reusing a local number does not establish issue identity.

```json
{
  "id": "MC-1",
  "title": "Reply updates state before checking its term",
  "status": "REPRODUCED",
  "cause": "ReceiveReply updates the accepted value before validating the reply term.",
  "trigger": "An older reply arrives after a newer value was accepted.",
  "consequence": "The consumer observes the older value.",
  "sites": ["src/reply.go:ReceiveReply"],
  "actions": ["ReceiveReply"],
  "invariants": ["ReplySafety"],
  "premises": ["Delayed replies reach ReceiveReply; no caller filters their terms."],
  "dependencies": [
    {"root": "source", "path": "src/reply.go", "start": "func ReceiveReply(r Reply) {", "end": "// End ReceiveReply"},
    {"root": "work", "path": "spec/base.tla", "start": "ReceiveReply(r) ==", "end": "\\* End ReceiveReply"},
    {"root": "work", "path": "spec/ReplySafety.tla"},
    {"root": "work", "path": "spec/MC.cfg"}
  ],
  "evidence": ["spec/confirmation-MC-1.md", "repro/test_bugMC-1_reply.sh", "repro/MC-1.log"]
}
```

Selectors use a whole relevant file or an inclusive span between two existing, unique literal lines (`start`/`end`). Never add source markers just for caching. Include relevant callers, helpers, data definitions, model operators/invariants, and configuration on which the conclusion depends; a symptom line alone is not a sufficient scope. Prefer spans when unrelated code shares a file. A renamed, missing, or ambiguous boundary conservatively requires reanalysis. Record non-file assumptions explicitly in `premises`; do not claim hashes prove them.

Select the actual confirmation, trace/log, reproduction scripts, and required helper files. CI bundles only the selected evidence and retains its original run/source identity. To make a completed record available for matching again within this run, use `record --input /path/to/proposal.json`; finalization also registers proposals automatically. If subsequent edits affect it, refresh the analysis and proposal before finishing. Old outputs lacking dependency metadata remain visible as requiring analysis and cannot be automatically reused.

## Resolve and Report

Keep reused findings visible as **Still unresolved; historical conclusion reused**, with links to the original evidence and its limits. Their existing classification still determines CI failure/warning. Never relabel reuse as a fresh reproduction or drop a prior confirmed issue through the novelty filter.

When targeted review confirms the root cause is fixed, record `FIXED` with current source and reproduction/control evidence in the CI verdict. CI removes the issue's record, bundled evidence, and lookup entry from the active registry. Do not keep a resolved-issue archive or tombstones in the matching collection.
