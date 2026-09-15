# Persistent Findings

Avoid paying again for completed analysis and verification. **As soon as any candidate defect appears, do a lightweight lookup before complex code analysis, counterexample diagnosis, developer-history research, or reproduction work.** This applies to every discovery stage and to both MC and code-review candidates.

Use the target's `.specula-output` as `--work`. Pipeline callers supply `persistent-findings-context.json` once the source checkout is known. If no context is present, initialize it with the source, run ID, and optional historical output directory:

```bash
specula findings --work /path/to/output --source /path/to/source --run-id current-run --previous /path/to/prior/output init
```

Omit `--previous` when no history is available. One-shot runs and CI initialization can select a prior output with `--findings-from=PATH`. Only unresolved records and their selected evidence are imported; work on the current model and source. Without historical records, continue normal analysis and save completed findings. Upstream-only known reports retain their existing treatment.

## Lookup First

```bash
specula findings --work /path/to/target/.specula-output lookup --query ReceiveReply --query ReplySafety
```

Use already available source paths/symbols, model Actions, invariant names, and the observed symptom. The helper returns at most five short summaries by default. Read a matched record with `show --id ID`; open only its relevant evidence. Do not load the whole index or read all old reports. A shared ID, invariant, title, or site alone does not establish the same defect. If a quick comparison cannot establish the same mechanism and consequence, proceed with normal analysis rather than turning matching into another investigation.

For a reliable match, run `check --id ID`. It compares the recorded source/model dependencies and checks historical evidence integrity. Then briefly check the recorded premises, including reachability, configuration, environment limits, and masking mechanisms. File hashes do not decide these semantic questions. An unrecorded dependency, unclear premise, new consequence, or changed relevant logic requires targeted reanalysis. Changes outside the recorded dependencies do not invalidate all old findings.

If the same mechanism/consequence and premises still apply:

```bash
specula findings --work /path/to/target/.specula-output reuse --id MC-1 --reason 'Same mechanism and consequence; the recorded configuration and reachability premises remain applicable.'
```

Replace the example reason with the actual brief applicability basis. Reuse keeps the stable issue ID and the original classification and evidence limits. Skip completed investigation, reproduction development/execution, and repeated classification. The helper writes a run-bound receipt under `spec/finding-reuse/`. The caller validates it against the final source/model and includes the historical conclusion in its report. If later edits invalidate it, remove the receipt and reanalyze that issue.

## Record Completed Work Once

After confirmation finishes, persist only unresolved `REPRODUCED`, `ENV_LIMITED`, and `MASKED` findings. Save identity, cause, trigger, consequence, classification, premises, relevant source/model/invariant dependencies, and selected evidence. Do not persist false positives, model/invariant repair issues, or incomplete investigations in this registry.

After confirmation, write a proposal to `spec/issue-input/ID.json`, or to `confirmation/ID/issue.json` in a per-finding worker. The pipeline registers it using the final confirmation verdict, including debate. Standalone callers use `record --input /path/to/proposal.json`. Fill it from the completed analysis; do not launch another investigation to produce metadata. Dependency fingerprints use the source supplied by the caller and the current model; CI supplies its frozen pre-instrumentation source.

Allocate an unused ID for a new defect, even when its local MC number collides with an old issue. When reanalysis updates an existing historical issue, include `"revises": "<record_sha256 from show>"` in the proposal to identify that prior record explicitly. Reusing a local number does not establish issue identity.

```json
{
  "id": "MC-1",
  "title": "Reply updates state before checking its term",
  "status": "REPRODUCED",
  "source": "model-checking",
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

Select the actual confirmation, trace/log, reproduction scripts, and required helper files. The tool bundles only the selected evidence and retains its original run/source identity. To make a completed record available for matching again within this run, use `record --input /path/to/proposal.json`; finalization also registers proposals automatically. If subsequent edits affect it, refresh the analysis and proposal before finishing. Old outputs lacking dependency metadata remain visible as requiring analysis and cannot be automatically reused.

## Resolve and Report

Keep reused findings visible as **Still unresolved; historical conclusion reused**, with links to the original evidence and its limits. Retain the original classification and evidence limits. Never relabel reuse as a fresh reproduction or drop a prior confirmed issue through the novelty filter.

A resolved record is removed only after targeted review confirms the root cause is fixed, with current source and reproduction/control evidence. The caller removes its record, bundled evidence, and lookup entry; an absent rediscovery does not delete a finding. Do not keep resolved archives or tombstones in the matching collection. CI-specific reporting and verdict requirements belong to the incremental-modeling guide.
