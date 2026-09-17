# Final Incremental Result

Write `spec/final-result.json` in the working output directory. Keep narrative fields short and plain text; detailed reasoning belongs in the linked evidence. Use the run ID provided by the task.

```json
{
  "version": 1,
  "run_id": "<current-run-id>",
  "summary": "Updated the model and harness; the admission defect remains present.",
  "validation_limits": ["The bounded model-checking campaign did not exhaust its queue."],
  "findings": [
    {
      "id": "CR-3",
      "title": "Configuration admission released before application",
      "status": "REPRODUCED",
      "source": "code-review",
      "cause": "Advance moves the admission cursor before membership application.",
      "trigger": "Advance the first entry, then propose a second before applying the first.",
      "consequence": "A second membership change commits before the first takes effect.",
      "severity": "High",
      "evidence": ["spec/confirmation-CR-3.md"],
      "persistence": {
        "sites": ["raft.go:advance"],
        "premises": ["The caller contract permits acknowledgement before membership application."],
        "dependencies": [{"root": "source", "path": "raft.go"}]
      }
    }
  ]
}
```

For a current confirmation, `id`, `title`, `status`, `source`, `cause`, `trigger`, `consequence`, and `evidence` are required. `source` is `model-checking` only for an actual model-checking counterexample; otherwise use `code-review`. Use the final confirmation status, including any completed debate or repair. New findings need unused IDs; reanalysis of the same historical issue keeps its ID. `FIXED` and other dispositions use the same fields and cite the evidence supporting that conclusion.

Evidence paths must identify existing nonempty files under `spec/`, `harness/`, or `traces/`, or top-level Markdown files. Do not cite the generated final reports as their own confirmation evidence. Keep reproduction commands, observed outcomes, and source identity in the evidence. `severity` is optional (`Critical`, `High`, `Medium`, or `Low`); omission is shown as unassessed, never inferred by the renderer.

`persistence` is optional. For automatic reuse, supply the applicable `premises` and relevant `dependencies` using the existing [Persistent Findings selectors](../../bug-confirmation/references/persistent-findings.md). Optional `sites`, `actions`, and `invariants` help matching; model-linked findings also need model dependencies. The tool computes hashes, source identity, and the historical-record revision binding. Missing or invalid reuse metadata leaves the current conclusion intact and marks the record **not automatically reusable**.

To reuse a historical conclusion instead of confirming it again, use a short entry:

```json
{"id": "CR-3", "reuse": "Same mechanism and consequence; the caller contract and reachability premises still apply."}
```

The command checks the historical record and dependencies and generates the reuse receipt. Do not copy the original conclusion into this entry or relabel it as a current reproduction. A failed applicability check requires targeted reanalysis; it does not silently reuse stale evidence. Optional `severity` can be carried from a supported prior classification.

Include every prior unresolved finding, even if no new defect was found. Use `"findings": []` only when there are no new or prior unresolved findings. An omitted prior defect is not considered fixed.

Generate and validate the final outputs:

```bash
specula ci-result --work=/path/to/current/.specula-output
```

This creates `ci-report.md`, `confirmed-bugs.md`, `bug-severity.md`, `.summary-findings.md`, `ci-verdict.json`, and the existing persistent records. Generated files are overwritten on each invocation; edit only the final result and its evidence. The command returns success even when the valid CI verdict is FAIL. Core input errors return failure with a correction message. After an interruption, use the normal manual resume; no automatic correction loop is added.
