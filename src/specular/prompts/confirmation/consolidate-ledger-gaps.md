# Complete the candidate list: {{name}}

The Phase-4 step 0 candidate list `{{current}}` leaves these defect-ledger rows
with neither a candidate nor a recorded disposition: {{missing}}.

The ledger is `{{ledger}}`. For each listed row, either:
- emit it as its own candidate: id `CR-<row id>` (e.g. `CR-D-3`),
  `source: "code-review"`, `ledger_ids: ["<row id>"]`, `invariant`, `config`,
  `counterexample` = null, and a summary that states the row's location,
  trigger, and wrong behavior; or
- if a model-checking candidate's counterexample reproduces it (same code site,
  same mechanism), add the row id to that candidate's `ledger_ids`; or
- if it is an exact duplicate of another row, record it in the top-level
  `ledger_dispositions` list as `{"id": "<row id>", "disposition": "absorbed" |
  "merged" | "removed", "into": "<candidate id or null>", "reason": "<why>"}`.

Listing a row in a code-review Scenario candidate's `ledger_ids` does not count.

Keep every existing candidate and disposition unchanged. Do not judge whether a
row is a real bug and do not drop known defects — confirmation decides.

Write the complete updated JSON (same format as `{{current}}`) to `{{out}}`.
Print nothing else.
