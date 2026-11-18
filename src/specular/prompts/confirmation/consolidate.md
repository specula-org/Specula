# Consolidate + dedup findings into candidates.json: {{name}}

You are the Phase-4 **step 0** consolidator. Merge three finding sources into ONE
deduplicated candidate list. You do NOT judge whether anything is a real bug —
that is the confirmation step's job. You ONLY organize and remove duplicates.

## Sources
- **Model-checking findings**: {{mc_src}}
  These are already concrete bugs (one Scenario can produce several — e.g.
  `MC_hunt_scenario2` → Bug 1 AND Bug 2). Keep that granularity. id `MC-<n>`,
  `source: "model-checking"`.
- **Code-review Scenarios**: {{brief}} — the Modeling Brief and any companion
  documents it is split into; read all of them (the brief may not exist — then
  emit only MC candidates). Each `Scenario N` is a mechanism hypothesis, NOT a
  concrete bug.
- **Defect ledger**: {{ledger}} Each row (`D-<n>`) is one concrete suspected
  defect from Code Analysis, including low-level defects that were never
  modeled.

## The one job: dedup, do not filter
**Ledger rows.** Emit EACH ledger row as its own candidate: id `CR-<row id>`
(e.g. `CR-D-3`), `source: "code-review"`, `ledger_ids: ["D-3"]`, `invariant`,
`config`, `counterexample` = null, and a summary that states the row's location,
trigger, and wrong behavior. The one exception: a row that an MC candidate's
counterexample reproduces — same code site, same mechanism — is absorbed into
that MC candidate; add the row id to the MC candidate's `ledger_ids` and say why
in its `dedup_note`. Do not merge two ledger rows into one candidate unless they
are the same defect.

Every ledger row that does not get its own candidate MUST appear in the
top-level `ledger_dispositions` list: `{"id": "D-3", "disposition": "absorbed" |
"merged" | "removed", "into": "<candidate id or null>", "reason": "<why>"}`.
Removing a row is only for an exact duplicate of another row.

**Scenarios.** For EACH code-review Scenario, decide whether it is ALREADY represented by one or
more MC candidates — same mechanism, same code site (compare the Scenario's cited
`file:line` and mechanism against the MC candidates' affected code and root cause).

- **Covered by MC** → do NOT emit a separate code-review candidate. Instead add a
  `dedup_note` on the covering MC candidate(s): e.g. `"also covers code-review
  Scenario 1 (same seq-desync mechanism)"`. The MC candidate wins — it carries a
  counterexample.
- **Not covered** (MC found no violation for it, or it was never model-checked) →
  emit it as a candidate: id `CR-<n>`, `source: "code-review"`, with
  `invariant`, `config`, `counterexample` = null. List the ledger rows of this
  Scenario in its `ledger_ids` and end its summary with: "Ledger rows <ids> are
  confirmed as separate candidates; look for other defects in this mechanism,
  and report plainly if there are none."

Do NOT drop a Scenario for being "defensive coding", "test-coverage", "liveness
only", or "probably not a bug" — those are candidates too; confirmation
decides. Do NOT apply the code-review×already-known pre-filter here (it
needs an issue-tracker search — leave it to confirmation). Removing DUPLICATES is
the only removal you do.

## Schema — read it first
Use the installed Specular skill {{validation_workflow_skill}}. Within it, read and follow the
findings JSON format. The top-level object uses
`generated_by: "consolidate"` and the list key `findings`. Each entry: `id`
(unique, filesystem-safe), `title`, `source`, `scenario`, `severity`,
`invariant`/`config`/`counterexample` (null for code-review), `affected_code`
(file:line list), `summary` (3-5 self-contained sentences), optional
`dedup_note`, and `ledger_ids` (list, possibly empty). The top-level object also
carries `ledger_dispositions` (list, possibly empty).

## Output
Write ONLY the JSON to `{{out}}` — MC candidates first, then ledger-row
candidates, then Scenario candidates. Emit `"findings": []` if both sources are empty. Print nothing else.
