# Match model-checking findings to confirmed Scenarios: {{name}}

You are the Phase-4 **step 0** consolidator for a run that confirmed the Phase 1
Scenarios before modeling. Those candidates and their verdicts are final. List the
model-checking findings and mark which earlier candidates each one repeats. You do
NOT judge whether anything is a real bug — that is the confirmation step's job.

## Sources
- **Model-checking findings**: {{mc_src}}
  These are already concrete bugs (one Scenario can produce several — e.g.
  `MC_hunt_scenario2` → Bug 1 AND Bug 2). Keep that granularity. id `MC-<n>`,
  `source: "model-checking"`.
- **Earlier Scenario candidates**: `{{scenario_candidates}}`, with their final
  verdicts in `{{scenario_report}}`.

## The one job: match, do not filter
For EACH model-checking finding, decide whether it is the same defect as one or
more earlier candidates — same mechanism, same code site. Compare its affected
code and root cause with what the earlier verdict established, not only with the
Scenario hypothesis. A shared Scenario, invariant, title, or file alone does not
make the same defect.

Record the matching earlier ids in `confirm_first_match` (for example
`["CR-3"]`), or `[]` when none matches. Match regardless of the earlier verdict;
the dispatcher decides what to confirm again. Emit every model-checking finding;
do not drop, merge, or re-judge any of them.

## Schema — read it first
Use the installed Specula skill {{validation_workflow_skill}}. Within it, read and follow the
findings JSON format. The top-level object uses
`generated_by: "consolidate"` and the list key `findings`. Each entry: `id`
(unique, filesystem-safe), `title`, `source`, `scenario`, `severity`,
`invariant`, `config`, `counterexample`, `affected_code` (file:line list),
`summary` (3-5 self-contained sentences), and `confirm_first_match`.

## Output
Write ONLY the JSON to `{{out}}` — model-checking findings only; the dispatcher
adds the earlier candidates. Emit `"findings": []` if there are no
model-checking findings. Print nothing else.
