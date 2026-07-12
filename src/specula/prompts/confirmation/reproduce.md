# Confirm ONE finding: {{finding_id}}

Confirm finding **{{finding_id}}** by following the bug-confirmation skill
(`guide.md` + `phases/01-investigation.md` + `phases/02-reproduction.md`):
investigate, reproduce, then emit ONE verdict chosen from the skill's decision
table. Execute the skill — do not restate it.

{{context}}

## Output (the dispatcher parses these)
- Write and ACTUALLY EXECUTE `repro/test_bug{{finding_id}}_*`.
- Header fields:
  - `- **Source**: MC` (real counterexample) or `Code Review` (no-violation / code-review)
  - `- **Novelty**: NEW` or `KNOWN (cite: <URL/dataset-id>; fix-status: unfixed|fixed)` — set from evidence, not by default (see the skill); Code Review AND known → `VERDICT: DROPPED`. Before writing `NEW`, do at least one prior-report search — upstream issues **and recently merged/closed PRs** (a fix that landed days ago still makes it KNOWN); `NEW` means you looked and found nothing for THIS mechanism, not that you skipped looking. (Do this via the issue tracker / git history only — do NOT open `bug-report.md` or other findings, per the "Do NOT" list below.)
  - `- **Location**: file:line`
- Body sections (they become the verdict body): `## Description`, `## Trigger scenario`, `## Developer intent`, `## Reproduction result` (paste real output), `## Recommendation`.
- End your ENTIRE response with one line: `VERDICT: <one of: {{canon}}>`.
- For `PENDING REPAIR`: also write `{{fdir}}/repair-request.body.md` using the installed skill's repair-request format — YAML frontmatter OMITTING `id`/`status`/`round` (the dispatcher owns those), carrying `target:` (SPEC_REPAIR | FAULT_MODEL | INVARIANT), `counterexample:`, and a `scope:` with the concrete `hunt_cfgs` / `invariants` / `actions` this CE came from; then `## Trigger`, `## Evidence`, optional `## Proposed change`, and a one-line `## History` seed.

## Before any `VERDICT: REPRODUCED` — answer this checklist in your response
State each answer explicitly (it will be checked against your captured output):
1. Did **Level 0 or Level 1 alone** trigger it — real public API / normal ops, timing help only? **yes / no**.
2. If **no**, and you used Level 2 (state injection) or Level 3 (source patch): the injected pre-condition must be reachable through a **real-API call sequence** or correspond to an admissible **counterexample-trace step**. Paste the sequence or cite the exact step.
3. Which **real consumer/caller** observes a wrong outcome? Name it (`file:line`), or state the consequence is argued-only (a finding, not a reproduced bug).
4. Is the bad state **permanent**, or does a downstream mechanism (sync / loopback / resend / a caller guard) later **resolve or mask** it? A transient snapshot the system afterwards fixes is NOT a reproduced bug; a real defect a safeguard currently masks → `VERDICT: MASKED` (a finding), naming the mechanism — not `REPRODUCED`, not `FALSE POSITIVE`.

If you cannot honestly answer these in the bug's favour, do NOT manufacture a pass. Route by source:

| Source | Other valid outcomes | Never use |
|---|---|---|
| MC | `MASKED`, `ENV_LIMITED`, `PENDING REPAIR`, `NEEDS MORE INFO` | `FALSE POSITIVE`, `DROPPED` |
| Code Review | `MASKED`, `ENV_LIMITED`, `FALSE POSITIVE`, `DROPPED`, `NEEDS MORE INFO` | `PENDING REPAIR` |

`DROPPED` remains only for the code-review × already-reported pre-filter. Every honest outcome beats a fabricated `REPRODUCED`.

## Do NOT
- Do not read or touch other findings, the spec files, `bug-report.md`, or `confirmed-bugs.md`. Do not allocate an RR number yourself.
- Do not fabricate or force the trigger to reach `REPRODUCED`: no hand-built unreachable pre-condition, no mock emitting what a real peer never sends, no source patch that creates the symptom.
