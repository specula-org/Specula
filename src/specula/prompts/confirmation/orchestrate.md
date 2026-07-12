# Bug Confirmation Task: {{name}}

Confirm and reproduce the bugs found in **{{name}}** by both model checking and
code review. This task is only the loop and aggregation; the per-finding
methodology is the single-bug skill (`guide.md`) applied to each candidate.

## Inputs
- MC findings (with counterexamples): {{bug_report}}
- Code-review findings: {{brief}}
- Source code: {{repo}}
- Spec directory: {{spec_dir}}

## Methodology (single-finding — apply to EACH candidate)
Use the installed Specula skill {{bug_confirmation_skill}}. Read it in full and
follow it exactly.

## 1. Consolidate
Merge the two sources into one candidate list, deduping by mechanism + site (the
same defect at the same `file:line` from both sources = one candidate).

## 2. For EACH candidate — apply the single-bug skill
For every candidate, run `guide.md` in full on that ONE finding: Phase 1
(investigation — record its evidence to a per-finding `investigation.md`, judge
nothing except the code-review × known drop) → Phase 2 (reproduction) → decide
exactly one verdict from the decision table, using the investigation record plus
the reproduction result. Apply **only** the skill's single pre-filter (code-review
× already-reported → drop — an existing issue/PR/CVE reported this exact defect;
developer suspicion or a TODO does NOT count). Invent no other pre-filter — never
skip a candidate as "defensive coding", "style", or "theoretical-only".

For `PENDING REPAIR`, the per-finding step produces only a semantic draft under
`{{spec_dir}}/../confirmation/<finding-id>/repair-request.body.md`; it never
allocates an RR or writes the shared queue. In this legacy single-agent mode you
also serve as the sole allocator, but only after the per-finding decisions are
complete: validate each draft, scan active and deferred RR ids serially, stamp
the dispatcher-owned lifecycle and History fields, and publish the final file.
Never let an individual finding allocate while it is being investigated.

## Before any `REPRODUCED` — the reachability checklist (per finding)
For every finding you are about to mark `REPRODUCED`, answer these explicitly in its entry (they are checked against the captured output):
1. Did **Level 0 or Level 1 alone** trigger it — real public API / normal ops, timing help only? **yes / no**.
2. If **no**, and you used Level 2 (state injection) or Level 3 (source patch): the injected pre-condition must be reachable through a **real-API call sequence** or correspond to an admissible **counterexample-trace step**. Paste the sequence or cite the exact step.
3. Which **real consumer/caller** observes a wrong outcome? Name it (`file:line`), or state the consequence is argued-only (a finding, not a reproduced bug).
4. Is the bad state **permanent**, or does a downstream mechanism (sync / loopback / resend / a caller guard) later **resolve or mask** it? A transient snapshot the system afterwards fixes is NOT a reproduced bug; a real defect a safeguard currently masks → `MASKED` (a finding), naming the mechanism — not `REPRODUCED`, not `FALSE POSITIVE`.

If you cannot honestly answer these in the finding's favour, do NOT manufacture a pass. Route by source:

| Source | Other valid outcomes | Never use |
|---|---|---|
| MC | `MASKED`, `ENV_LIMITED`, `PENDING REPAIR`, `NEEDS MORE INFO` | `FALSE POSITIVE`, `DROPPED` |
| Code Review | `MASKED`, `ENV_LIMITED`, `FALSE POSITIVE`, `DROPPED`, `NEEDS MORE INFO` | `PENDING REPAIR` |

`DROPPED` remains only for the code-review × already-reported pre-filter. Every honest outcome beats a fabricated `REPRODUCED`.

## 3. Aggregate
Write every finding's entry to {{report}} (one `repro/` test per non-dropped
finding under {{repro_dir}}). The report is consumed by Phase 4b and the repair
loop, so use this canonical structure exactly:

- `Reproduced: <N> = <NEW> NEW + <KU> KNOWN-unfixed + <KF> KNOWN-fixed + <U> UNKNOWN`
- `Findings: <N> = <E> env-limited + <M> masked`
- `Dispositions: <N> total = <R> reproduced + <E> env-limited + <M> masked + <FP> false-positive + <NMI> needs-more-info + <D> dropped + <PR> pending-repair + <I> incomplete + <DEF> deferred`
- A table headed exactly `| Bug | Finding | Status |`, followed by one row per entry.
- One detail section per table row, headed `## Bug N: <title>`. Number sections consecutively from 1, keep table and section order identical, and emit exactly one row and one section for each entry.

Use zero for absent disposition categories; never omit `incomplete` or `deferred`
from the `Dispositions:` line.
