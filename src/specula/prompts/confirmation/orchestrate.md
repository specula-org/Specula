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

## Before any `REPRODUCED` — the reachability checklist (per finding)
For every finding you are about to mark `REPRODUCED`, answer these explicitly in its entry (they are checked against the captured output):
1. Did **Level 0 or Level 1 alone** trigger it — real public API / normal ops, timing help only? **yes / no**.
2. If **no**, and you used Level 2 (state injection) or Level 3 (source patch): paste the **real-API call sequence** that actually produces the injected pre-condition, **or** cite the exact **counterexample-trace step** it instantiates. If your OWN Level-0/1 attempt failed to produce that state, that is proof it is NOT reachable — do not then label the injection "reachable".
3. Which **real consumer/caller** observes a wrong outcome? Name it (`file:line`), or state the consequence is argued-only (a finding, not a reproduced bug).
4. Is the bad state **permanent**, or does a downstream mechanism (sync / loopback / resend / a caller guard) later **resolve or mask** it? A transient snapshot the system afterwards fixes is NOT a reproduced bug; a real defect a safeguard currently masks → `MASKED` (a finding), naming the mechanism — not `REPRODUCED`, not `FALSE POSITIVE`.

If you cannot honestly answer these in the finding's favour, do NOT manufacture a pass — settle it per the skill's decision table. Every honest outcome (MASKED / ENV_LIMITED / PENDING REPAIR / DROPPED / FALSE POSITIVE / NEEDS MORE INFO) beats a fabricated `REPRODUCED`.

## 3. Aggregate
Write every finding's entry to {{report}} (one `repro/` test per non-dropped
finding under {{repro_dir}}), and record two one-line headline splits at the top
so confirmed **bugs** and the **finding** tier are counted separately:
- `Reproduced: <N> = <M> NEW + <K> KNOWN-unfixed` — and, if any, `KNOWN-fixed: <J>` separately (each needs a version recheck).
- `Findings: <J> = <R> env-limited + <L> masked` — real defects that are not confirmed live bugs, surfaced so they are neither miscounted as bugs nor lost as false positives.
