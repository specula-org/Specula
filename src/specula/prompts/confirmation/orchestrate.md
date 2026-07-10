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

## 3. Aggregate
Write every finding's entry to {{report}} (one `repro/` test per non-dropped
finding under {{repro_dir}}), and record two one-line headline splits at the top
so confirmed **bugs** and the **finding** tier are counted separately:
- `Reproduced: <N> = <M> NEW + <K> KNOWN-unfixed` — and, if any, `KNOWN-fixed: <J>` separately (each needs a version recheck).
- `Findings: <J> = <R> unreproduced + <L> masked` — real defects that are not confirmed live bugs, surfaced so they are neither miscounted as bugs nor lost as false positives.
