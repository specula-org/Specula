# Bug Classification and Findings Summary

Turn the final Phase 4a report into two final reporting artifacts. Complete them in order:

1. Classify every entry by external impact in `bug-severity.md`.
2. Write a concise, human-readable findings fragment in `.summary-findings.md`.

Finish and validate the severity classification before starting the findings fragment. Do not weaken, abbreviate, or otherwise change the classification task to make room for the second output.

## Scope

- **Input**: `<work_dir>/confirmed-bugs.md` — every entry already has a Phase 4 Status and supporting evidence.
- **Outputs**:
  - `<work_dir>/bug-severity.md` — a single table with one row per input entry.
  - `<work_dir>/.summary-findings.md` — a short result narrative consumed by the user-facing `summary.md`.
- **You do not**: write new bug analysis, change reproduction status, reject bugs, re-do investigation, or modify `confirmed-bugs.md`.

Classify each status exactly as follows:

| Phase 4 status | Class | Phase 4b action |
|---|---|---|
| `REPRODUCED` | bug | Assign `Critical` / `High` / `Medium` / `Low`. |
| `ENV_LIMITED`, `MASKED` | finding | Assign `Critical` / `High` / `Medium` / `Low` from the argued or masked consequence. Preserve the finding status; do not call it reproduced. |
| `FALSE POSITIVE`, `NEEDS MORE INFO`, `DROPPED`, `PENDING REPAIR`, `DEFERRED`, `INCOMPLETE` | disposition | Assign no severity (`—`). Record the disposition without turning it into a bug or finding. |

## Severity rubric

Severity is a property of **what the defect does to the system**, not of how easy it was to reproduce. An `ENV_LIMITED` finding can still be Critical when its sound production-impact argument establishes Critical harm. A `MASKED` finding is classified by the consequence the real defect would expose if the named mask were absent; keep the mask explicit in the reasoning.

| Tier | When to assign |
|---|---|
| **Critical** | Externally observable corruption, crash, hang, or deadlock with persistent client-side impact and no automatic recovery. Examples: data inconsistency across replicas after a single fault, signature verification failure on legitimate input, election that elects two leaders, lost-wakeup deadlock under realistic concurrency. |
| **High** | Externally observable but bounded harm OR internal invariant violation that demonstrably propagates to external effect. Examples: single failed response a client can retry, recoverable hang that times out, off-by-one that affects one slot/round, term-monotonicity break on crash-restart, missing leader check, missing quorum check, panic on attacker-controlled input. |
| **Medium** | Internal invariant violation without a directly demonstrated external effect, but with downstream risk. Examples: commit idempotency missing (re-commit produces same result so no harm today, but future code change could expose), ordering non-determinism (HashMap iteration), cache freshness gap (downstream read might be stale under specific composition). |
| **Low** | Hygiene / defensive coding gap / hardening recommendation. Examples: unused defensive guard, redundant lock, code-smell that the surrounding code already catches before any state escapes, deprecated path that is reachable but caught by a downstream guard. |

When in doubt between two tiers, prefer the higher tier and explain the uncertainty in the Reasoning. The downstream submission filter will downgrade if needed; over-classification is recoverable, under-classification is not.

## Severity is independent of reproduction status

This is the central rule that separates classification from confirmation:

- A **REPRODUCED Critical** bug → primary submission.
- A **REPRODUCED Low** bug → record but probably not submitted.
- An **ENV_LIMITED Critical** finding → Critical severity, while remaining explicitly unreproduced in this environment.
- A **MASKED Medium** finding → Medium severity, while naming the mechanism that currently masks the consequence.
- A disposition (`FALSE POSITIVE`, `NEEDS MORE INFO`, `DROPPED`, `PENDING REPAIR`, `DEFERRED`, or `INCOMPLETE`) → no severity (`—`).

## Classification process

For each entry in `confirmed-bugs.md`:

1. Read the entry's Status and its available Description, Trigger scenario, Developer intent investigation, Reproduction result, and Recommendation fields.
2. If its status is `REPRODUCED`, `ENV_LIMITED`, or `MASKED`, identify the **worst observable consequence** the defect enables under realistic conditions. "Realistic" means: code path is reachable from the system's public interface, faults assumed are within the system's stated fault model, attacker capability (if Byzantine) is within the model's threat model.
3. For those bugs/findings, match to the rubric and write a 1–2 sentence Reasoning that names the consequence and the conditions under which it appears. For `ENV_LIMITED`, cite the production-impact argument; for `MASKED`, name the mask.
4. For every other status, use Severity `—` and briefly state that the Phase 4 disposition is not severity-bearing. Do not re-decide it.

Do not re-do Phase 4a's investigation. If you find that Phase 4a's Status is wrong, do not change it — note the concern in the Reasoning and leave the Status alone. Phase 4a is the authority on Status; Phase 4b is the authority on Severity.

## Severity output schema

Write to `<work_dir>/bug-severity.md` with exactly this structure:

```markdown
# Severity Classification — <case>

## Summary

- Total entries: N
- Reproduced bugs: N
- Severity-bearing findings: N
- Critical: N
- High: N
- Medium: N
- Low: N
- No-severity dispositions: N

## Per-entry classification

| Entry | Finding | Status | Severity | Reasoning |
|-------|---------|--------|----------|-----------|
| 1     | MC-1 | REPRODUCED | High | <worst consequence + reachability> |
| 2     | MC-2 | ENV_LIMITED | Critical | <production consequence + named environment limit> |
| 3     | MC-3 | MASKED | Medium | <consequence + named mask> |
| 4     | MC-4 | FALSE POSITIVE | — | <non-severity disposition> |
```

- **Entry** column: integer matching `## Entry N:` headers in `confirmed-bugs.md`. One row per entry, no merging, no skipping.
- **Finding** column: copy the stable finding id from the matching `Finding` table row or `- **Finding ID**:` field.
- **Status** column: copy the entry's `Status` field verbatim, including an RR suffix or defer reason when present. Categorize it by its leading canonical status token.
- **Severity** column: one of `Critical` / `High` / `Medium` / `Low` for `REPRODUCED`, `ENV_LIMITED`, and `MASKED`; exactly `—` for every disposition status.
- **Reasoning** column: for a bug/finding, name the consequence and trigger surface; for a disposition, briefly state why it has no severity. Avoid restating the entry verbatim.

The Summary section at the top is mandatory. `Total entries = Reproduced bugs + Severity-bearing findings + No-severity dispositions`, and `Critical + High + Medium + Low = Reproduced bugs + Severity-bearing findings`.

## Classification boundaries

- **Do not modify `confirmed-bugs.md`.** It is read-only input.
- **Do not add entries** that are not already in `confirmed-bugs.md`. If you notice a bug Phase 4a missed, note it in a separate file or skip it — classifier is not the place to introduce new findings.
- **Do not change `Status`**, even if you disagree. Note the concern in Reasoning if you must.
- **Do not write Phase 4a-style content** (no code audit, no developer-intent investigation, no reproduction scripts). Classification is a fast read-and-judge pass.
- **Do not invent intermediate tiers** (no "High-but-edge-case" or "Critical-only-under-attack"). Pick one of the four tiers; capture the nuance in Reasoning.
- **Do not lower severity because an impact-bearing finding is unreproduced or masked.** See "Severity is independent of reproduction status".

## Edge cases

- **Composition bugs**: a bug whose impact only manifests when combined with another bug. Classify on the combined impact, not on the individual bug's surface. Note the composition in Reasoning.
- **Byzantine-only bugs**: in BFT systems, a bug exploitable only by a Byzantine node within the threat model is still High / Critical depending on impact. Honest-only failure modes typically rank lower.
- **Liveness vs safety**: a liveness violation (deadlock, livelock, starvation) under realistic load is at least High. A safety violation is at least High (often Critical).
- **Documented design vs bug**: if Phase 4a set `FALSE POSITIVE`, use `—`; if Phase 4a kept it `REPRODUCED`, classify on its actual impact and let Reasoning note the disagreement.
- **Entry count mismatch**: if `confirmed-bugs.md` has 8 `## Entry N:` headers, the output table must have 8 rows. Preserve the input identifiers; do not silently repair the Phase 4 report.

## Severity validation checklist

Before finishing, verify:

- One row per `## Entry N:` header in `confirmed-bugs.md` (no missing, no extra).
- Every Severity is one of `Critical` / `High` / `Medium` / `Low` / `—`.
- Every `REPRODUCED`, `ENV_LIMITED`, or `MASKED` row has a four-tier Severity.
- Every `FALSE POSITIVE`, `NEEDS MORE INFO`, `DROPPED`, `PENDING REPAIR`, `DEFERRED`, or `INCOMPLETE` row has Severity `—`.
- Every non-`—` Reasoning names at least one consequence (what goes wrong) and one surface (where it's triggerable from).
- Summary entry classes add up to Total entries, and severity counts add up to reproduced bugs plus severity-bearing findings.
- `confirmed-bugs.md` is unchanged (mtime not bumped, content not edited).

Only after every check above passes, write `.summary-findings.md`.

## Findings summary

The findings fragment gives a reader the final result without repeating the full confirmation report. Base it only on statements explicitly supported by `confirmed-bugs.md`. Do not use `bug-severity.md` as a source for this fragment.

Include every entry whose leading canonical Status is `REPRODUCED`, `MASKED`, or `ENV_LIMITED`. For each entry, provide:

- the stable finding ID;
- the title;
- the canonical Status;
- one sentence describing the practical impact; and
- one short evidence note when the report explicitly states how the result was reproduced, constrained, or masked.

Count all other dispositions together. Do not list or describe those entries individually.

Evidence notes must use plain language. For example, state that a result was exercised through a public API, required controlled timing or component state, could not be exercised because a named dependency was unavailable, or is repaired by a named existing mechanism. Do not use internal reproduction tiers or levels.

### Findings fragment schema

Write `.summary-findings.md` with exactly this section order:

```markdown
<one short paragraph stating the final status counts and the main practical conclusion supported by the report>

## Findings

- **<ID> — <title>** — Status: `<REPRODUCED | MASKED | ENV_LIMITED>`. Impact: <one sentence>. Evidence: <explicit evidence note>.
- Other dispositions: <N>.

## Validation limits

- <important limitation explicitly recorded in confirmed-bugs.md>
```

Omit `Evidence:` from an item when `confirmed-bugs.md` does not support a clear evidence note. When there are no impact-bearing entries, say so under `## Findings` and still report the disposition count. When the input records no finding-specific validation limits, write `No finding-specific validation limits were recorded.` under `## Validation limits`.

The validation-limits section may summarize unavailable dependencies, component-only validation, controlled preconditions or timing, and named masking or recovery behavior already recorded in the input. Do not inspect logs or modeling artifacts to infer additional limitations.

### Findings fragment boundaries

- Do not include Severity labels, severity counts, or severity reasoning.
- Do not include internal reproduction tiers or levels.
- Do not include URLs, Markdown links, source paths, or heading anchors.
- Do not add trigger steps, code locations, repair advice, or new technical analysis.
- Do not choose only the most important findings; include every `REPRODUCED`, `MASKED`, and `ENV_LIMITED` entry.
- Do not soften `MASKED` or `ENV_LIMITED` into `REPRODUCED`; preserve the canonical Status.
- Do not copy detailed report prose when one clear sentence will do.

## Findings summary validation checklist

Before finishing, verify:

- A short paragraph with the final status counts and main practical conclusion appears before `## Findings`.
- `## Findings` appears before `## Validation limits`.
- Every `REPRODUCED`, `MASKED`, and `ENV_LIMITED` input entry appears exactly once with its ID, title, Status, and practical impact.
- Other dispositions appear only as a combined count.
- Every evidence statement and validation limit is explicitly supported by `confirmed-bugs.md`.
- No Severity, internal reproduction level, URL, or Markdown link appears in the fragment.
- `bug-severity.md` remains complete and unchanged after its validation.
- `confirmed-bugs.md` remains unchanged.
