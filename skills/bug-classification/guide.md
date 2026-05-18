# Bug Classification

Assign a Severity tier to each bug in `confirmed-bugs.md` (produced by Phase 4a / `bug-confirmation`). Single responsibility: classify by external impact. **Do nothing else.**

## Scope

- **Input**: `<work_dir>/spec/confirmed-bugs.md` — every entry already has Status (REPRODUCED / REPRODUCTION FAILED / FALSE POSITIVE / NEEDS MORE INFO), Trigger scenario, Developer intent, Reproduction evidence.
- **Output**: `<work_dir>/spec/bug-severity.md` — a single table with one row per bug.
- **You do not**: write new bug analysis, change reproduction status, reject bugs, re-do investigation, or modify `confirmed-bugs.md`.

If a bug's `Status` is FALSE POSITIVE, it still gets a row in the output (with severity reasoning explaining why the FP determination is sound). FP entries are typically not assigned a Severity tier (use `—`) because there is no bug to be severe; but the row records the classifier's agreement with the FP call.

## Severity rubric

Severity is a property of **what the bug does to the system**, not of how easy it was to reproduce. A bug whose Status is REPRODUCTION FAILED can still be Critical if its code-audit evidence implies severe impact when triggered.

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
- A **REPRODUCTION FAILED Critical** bug → still primary submission with the audit evidence and the failed-reproduction record as honest disclosure (the maintainer can decide whether to invest in a deterministic repro). Do NOT downgrade severity because reproduction was hard.
- A **REPRODUCTION FAILED Medium** bug → record, lower submission priority.
- A **FALSE POSITIVE** bug → no severity (Severity = `—`), Reasoning briefly notes why the FP call appears sound.

## Classification process

For each bug in `confirmed-bugs.md`:

1. Read the bug's Description, Trigger scenario, Developer intent investigation, Reproduction result, and Recommendation fields.
2. Identify the **worst observable consequence** the bug enables under realistic conditions. "Realistic" means: code path is reachable from the system's public interface, faults assumed are within the system's stated fault model, attacker capability (if Byzantine) is within the model's threat model.
3. Match to the rubric. Lean toward the higher tier when the line between two tiers is unclear.
4. Write a 1–2 sentence Reasoning that names the consequence and the conditions under which it appears.

Do not re-do Phase 4a's investigation. If you find that Phase 4a's Status is wrong, do not change it — note the concern in the Reasoning and leave the Status alone. Phase 4a is the authority on Status; Phase 4b is the authority on Severity.

## Output schema

Write to `<work_dir>/spec/bug-severity.md` with exactly this structure:

```markdown
# Severity Classification — <case>

## Summary

- Total bugs: N
- Critical: N
- High: N
- Medium: N
- Low: N
- FALSE POSITIVE (no severity): N

## Per-bug classification

| Bug | Title | Status | Severity | Reasoning |
|-----|-------|--------|----------|-----------|
| 1   | <title from confirmed-bugs.md ## Bug 1: header>           | REPRODUCED         | High     | <1-2 sentences naming worst consequence + reachability> |
| 2   | <title from ## Bug 2>                                     | REPRODUCTION FAILED | Critical | <consequence + why FAILED doesn't lower severity> |
| 3   | <title from ## Bug 3>                                     | FALSE POSITIVE     | —        | <1 sentence acknowledging the FP call is sound> |
```

- **Bug** column: integer matching `## Bug N:` headers in `confirmed-bugs.md`. One row per bug, no merging, no skipping.
- **Title** column: copy the title from the `## Bug N:` header verbatim. Truncate to ~60 chars if needed; preserve enough to identify the bug.
- **Status** column: copy from confirmed-bugs.md's `Status` field. Verbatim — REPRODUCED / REPRODUCTION FAILED / FALSE POSITIVE / NEEDS MORE INFO.
- **Severity** column: one of `Critical` / `High` / `Medium` / `Low` / `—`. Use `—` only for FALSE POSITIVE.
- **Reasoning** column: 1–2 sentences. Name the consequence (what goes wrong) and the trigger surface (what makes it reachable). Avoid restating the bug description verbatim; the reasoning should add the severity-justifying argument.

The Summary section at the top is mandatory — it lets downstream readers see the distribution at a glance.

## What NOT to do

- **Do not modify `confirmed-bugs.md`.** It is read-only input.
- **Do not add bugs** that are not already in `confirmed-bugs.md`. If you notice a bug Phase 4a missed, note it in a separate file or skip it — classifier is not the place to introduce new findings.
- **Do not change `Status`**, even if you disagree. Note the concern in Reasoning if you must.
- **Do not write Phase 4a-style content** (no code audit, no developer-intent investigation, no reproduction scripts). Classification is a fast read-and-judge pass.
- **Do not invent intermediate tiers** (no "High-but-edge-case" or "Critical-only-under-attack"). Pick one of the four tiers; capture the nuance in Reasoning.
- **Do not lower severity because reproduction failed.** See "Severity is independent of reproduction status".

## Edge cases

- **Composition bugs**: a bug whose impact only manifests when combined with another bug. Classify on the combined impact, not on the individual bug's surface. Note the composition in Reasoning.
- **Byzantine-only bugs**: in BFT systems, a bug exploitable only by a Byzantine node within the threat model is still High / Critical depending on impact. Honest-only failure modes typically rank lower.
- **Liveness vs safety**: a liveness violation (deadlock, livelock, starvation) under realistic load is at least High. A safety violation is at least High (often Critical).
- **Documented design vs bug**: if Phase 4a's developer-intent investigation says "maintainer accepts this as design", the entry is usually FALSE POSITIVE — but if Phase 4a kept it REPRODUCED, classify on its actual impact and let Reasoning note the disagreement.
- **Bug count mismatch**: if `confirmed-bugs.md` has 8 bug headers, the output table must have 8 rows. Number gaps in confirmed-bugs.md (e.g., Bug 1, 2, 4 — no Bug 3) should be preserved verbatim, not renumbered.

## Output validation checklist

Before finishing, verify:

- One row per `## Bug N:` header in `confirmed-bugs.md` (no missing, no extra).
- Every Severity is one of `Critical` / `High` / `Medium` / `Low` / `—`.
- Every `—` row has Status = FALSE POSITIVE.
- Every non-`—` Reasoning names at least one consequence (what goes wrong) and one surface (where it's triggerable from).
- Summary counts add up to Total.
- `confirmed-bugs.md` is unchanged (mtime not bumped, content not edited).
