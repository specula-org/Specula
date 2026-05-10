# Bug Confirmation and Reproduction

Confirm MC-found bugs are real, classify their reportability, and reproduce the new ones.

## Flow

Each finding goes through three phases in order. Phase 1 is investigation — five internal steps ordered cheap-first, with explicit guidance to bias toward continuing rather than rejecting when uncertain. Phases 2 and 3 are heavier and only add information for the right kind of finding.

| # | Phase | When it runs | Output it adds |
|---|-------|---|---|
| 1 | [Investigation](phases/01-investigation.md) | Every finding | Triage outcome + reachability + trigger scenario + dev-intent summary + `Prerequisites:` block + precedent re-check |
| 2 | [Counterfactual Fix Check](phases/02-counterfactual-check.md) | **Only** findings whose violated property is system-wide (availability, exhaustion, eventual consistency, replay-immunity, etc.) | `Counterfactual fix check:` block; possibly framing change |
| 3 | [Reproduction](phases/03-reproduction.md) | **Mandatory** for every new bug; not required for known/historical | `repro/test_bug*` file + REPRODUCED/FAILED status |

After all applicable phases have run for a finding, classify it into a Report Tier (see below). Tier is assigned **at the end**, with all evidence in hand — Phase 1 prerequisite check may have downgraded or invalidated the finding, Phase 2 may have reframed it from security to hygiene, Phase 3's REPRODUCED / FAILED outcome affects reportability. Assigning tier upfront is "judgment before evidence" and produces wrong calls.

## Report Tier

After Phases 1-3 have produced their evidence for a finding, assign one Report Tier based on the worst-case observable consequence given everything you now know:

- **Tier A — primary submission.** Externally observable, hard-to-recover harm: data corruption, crash/hang/deadlock, signature or transcript verification failure on legitimate input, integrity violation under realistic attacker model, key/credential loss, MITM-exploitable gap, memory-safety bug.
- **Tier B — selective submission.** Real but bounded: information leak only under attacker access (not amplification-style), recovery requires session/connection teardown, fail-soft path that degrades availability without compromising correctness, hygiene gap whose absence is documented in spec / nearby code.
- **Tier C — record only, not submitted by default.** No externally observable consequence beyond noise: wasted CPU cycles, one extra round trip, "looks like an anti-pattern but downstream gate catches before any state escapes," consequence indistinguishable from compliant behavior, finding whose framing was downgraded by Phase 1 Step 4 (spec contradicts prerequisite) or Phase 2 (counterfactual showed alternative paths at comparable cost).

Tier C findings are recorded in `confirmed-bugs.md` but excluded from the maintainer-facing submission by default. The downstream report-generation step decides which tiers to include for each audience.

## Per-bug output schema

Each finding's entry in `confirmed-bugs.md` should include, in addition to the existing fields (Source, Status, Severity, Location, Description, Trigger scenario, Developer intent investigation, Reproduction test, Reproduction result, Recommendation), the following fields produced by the new phases:

- `Prerequisites:` block (from Phase 1 Step 4)
- `Counterfactual fix check:` block, when applicable (from Phase 2)
- `Report Tier: A | B | C` (assigned at the end based on evidence from all applicable phases)

If launcher prompts or older templates say "every confirmed bug needs reproduction," read that as **every new confirmed bug**. Known/historical bugs remain exempt when they cite accepted upstream evidence (JIRA, CVE, maintainer-accepted issue, or equivalent).

## Batch Mode Constraints (CRITICAL)

This pipeline runs `claude --print` (non-interactive batch). The harness exits at `end_turn`; any timer/wakeup registered before that is silently dropped along with it. Reproduction tests, build steps, and TLC runs (Phase 2 and Phase 3) that need waiting must block in the same turn.

- ❌ **Do NOT use `ScheduleWakeup`, `CronCreate`,** or any tool whose semantics is "schedule me to be re-invoked later." The phase will appear to succeed (exit 0) but reproduction will be left half-done.
- ❌ **Do NOT end your turn** while a reproduction test, compile step, or TLC run is unfinished and unobserved.
- ❌ **Do NOT run a reproduction test or build without an outer `timeout`.** Reproduction tests deliberately exercise concurrent / racy code paths — they can and do deadlock. Always wrap: `timeout 5m cargo test ...`, `timeout 10m ./repro.sh`, etc. A fired timeout is a finding (likely the bug you're chasing), not a failure to retry.
- ❌ **Do NOT use unbounded polling loops (`until grep ... ; sleep ; done`) waiting on a subprocess marker.** If the subprocess was killed by SIGTERM (e.g., its own `-t` budget hit), the natural-termination marker never appears and the polling spins forever on a static file. Outer `timeout` ≥ inner subprocess budget + grace. Real incident: 2 hours lost on arc-swap because polling watched for TLC's `Finished in` while TLC had been killed by its own `-t`.
- ✅ **Block in the same turn**: `Bash` with `wait $PID`, `timeout 30m ...`, or a single bounded poll loop wrapped in an outer `timeout`.

See `../tla-checking-workflow/guide.md` Phase 2 "Batch Mode Constraints" for full rationale.

## Additional References

For examples beyond the built-in ones, see the [Specula case-studies repository](https://github.com/specula-org/specula-case-studies) which contains 60+ completed case studies across distributed systems, consensus protocols, and concurrent data structures.
