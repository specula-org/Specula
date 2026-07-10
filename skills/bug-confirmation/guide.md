# Bug Confirmation and Reproduction

Confirm that ONE finding — from model checking or code review — is a real bug, then reproduce it in the actual system. This skill is **single-finding**: it is the methodology for the one finding you are handed. Confirming a whole batch — consolidate the sources, apply this skill to each finding, then aggregate — is a thin loop the pipeline wraps around it (the parallel mode does it in code; the single-agent mode via an orchestration prompt). This file adds no batch logic.

## Flow

The finding goes through two phases in order: investigation (Phase 1) and reproduction (Phase 2). **Phase 1 only gathers evidence** (into `investigation.md`) and makes NO verdict — with one exception, the single pre-filter below. **The verdict is decided after Phase 2**, from the investigation record plus the reproduction result, per the decision table.

**The only pre-filter (a Phase-1 drop): code-review × already-reported.** Drop before Phase 2 **only** if the finding is code-review-sourced **AND an existing issue / PR / CVE / advisory (or a prior Specula dataset entry) has already reported THIS exact defect** — the same mechanism at the same site, **whether still open or already fixed** (open-vs-fixed does not matter — an already-reported bug is not a *new* bug). It is a duplicate of an existing report, not a new find. Mark `Status: DROPPED (code-review × known, cite: <URL/dataset-id>)`, write no `repro/` test. This is about *a report already existing in the tracker*, **NOT** developer awareness: a developer merely suspecting a problem — a `TODO`/`FIXME`/"this might be unsafe"/"we don't handle X yet" comment, a "known limitation" about a *different* aspect, a same-shape precedent on a *different* site, or you spotting the gap yourself — does **NOT** count; finding and confirming an unreported problem is still a real bug. Everything else proceeds to Phase 2 unfiltered: MC-found *with an actual counterexample* (new or known), or any code-review finding not already reported. A model-checking run that returned **no violation** is code-review-sourced (not MC-found); a `Family`/`MC` label alone never exempts a finding.

| # | Phase | When it runs | Output it adds |
|---|-------|---|---|
| 1 | [Investigation](phases/01-investigation.md) | Always | `investigation.md` — evidence only (code audit, reachability, developer knowledge, known-status). No verdict, except a code-review × known drop. |
| 2 | [Reproduction](phases/02-reproduction.md) | Unless dropped (code-review × known) | `repro/test_bug*` + **the verdict** (decided here from the investigation record + reproduction result), or a repair request for a cited artifact |

**Confirmation loop.** When reproduction concludes — with a citation — that a counterexample is a spec / fault-model / invariant **artifact** rather than a real bug, it does not drop the finding. It emits a *repair request* (`PENDING REPAIR`) that hands the finding back to Phase 3 for a scoped repair. Phase 3 repairs the spec and **re-runs model checking**; the pipeline then runs this same confirmation skill on the fresh output — **there is no separate re-check pass**. A repaired artifact simply no longer appears; a surviving or new violation is confirmed from scratch like any finding. The orchestrator caps the loop at a fixed number of rounds and files any still-open repair request under `repair-requests/deferred/` for a developer (the `DEFERRED` disposition is the orchestrator's, never your verdict). See `references/repair-request-format.md`.

## Per-bug output schema

**Confirmation bar.** A finding is a confirmed bug only if it is (1) **reachable** — the triggering state is reached through the real interface or an admissible model-counterexample step, never a fabricated/unreachable pre-condition — and (2) has a **consequence** — a real consumer/caller experiences a wrong outcome. `REPRODUCED` = consequence demonstrated. A real-but-here-untriggerable consequence may be confirmed by a sound argument that production exhibits it (name the env limitation) as `ENV_LIMITED` — never as `REPRODUCED`. When a bar fails, split the "no live harm" cases — do not lump them all into FALSE POSITIVE: (a) **not a defect at all** (documented/intended/nothing-reads/fabricated) → `FALSE POSITIVE`; (b) a **real defect whose consequence is currently masked** by a safeguard / downstream mechanism (sync/loopback/resend/guard) / a discarded output / a *separate* bug → `MASKED` (a *finding*, see below), naming the mask; (c) an **MC counterexample that flags a benign state** the correct code never treats as bad → hand back to repair (`INVARIANT`); and an unreachable-trigger MC finding → repair (`FAULT_MODEL`/`SPEC_REPAIR`) as `PENDING REPAIR`. WIP status and "maybe intended" are never part of this judgment — developer intent counts only as evidence about whether a consequence exists.

**The finding tier.** `REPRODUCED` is a confirmed **bug** (live consequence demonstrated). `ENV_LIMITED` (real defect, argued but untriggerable here) and `MASKED` (real defect, consequence masked today) are **findings** — real anomalies that are not confirmed live bugs but could bite if the mask is removed or the env allows the trigger. Findings are surfaced separately, never discarded as false positives.

**Decision table — settle top-down.** A brief recap of each verdict's bar.

| Verdict | Tier | Settle here when |
|---|---|---|
| `REPRODUCED` | bug | You triggered the live harm through a real interface / an admissible CE step, and a real consumer/caller observes the wrong outcome. |
| `MASKED` | finding | Real defect, but you PROVED a safeguard / downstream mechanism (sync / loopback / resend / guard) / a discarded output / a *separate* bug currently masks the consequence — name the mask. |
| `ENV_LIMITED` | finding | Real defect with a SOUND argument production exhibits it, but this environment cannot trigger it (needs a real cluster / hardware / timing) — name the env limit. |
| `PENDING REPAIR` | MC → repair | (MC only) the counterexample needs a state the code cannot reach, or flags a benign state — a spec / fault-model / invariant artifact. Cite it and emit an RR (`SPEC_REPAIR` / `FAULT_MODEL` / `INVARIANT`). |
| `DROPPED` | pre-filter | Code-review-sourced AND an existing issue / PR / CVE already reported THIS exact defect (decided in Phase 1, before reproduction). Cite it. |
| `FALSE POSITIVE` | not a bug | Not a defect at all — documented / intended, nothing reads the value, or a fabricated / unreachable trigger. |
| `NEEDS MORE INFO` | fallback | You genuinely cannot decide even after investigation + reproduction. The last resort — never a shortcut past a row above. |

Each finding's entry in `confirmed-bugs.md` should include:

- **Source**: `MC` only if model checking produced an actual counterexample (a violation trace) for this finding; otherwise `Code Review`. A finding whose model-checking run returned *no violation* is **not** MC-sourced even if it was checked under a named `Family`/`MC` config — record it as `Code Review` (cite the issue/Family), noting the no-violation result.
- **Novelty**: `NEW` or `KNOWN`. `KNOWN` = a public issue/PR/CVE/advisory **or** a prior Specula dataset entry describes the same mechanism at the same site — the determination the Phase 1 issue-tracker search + precedent re-check (Steps 2–3) already make; just record the outcome here. A `KNOWN` value MUST carry a citation and fix-status: `KNOWN (cite: <URL or dataset-id>; fix-status: unfixed|fixed)`.
- **Status**: REPRODUCED / ENV_LIMITED / MASKED / FALSE POSITIVE / NEEDS MORE INFO / PENDING REPAIR (`DEFERRED` is set by the orchestrator, not you, when the repair loop is exhausted)
- **Repair request**: RR-NNN if this finding was handed back to Phase 3 (omit otherwise)
- **Severity**: Critical / High / Medium / Low
- **Location**: file:line
- **Description**: what the bug is, in 2-3 sentences
- **Trigger scenario**: the concrete sequence of events from Phase 1 Step 1
- **Developer intent investigation**: what Phase 1 Step 2 found (or "no developer commentary found, falling back to engineering principle X")
- **Reproduction test**: path to `repro/test_bug*` + the escalation level reached
- **Reproduction result**: PASS (bug triggered, copy-paste output) / FAIL (escalation exhausted, per-level summary)
- **Recommendation**: suggested fix or mitigation

## Batch Mode Constraints (CRITICAL)

This pipeline runs `claude --print` (non-interactive batch). The harness exits at `end_turn`; any timer/wakeup registered before that is silently dropped along with it. Reproduction tests, build steps, and TLC runs that need waiting must block in the same turn.

- ❌ **Do NOT use `ScheduleWakeup`, `CronCreate`,** or any tool whose semantics is "schedule me to be re-invoked later." The phase will appear to succeed (exit 0) but reproduction will be left half-done.
- ❌ **Do NOT end your turn** while a reproduction test, compile step, or TLC run is unfinished and unobserved.
- ❌ **Do NOT run a reproduction test or build without an outer `timeout`.** Reproduction tests deliberately exercise concurrent / racy code paths — they can and do deadlock. Always wrap: `timeout 5m cargo test ...`, `timeout 10m ./repro.sh`, etc. A fired timeout is a finding (likely the bug you're chasing), not a failure to retry.
- ❌ **Do NOT block on a log marker.** A subprocess killed by SIGTERM (e.g., its own `-t` budget hit, OOM) exits without writing any natural-termination marker, so any wait that watches for a log token can spin forever on a static file. Use a PID-based wait instead.
- ✅ **Block in the same turn**: `Bash` with `wait $PID`, `timeout 30m ...`, or — for any backgrounded long-running job launched via `scripts/infra/start_background.sh` — `scripts/infra/wait_for_pid.sh --pid-file out.log.pid --timeout 1h --log out.log` (blocks on PID, immune to SIGTERM-without-marker).

See `../tla-checking-workflow/guide.md` Phase 2 "Batch Mode Constraints" for full rationale.

## Additional References

For examples beyond the built-in ones, see the [Specula case-studies repository](https://github.com/specula-org/specula-case-studies) which contains 60+ completed case studies across distributed systems, consensus protocols, and concurrent data structures.
