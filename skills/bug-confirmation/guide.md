# Bug Confirmation and Reproduction

Confirm bugs found by model checking or code review are real, then reproduce them in the actual system.

## Flow

Each finding goes through two phases in order: investigation (Phase 1) and reproduction (Phase 2). Both phases run for every finding, with one exception: if Phase 1 establishes the finding is **code-review-sourced AND already-known** (a public issue/PR/CVE/advisory — **whether still open or already fixed** — describes the same mechanism at the same site), drop the finding before Phase 2 — mark its entry `Status: DROPPED (code-review × known, cite: <URL>)` and do not write a `repro/` test. **Open-vs-fixed does not matter: an open, unfixed issue still counts as already-known. A code-review reproduction of any already-reported bug is not a new bug (it is already in the tracker), so it is dropped regardless of fix status** — do not keep it on the grounds that the bug is still live. This is the only pre-filter; MC-found bugs (new or known) and code-review-found *new* bugs all proceed to Phase 2 as usual.

| # | Phase | When it runs | Output it adds |
|---|-------|---|---|
| 1 | [Investigation](phases/01-investigation.md) | Every finding | Code-audit result + dev-intent summary + precedent re-check |
| 2 | [Reproduction](phases/02-reproduction.md) | Every finding except dropped (code-review × known) | `repro/test_bug*` file + REPRODUCED / REPRODUCTION FAILED status; or, for a **cited** artifact verdict, a repair request |
| 2′ | [Re-check](phases/03-recheck.md) | `--recheck` only (pipeline repair loop) | resolves `RECHECK` repair requests; transitions each to RESOLVED / REOPENED / DEFERRED |

**Confirmation loop.** When reproduction concludes — with a citation — that a counterexample is a spec / fault-model / invariant **artifact** rather than a real bug, it does not drop the finding. It emits a *repair request* that hands the finding back to Phase 3 for a scoped repair; the pipeline then re-runs this skill in `--recheck` mode (Phase 2′) to settle it. See `references/repair-request-format.md`. The loop is bounded by the run's token budget and by per-request anti-oscillation, not by a fixed iteration cap.

## Per-bug output schema

Each finding's entry in `confirmed-bugs.md` should include:

- **Source**: MC (with counterexample) or Code Review
- **Status**: REPRODUCED / REPRODUCTION FAILED / FALSE POSITIVE / NEEDS MORE INFO / PENDING REPAIR / DEFERRED
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
