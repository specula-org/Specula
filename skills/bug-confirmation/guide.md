# Bug Confirmation and Reproduction

Confirm bugs found by model checking or code review are real, then reproduce them in the actual system.

## Flow

Each finding goes through two phases in order: investigation (Phase 1) and reproduction (Phase 3). Both phases run for every finding — no pre-filtering.

| # | Phase | When it runs | Output it adds |
|---|-------|---|---|
| 1 | [Investigation](phases/01-investigation.md) | Every finding | Code-audit result + dev-intent summary + precedent re-check |
| 3 | [Reproduction](phases/03-reproduction.md) | Every finding | `repro/test_bug*` file + REPRODUCED / REPRODUCTION FAILED status |

## Per-bug output schema

Each finding's entry in `confirmed-bugs.md` should include:

- **Source**: MC (with counterexample) or Code Review
- **Status**: REPRODUCED / REPRODUCTION FAILED / FALSE POSITIVE / NEEDS MORE INFO
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
- ❌ **Do NOT use unbounded polling loops (`until grep ... ; sleep ; done`) waiting on a subprocess marker.** If the subprocess was killed by SIGTERM (e.g., its own `-t` budget hit), the natural-termination marker never appears and the polling spins forever on a static file. Real incident: 2h lost on arc-swap doing exactly this.
- ✅ **Block in the same turn**: `Bash` with `wait $PID`, `timeout 30m ...`, or — for background TLC launched via `scripts/infra/start_background.sh` — `scripts/infra/wait_for_tlc.sh --pid-file out.log.pid --timeout 1h --log out.log` (blocks on PID, immune to SIGTERM-without-marker).

See `../tla-checking-workflow/guide.md` Phase 2 "Batch Mode Constraints" for full rationale.

## Additional References

For examples beyond the built-in ones, see the [Specula case-studies repository](https://github.com/specula-org/specula-case-studies) which contains 60+ completed case studies across distributed systems, consensus protocols, and concurrent data structures.
