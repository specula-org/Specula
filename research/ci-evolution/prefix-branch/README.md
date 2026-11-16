# Branching from recorded runs

For #188 §3.3, starting from validated trace prefixes instead of `Init`. Qian's bug A probe (`etcd-v0-v3/experiments/campaign-prefix/V01`) did this by hand for one trace and one action. `branch.py` does it for any suite with a `Trace.tla` and an `Update.tla`.

## How it works

Each simulated run replays the recorded trace up to a random step, takes one of the update's `AffectedActions` there, and then lets the system settle: the parts of `ReactiveActions` take turns, so persisting, sending and delivering keep moving. Every invariant the suite enables in any config is checked after the branch. The branch can also come after the recording ends, while the system settles.

Limits come from `Update_full.cfg`, the recorded system's settings from `Trace.cfg`. Replay is strict by default (`TraceNext`); `--replay MatchEvent(logline)` replays inputs only, for traces recorded on another model revision.

Input ranges such as request IDs and weights are picked automatically: a smaller range from the limits config is kept only if the trace replays to exactly the same final state with it.

## Bug A on etcd V01–V03

The only recorded run in this branch is the first 153 events of the run Qian's probe used (`progress-probe-V03/out/joint-autoleave-prefix-inputs.ndjson`), replayed by inputs. `etcd/evaluate.py` runs each version for 600 s three ways: rotating settle (`rotate`), the same with V01's RawNode rule as a branch guard (`rotate-rawnode`), and the spec's own next-state relation at random (`random`).

| Version | Continuation | Result | Seconds | Runs |
|---|---|---|---:|---:|
| V01 | random | nothing | 600 | 103 |
| V01 | rotate | bug A | 434 | 75 |
| V01 | rotate-rawnode | nothing (also nothing in 1800 s) | 600 | 120 |
| V01 | rotate-rawnode, only `CampaignDecisionEligibility` | bug A | 143 | 429 |
| V02 | random | nothing | 600 | 104 |
| V02 | rotate | bug A | 9 | 3 |
| V02 | rotate-rawnode | bug A | 41 | 10 |
| V03 | random | nothing | 600 | 125 |
| V03 | rotate | bug A | 12 | 3 |
| V03 | rotate-rawnode | bug A | 53 | 10 |

Bug A here is a follower with the V2 configuration entry committed but not applied campaigning while the leader is alive. No other invariant fired (36 checks on V01, 43 on V02 and V03). Without the guard the follower still has an outstanding Ready, which the model allows but V01's API does not; with it, the counterexample matches Qian's witness. On V01 the guarded run needs about 400 runs, and with all 36 checks on each run is about 15 times slower, so it does not get there in 30 minutes.

From the same 153 events, random continuation finds nothing. From `Init`, 20-minute runs of the corrected V01 configs found nothing either (`update-coverage/etcd/after-fix-simulation.md`).

With automatic ranges instead of the three set by hand, V02 picks the two weight ranges, keeps the trace's request IDs, and still finds bug A in 36 s.

The table was produced before two later changes: automatic ranges, and letting a run keep settling after a branch inside the recording (before, such runs stopped at the branch). All the counterexamples above branched after the recording, so they are unaffected.

## Bug B (progress)

`--settled PRED --after N` checks a condition after N settle steps. With "no node still has `autoLeave` set" (under a "no node fatal or down" premise), 150 steps, and no state constraint, both V03 and V02 fail it, so it does not separate the buggy version from the fixed one. On V02 the branch injects a second V2 change mid-transition and the leader stops with "invalid configuration transition", after which nothing can progress. Bug B still needs a scenario-specific property like Qian's.

## Limits

- One partial recording. The full traces from Qian's CI run would allow branching inside the recording, as his probe did.
- Strict replay is covered only by unit tests.
- The RawNode guard and a usable progress condition still need someone who knows the spec.
- Rerunning Specula's CI on etcd here to get our own traces was tried and stopped: code analysis alone used a 5-hour Claude quota in 23 minutes.

## Running

```sh
python3 branch.py SPEC_DIR TRACE.ndjson --out /tmp/branch
python3 etcd/evaluate.py
python3 -m pytest test_branch.py
```
