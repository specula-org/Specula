# Branching from recorded runs

For #188 §3.3, starting from validated trace prefixes instead of `Init`. Qian's bug A probe (`etcd-v0-v3/experiments/campaign-prefix/V01`) did this by hand for one trace and one action. `branch.py` does it for any suite with a `Trace.tla` and an `Update.tla`.

## How it works

Each simulated run replays the recorded trace up to a random step, takes one of the update's `AffectedActions` there, and then lets the system settle: the parts of `ReactiveActions` take turns, so persisting, sending and delivering keep moving. Every invariant the suite enables in any config is checked after the branch, except those already false right before it. The branch can also come after the recording ends, while the system settles.

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

## All 11 recordings of the V02 CI run

Qian shared all 11 traces from the V02 incremental CI run (run `20260915-173143-1152`), including the full 415-event `joint-autoleave`. They are not in this branch; `etcd/full_traces.py --traces DIR` runs them. Each run had 300 s, replayed by inputs. Two changes were needed:

- **Domains.** The traces declare request ids 1–32 and weights 0–256, so a branch step had millions of successors and a run did 1 simulation in 10 minutes. `--domain NAME=VALUE` now sets a domain by hand; the script uses the values the run itself uses (entries inside messages included) plus those in `Update_full.cfg`. The replay still has to reach the end.
- **Other versions.** V01 and V03 cannot replay every V02 recording to the end. `--prefix auto` finds the longest prefix that replays (by bisection) and branches from there. V03 replays 205 of `joint-autoleave`'s 414 events.

Strict replay of the full `joint-autoleave`, with every post-state checked, also passes on V02 (23 s).

Bug A, checking only `CampaignDecisionEligibility` (`reports/full-traces/bug-a/summary.md`):

| Recording | V01 | V02 | V03 |
|---|---:|---:|---:|
| joint-autoleave | 20 s | 26 s | 10 s |
| joint-explicit | 21 s | 27 s | 89 s |
| joint-snapshot-recovery | 15 s | 55 s | 55 s |
| outgoing-snapshot-restore | 8 s | 9 s | 168 s |
| the other 7 | nothing | nothing | nothing |

- The four that find it are the runs that go through a joint configuration change. Every counterexample branches at step 193–416 with one `Campaign`, inside or right after the recording, so the recordings themselves reach bug A's precondition.
- On V01 this takes 8–21 s. From the 153-event prefix it took 434 s, and with the RawNode guard it was not found in 30 minutes.

### All checks

Every invariant in the suite is checked (`reports/full-traces/fixed/`). Checks already false in the recording are not counted, `Maintenance.tla` is loaded so a `Revised` check replaces the original, and `--guard` only injects V2 requests that leave a well-formed configuration. Each alarm is rerun on the previous version (`full_traces.py triage`), and labels follow Qian's review (`etcd/qian-verdicts.json`). Times are summed over the 11 runs; branching makes no model calls.

| Version | Checks | Wall s | TLC CPU s | Alarms | Real, from the update | Real, older | Noise | Not reviewed |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| V01 | all | 3621 | 3598 | 4 | 2 | 1 | 1 | 0 |
| V02 | all | 3104 | 3052 | 4 | 0 | 3 | 1 | 0 |
| V03 | all | 3106 | 3415 | 4 | 0 | 1 | 1 | 2 |
| V01 | without the 4 noisy | 3938 | 3787 | 3 | 2 | 0 | 0 | 1 |
| V02 | without the 4 noisy | 3399 | 3253 | 4 | 0 | 3 | 0 | 1 |
| V03 | without the 4 noisy | 3106 | 3416 | 4 | 0 | 1 | 0 | 3 |

- Bug A comes from the V01 update and is found on V01, V02 and V03.
- An empty ConfChangeV2 outside a joint config is committed and every node panics. It is found on V01 and V02 from node-lifecycle and ready-intervening-output, not on V03. This is a raft bug already fixed upstream.
- `PromiseBacking` fails on all three versions from same-batch-replay. It is an old model gap from V00.
- `ConfigurationOrigin` is already false in V01's joint-snapshot-recovery recording.
- Removing the only voter, which raft also rejects, is no longer injected.
- Without the four noisy invariants (`reports/full-traces/fixed-without-noisy/`), V02 finds bug A on two more recordings.

Not reviewed yet:

- V03: `RevisedProposalConfigurationDecisions` on node-lifecycle, ready-intervening-output and same-batch-replay.
- V03 node-lifecycle: the app calls `Advance` before `ApplyConfChange` after an auto-leave, the leader proposes a second leave, and applying it is fatal.
- `RevisedConfigurationTransitionSafety` on V01 and `ReadBasis` on V01 and V02, both on node-lifecycle.

### Choosing branch points

`choose.py` replays each recording and records, at every step, which affected actions are enabled and which one the recording took. Enabled but not taken is an alternative the recording never tried. Points are ranked by how rare their untried alternatives are across all recordings, and `--points` makes `branch.py` branch only there.

It does not beat branching everywhere. With the top 10 points per recording, bug A is found from 4 of the 4 recordings on V01, 0 of 4 on V02 and 2 of 4 on V03 (`reports/full-traces/bug-a/*-chosen`). Bug A needs a `Campaign`, and `Campaign` is possible at almost every step, so rarity ranks its point low. The data is still useful as trace coverage: across all 11 recordings on V02, `Campaign` is taken at 15 of 5766 steps where it is possible, and `InvokeV2` at 5 of 5658.

A breadth-first sweep over every recorded state was also tried and dropped: it reached 1.08 million states in 15 minutes without finishing.

## Bug B (progress)

`--settled PRED --after N` checks a condition after N settle steps. With "no node still has `autoLeave` set" (under a "no node fatal or down" premise), 150 steps, and no state constraint, both V03 and V02 fail it, so it does not separate the buggy version from the fixed one. On V02 the branch injects a second V2 change mid-transition and the leader stops with "invalid configuration transition", after which nothing can progress. Bug B still needs a scenario-specific property like Qian's.

## Limits

- The full-trace domains are chosen from parameter names (`id`, `weight`, `encoded`), which is specific to this suite.
- Recordings are made on V02 only, so V01 and V03 branch from a prefix of some of them.
- There is no full V00 suite, so V01 alarms are not compared with a previous version.
- The RawNode guard and a usable progress condition still need someone who knows the spec.
- Rerunning Specula's CI on etcd here to get our own traces was tried and stopped: code analysis alone used a 5-hour Claude quota in 23 minutes.

## Running

```sh
python3 branch.py SPEC_DIR TRACE.ndjson --out /tmp/branch
python3 etcd/evaluate.py
python3 etcd/full_traces.py all --traces DIR --checks CampaignDecisionEligibility --label bug-a
python3 etcd/full_traces.py all --traces DIR --guard --label fixed
python3 etcd/full_traces.py triage --traces DIR --label fixed
python3 etcd/full_traces.py verdicts --traces DIR --label verdicts
python3 etcd/full_traces.py table
python3 choose.py SPEC_DIR TRACE.ndjson... --out /tmp/choose
python3 -m pytest test_branch.py test_choose.py etcd/test_full_traces.py
```
