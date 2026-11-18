# Environment summary for the focused update model

For #188 §3.3: summarize the environment the focused update model leaves out (`EnvUpdate`) and check that the real environment actions stay within it. Specula's incremental skill describes this (`references/generation/modular-verification.md`), but none of the etcd V01–V03 suites wrote one; their `Update.tla` says "no EnvUpdate or discharge claim is made". `envupdate.py` builds one from the suite as it is.

## How it works

The full model (`Update_full.cfg`, usually `MCNext`) is split into single actions, each under its own quantifiers. Each action is compared with the actions in the focused relation (`ConcreteUpdateNext` from `Update_focused.cfg`). If the focused model has the same action written the same way, it is in focus. Otherwise TLC decides step by step.

TLC then simulates the full model and records, for every step outside the focused relation, the action that took it and the state fields it changed. The run can start from `Init` or, with `--trace`, from a recorded run replayed as in `prefix-branch/branch.py`.

The update view is the set of fields read by the `Update*` properties in the suite's `Update_*.cfg` files. `EnvUpdate` keeps every view field that no outside step was seen to change. It is then checked on fresh runs with a new seed, and written to `EnvUpdate.tla` together with `DischargeContext == [][(MCNext /\ ~ConcreteUpdateNext) => EnvUpdate]_vars` so later versions can recheck it.

Actions whose outside steps change view fields are the main output: they need to be in the focused model, or summarized by hand.

## etcd V01–V03

Same suites and 153-event recorded run as `prefix-branch/etcd/`. Each run learned for 600 s and checked for another 600 s. `etcd/evaluate.py` runs all six; the table is `etcd/reports/summary.md`.

| Version | Start | Runs | Actions left out | Out-of-focus steps that change the view | EnvUpdate keeps | Check |
|---|---|---:|---:|---|---:|---|
| V01 | Init | 2009 | 11 | none | 8 of 8 | held on 1947 runs |
| V01 | recorded run | 74 | 11 | none | 8 of 8 | held on 57 runs |
| V02 | Init | 2013 | 11 | MCLose, MCReportUnreachable: `quality.votes` | 22 of 23 | held on 1912 runs |
| V02 | recorded run | 65 | 11 | the same, plus MCTransfer: `raft.elapsed` and ReadIndex: `quality.votes` | 21 of 23 | held on 62 runs |
| V03 | Init | 381 | 9 | MCLose, MCReportUnreachable: `quality.votes` | 22 of 23 | held on 334 runs |
| V03 | recorded run | 46 | 9 | the same, plus ReadIndex: `quality.votes` | 22 of 23 | held on 35 runs |

- **V02 leaves leader transfer out of the focused model, and transfer changes a field the update's properties read.** Only the runs from the recorded run showed this. The V03 model adds transfer to its focused relation, and bug B in V03 needs a leader transfer.
- `quality.votes` is read by `UpdateLearnerVoteContract` and is written by message loss, unreachable reports and read-index requests, none of which are in focus. Whether that matters needs someone who knows the spec.
- V03 puts only some client requests in focus, so some `MCInvoke` steps fall outside it. Because steps are checked one by one, a partial restriction like this shows up.
- Starting from the recorded run gives 20 to 40 times fewer runs but reaches states `Init` does not. In 500 simulated runs from `Init` with `MCNext` as written, no node ever became a candidate. With `MCNext` split into single actions, TLC's random choice changes enough that messages are sent and received.

### All 11 recordings of the V02 CI run

`etcd/full_traces.py` learns from each of Qian's 11 V02 recordings (300 s to learn, 300 s to check), replayed and with domains set as in `prefix-branch/etcd/full_traces.py`. Results are in `etcd/reports/full-traces/`.

- Leader transfer changes `raft.elapsed` in 9 of the 11 recordings, so the V02 finding above does not depend on one run.
- Over all recordings, the actions outside focus that change the view are the same four as above: message loss, unreachable reports and read-index requests (`quality.votes`), and transfer (`raft.elapsed`, `quality.votes`).
- On two recordings the check on fresh runs failed, because the summary learned from that recording alone (5 and 17 runs) missed one of these changes. Learning from all recordings together covers them.

## Other specs

The split of the next-state relation was checked on the 10 blind-study V0 suites Qian shared (OpenRaft, ZooKeeper, CometBFT and others). For each suite TLC checked, for 75 s each way, that every step of the original relation is a step of the split one and the reverse. `blind/split_check.py` runs it; results are in `blind/split-check.json`.

- All 10 hold in both directions (12 to 27 actions per suite).
- As a control, the first action is dropped from the split; TLC catches the missing action on 8 of the 10. On the other two the dropped action did not fire within 75 s.
- The suites found two parser bugs, both fixed: `[][Next]_<<a, b>>` with a tuple was not recognised (cases 002, 004), and a guard written as `/\ Guard /\ \/ A \/ B` was split away from its actions (case 006). It is now distributed: `(Guard /\ A) \/ (Guard /\ B)`.

The suites have no `Update.tla`, so the update-specific part of the tool could not be run on them.

## Limits

- The summary is learned from simulation, so it holds only for the behaviour seen. Six actions never fired in any run, including the 11 recordings: `ApplySnapshot` and the five whose limit is 0 in `Update_full.cfg` (`MCAvailability` twice, `MCCancel`, `MCDuplicate`, `MCQuiesce`). There is no evidence about them.
- `EnvUpdate` is only a frame: it says which fields stay unchanged, not how changed fields may change. It is enough for the discharge check, not for an open model check that replaces the omitted actions.
- The view is found by text. Fields of per-node records are matched by name, so the view can include more than the properties read.
- Two actions count as the same only if they are written the same way after expanding one-line wrappers such as `Framed`. Anything else is decided by TLC, which is slower but exact.

## Running

```sh
python3 envupdate.py SPEC_DIR --out /tmp/env-update
python3 envupdate.py SPEC_DIR --trace TRACE.ndjson --replay "MatchEvent(logline)" --out /tmp/env-update
python3 etcd/evaluate.py
python3 etcd/full_traces.py --traces DIR
python3 blind/split_check.py DIR_WITH_CASES
python3 -m pytest test_envupdate.py
```
