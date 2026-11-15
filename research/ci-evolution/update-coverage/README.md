# Update coverage check

For #188 §3.3: "verify that checking configurations enable the workloads and properties related to the update." The V0–V3 report found that both etcd bugs were missed partly for this reason: the ordinary configs never issued V2 requests, and the update-focused configs issued them but did not enable `CampaignDecisionEligibility`. Both were found by hand. This prototype finds them automatically.

## What it does

`check.py SPEC_DIR` reads `AffectedActions` from `Update.tla`, which the incremental-modeling skill already requires, and splits it into one probe per action. It then runs every `MC*.cfg` and `Update_*.cfg` in a short TLC simulation with its invariants and properties turned off and an action constraint that records, for each probe, whether it was ever enabled and whether it was ever taken. The constraint never prunes. Configs that leave a gap get a second, longer pass with another seed.

The report starts with the gaps, grouped: each row is a set of actions and the checks that never run in any config that takes them. Each action is marked

- *possible*: it was enabled in those configs but not taken within the budget, so a longer run may close the gap;
- *never possible*: it was never enabled in any state those configs visited, which usually means a limit or workload in the config rules it out.

It then lists affected actions no config reached, and whether any config enables a temporal property. A full matrix of configs against actions follows.

It needs no agent and no changes to the spec. `--actions FILE.tla:DEF` points it at another definition for suites without `Update.tla`.

## Results on etcd V01–V03

`etcd/evaluate.py` runs the check on the final specs in `etcd-v0-v3/agent-runs/inv-evidence/out/revised-spec`, as they are and with `"V2"` added to the workload of every MC config, and nothing else changed. Each config got 180 s at depth 100 with seed 1, and configs with gaps got another 240 s with seed 2. Reachability canaries (`*NotReached`, `*NotAppended`) are left out.

| Version | MC configs issuing V2 requests | Checks with gaps | Gap groups |
|---|---:|---:|---|
| V01 as-is | 0 of 12 | 21 | `MCInvokeV2`; `MCInvokeV2` + `MCCreateSnapshot` |
| V01 with V2 | 11 of 12 | 8 | `MCCreateSnapshot` |
| V02 as-is | 0 of 12 | 22 | `MCInvokeV2` |
| V02 with V2 | 11 of 12 | 0 | |
| V03 as-is | 0 of 12 | 22 | `MCInvokeV2`; `MCInvokeV2` + `MCTransfer` |
| V03 with V2 | 11 of 12 | 2 | `MCTransfer` |

Every action in every gap is *never possible*. `MC_smoke.cfg` has an empty workload and is left as is. Full tables are in `etcd/reports/*/report.md`.

1. **Both gaps from the report are flagged in every version.** No ordinary config ever issues a V2 request, and every check enabled only in ordinary configs, `CampaignDecisionEligibility` included, is never run while one happens. Adding V2 to the workloads clears that.
2. **It finds gaps the report did not mention.** With V2 added, V01 still has 8 checks that never run while a snapshot is created, because they are enabled only in hunts with `SnapshotLimit = 0`. V03 still has `RecoveryBacking` and `VoteRecovery`, which are enabled only in hunts with `TransferLimit = 0`, and leader transfer is part of the V03 update and of bug B. Both were checked against the config files. These are facts about the configs; whether they matter is a modeling call.
3. **No config in any version enables a temporal property**, so a progress bug such as bug B cannot be caught by any configured run.
4. **Fixing the configs is not enough on its own.** No config ever reached `Receive`, and it was never even enabled: random runs from Init never deliver a message, so no leader is elected. Twenty-minute simulations of the corrected V01 configs found nothing (`etcd/after-fix-simulation.md`). This matches `etcd-v0-v3/prefix-ablation/`: the right checks and a recorded starting point are both needed.

## Case study: MongoDB RaftReconfig

To see whether it works on a suite it was not built for, the check ran on `case-studies/systems/mongodb/modules/raftreconfig/runs/case-studies-mongodb-raftreconfig/spec` with `--actions MC.tla:MCNext` (13 configs, 120 s plus a 240 s retry). Results are in `mongodb-raftreconfig/report.md`.

| Never checked while | Checks |
|---|---|
| `MCForceReconfig` (never possible) | `ConfigTermValid`, `ConfigVersionNonNeg`, `LeaderInOwnConfig` |
| `MCRemoveNewlyAdded` (never possible) | `ActiveConfigsOverlap`, `ArbiterQuorumOverlap`, `DrainModeReconfigSafety` |
| `MCShutDown`, `MCRemoveNewlyAdded` (never possible) | `ConfigPropagationSafety` |

Each *never possible* matches a limit of 0 in the configs that enable those checks. The first gap was worth a look: the three checks run only in `MC.cfg`, which has `ForceReconfigLimit = 0`. With the limit set to 1, `LeaderInOwnConfig` fails at state 9: a follower force-reconfigures to a config that leaves the leader out, and the leader adopts it and stays leader (`mongodb-raftreconfig/force-reconfig-check.md`). Either the model is missing a step-down or the invariant is not meant to hold under force reconfig. That is for the case study's authors to decide, but the combination had never been checked.

## Limits

- It relies on `AffectedActions` being complete. It checks the configs against that list, not the list against the code.
- Probes are copied disjuncts. A disjunct such as `\E n: A(n) \/ B(n)` on one line is split into `A` and `B`; anything more complex stays one probe.
- Probes are evaluated on every candidate step, which slows runs: as-is etcd MC configs completed a median of about 8 traces in 180 s, against 70–150 with V2 enabled.
- "Never possible" is still based on sampled runs, not a proof. A limit of 0 confirms it; otherwise it means "never seen enabled".
- It is not wired into CI. It costs a few minutes per config and its output needs a modeling judgment, so for now it is a tool to run on an update.

## Running

```sh
python3 check.py ../etcd-v0-v3/agent-runs/inv-evidence/out/revised-spec/V03 --out /tmp/v03
python3 check.py ../../../case-studies/systems/mongodb/modules/raftreconfig/runs/case-studies-mongodb-raftreconfig/spec --actions MC.tla:MCNext --out /tmp/mongo
python3 etcd/evaluate.py                # all six reports, about an hour with --jobs 5
python3 etcd/evaluate.py --rebuild      # rebuild the reports from the saved report.json files
python3 -m pytest test_check.py
```

`TLA2TOOLS` and `COMMUNITY_MODULES` point to the jars and default to `lib/` in the Specula checkout.
