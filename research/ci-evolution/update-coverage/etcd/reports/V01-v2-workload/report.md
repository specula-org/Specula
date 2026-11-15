# V01, v2-workload

## Checks never run while an action happens

An action marked *never possible* was never enabled in any state visited by the configs that
enable those checks; *possible* means it was enabled there but not taken within the budget.

| Never checked while | Checks | Names |
|---|---:|---|
| 10 MCCreateSnapshot (never possible) | 8 | `ConfigurationOrigin`, `ConfigurationTransitionSafety`, `LearnerEligibility`, `OutcomeSoundness`, `ReadApplication`, `ReadBasis`, `ReadCorrelation`, `ReadyAccounting` |

Actions no config reached: 6 Receive (never possible).

No config enables a temporal property, so no progress obligation is checked.

Ignored as requested: `AutoLeaveNotAppended`, `JointNotReached`, `JointRecoveryNotReached`.

## Actions

| # | Group | Action |
|---:|---|---|
| 1 | AffectedConfigurationActions | MCInvokeV2 |
| 2 | AffectedConfigurationActions | Propose |
| 3 | AffectedConfigurationActions | ApplyEntry |
| 4 | AffectedQuorumAndAdvanceActions | MCCampaign |
| 5 | AffectedQuorumAndAdvanceActions | MCTick |
| 6 | AffectedQuorumAndAdvanceActions | Receive |
| 7 | AffectedQuorumAndAdvanceActions | Ready |
| 8 | AffectedQuorumAndAdvanceActions | Advance |
| 9 | AffectedRecoveryActions | Restart |
| 10 | AffectedRecoveryActions | MCCreateSnapshot |

## What each config reached

`x` taken, `e` enabled but not taken, `.` never enabled. Retried configs ran a second, longer pass.

| Config | Status | Traces | Seconds | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
|---|---|---:|---:|---|---|---|---|---|---|---|---|---|---|
| `MC.cfg` | budget used | 61 | 180.0 | x | x | x | x | x | . | x | x | x | x |
| `MC_hunt_1_durability.cfg` | budget used | 56 | 180.0 | x | x | x | x | x | . | x | x | x | x |
| `MC_hunt_1_parallel.cfg` | budget used | 56 | 180.0 | x | x | x | x | x | . | x | x | x | x |
| `MC_hunt_1_same_batch.cfg` | budget used | 55 | 180.0 | x | x | x | x | x | . | x | x | x | x |
| `MC_hunt_2_election_transfer.cfg` | budget used, retried | 152 | 420.0 | x | x | x | x | x | . | x | x | x | . |
| `MC_hunt_3_configuration_application.cfg` | budget used, retried | 151 | 420.0 | x | x | x | x | x | . | x | x | x | . |
| `MC_hunt_3_node.cfg` | budget used, retried | 203 | 420.0 | x | . | x | x | x | . | x | x | x | . |
| `MC_hunt_4_replication_snapshot.cfg` | budget used | 66 | 180.0 | x | x | x | x | x | . | x | x | x | x |
| `MC_hunt_5_reads.cfg` | budget used, retried | 149 | 420.0 | x | x | x | x | x | . | x | x | x | . |
| `MC_hunt_5_singleton.cfg` | budget used, retried | 804 | 420.0 | x | x | x | x | x | . | x | x | x | . |
| `MC_hunt_6_outcomes.cfg` | budget used, retried | 226 | 420.0 | x | x | x | x | x | . | x | x | x | . |
| `MC_smoke.cfg` | budget used, retried | 9693 | 420.0 | . | . | x | x | . | . | x | x | . | . |
| `Update_focused.cfg` | budget used | 4031 | 180.0 | x | x | x | x | x | . | x | x | x | x |
| `Update_full.cfg` | budget used | 467 | 180.0 | x | x | x | x | x | . | x | x | x | x |
| `Update_hunt_autoleave.cfg` | budget used | 7041 | 180.0 | x | x | x | x | x | . | x | x | . | . |
| `Update_hunt_joint.cfg` | budget used | 10579 | 180.0 | x | x | x | x | x | . | x | x | . | . |
| `Update_hunt_recovery.cfg` | budget used | 10324 | 180.0 | x | x | x | x | x | . | x | x | x | x |
