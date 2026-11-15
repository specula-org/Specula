# V03, v2-workload

## Checks never run while an action happens

An action marked *never possible* was never enabled in any state visited by the configs that
enable those checks; *possible* means it was enabled there but not taken within the budget.

| Never checked while | Checks | Names |
|---|---:|---|
| 12 MCTransfer (never possible) | 2 | `RecoveryBacking`, `VoteRecovery` |

Actions no config reached: 3 Receive (some message types) (never possible); 7 Receive (some message types) (never possible); 13 Receive (some message types) (never possible).

No config enables a temporal property, so no progress obligation is checked.

Ignored as requested: `AutoLeaveNotAppended`, `JointNotReached`, `JointRecoveryNotReached`, `LearnerGrantNotReached`, `OutgoingSnapshotRestoreNotReached`, `PostReadyOutputNotReached`.

## Actions

| # | Group | Action |
|---:|---|---|
| 1 | AffectedElectionActions | MCCampaign |
| 2 | AffectedElectionActions | MCTick |
| 3 | AffectedElectionActions | Receive (some message types) |
| 4 | AffectedReadyActions | Ready |
| 5 | AffectedReadyActions | Advance |
| 6 | AffectedRecoveryActions | Restart |
| 7 | AffectedRecoveryActions | Receive (some message types) |
| 8 | AffectedConfigurationActions | MCInvoke |
| 9 | AffectedConfigurationActions | MCInvokeV2 |
| 10 | AffectedConfigurationActions | Propose |
| 11 | AffectedConfigurationActions | ApplyEntry |
| 12 | AffectedProgressActions | MCTransfer |
| 13 | AffectedProgressActions | Receive (some message types) |

## What each config reached

`x` taken, `e` enabled but not taken, `.` never enabled. Retried configs ran a second, longer pass.

| Config | Status | Traces | Seconds | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 |
|---|---|---:|---:|---|---|---|---|---|---|---|---|---|---|---|---|---|
| `MC.cfg` | budget used | 64 | 180.1 | x | x | . | x | x | x | . | x | x | x | x | x | . |
| `MC_hunt_1_durability.cfg` | budget used, retried | 138 | 420.2 | x | x | . | x | x | x | . | x | x | x | x | . | . |
| `MC_hunt_1_parallel.cfg` | budget used, retried | 130 | 420.2 | x | x | . | x | x | x | . | x | x | x | x | . | . |
| `MC_hunt_1_same_batch.cfg` | budget used, retried | 135 | 420.0 | x | x | . | x | x | x | . | x | x | x | x | . | . |
| `MC_hunt_2_election_transfer.cfg` | budget used | 64 | 180.1 | x | x | . | x | x | x | . | x | x | x | x | x | . |
| `MC_hunt_3_configuration_application.cfg` | budget used | 61 | 180.0 | x | x | . | x | x | x | . | x | x | x | x | x | . |
| `MC_hunt_3_node.cfg` | budget used | 86 | 180.1 | x | x | . | x | x | x | . | x | x | . | x | x | . |
| `MC_hunt_4_replication_snapshot.cfg` | budget used | 64 | 180.1 | x | x | . | x | x | x | . | x | x | x | x | x | . |
| `MC_hunt_5_reads.cfg` | budget used | 60 | 180.0 | x | x | . | x | x | x | . | x | x | x | x | x | . |
| `MC_hunt_5_singleton.cfg` | budget used | 377 | 180.1 | x | x | . | x | x | x | . | x | x | x | x | x | . |
| `MC_hunt_6_outcomes.cfg` | budget used | 69 | 180.1 | x | x | . | x | x | x | . | x | x | x | x | x | . |
| `MC_smoke.cfg` | budget used, retried | 7356 | 420.1 | x | . | . | x | x | . | . | . | . | . | x | . | . |
| `Update_focused.cfg` | budget used | 3535 | 180.0 | x | x | . | x | x | x | . | . | x | x | x | . | . |
| `Update_full.cfg` | budget used | 424 | 180.0 | x | x | . | x | x | x | . | x | x | x | x | x | . |
| `Update_hunt_autoleave.cfg` | budget used | 6020 | 180.0 | x | x | . | x | x | . | . | . | x | x | x | . | . |
| `Update_hunt_joint.cfg` | budget used | 5939 | 180.1 | x | x | . | x | x | . | . | . | x | x | x | . | . |
| `Update_hunt_learner_vote.cfg` | budget used | 1263 | 180.1 | x | x | . | x | x | . | . | . | x | x | x | . | . |
| `Update_hunt_outgoing_snapshot.cfg` | budget used | 659 | 180.0 | x | x | . | x | x | . | . | x | x | x | x | . | . |
| `Update_hunt_ready.cfg` | budget used | 1016 | 180.1 | x | x | . | x | x | . | . | x | . | x | x | . | . |
| `Update_hunt_recovery.cfg` | budget used | 5237 | 180.0 | x | x | . | x | x | x | . | . | x | x | x | . | . |
