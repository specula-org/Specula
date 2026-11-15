# V02, v2-workload

## Checks never run while an action happens

None: every enabled check runs in a config that reaches every action some config reaches.

Actions no config reached: 3 Receive (some message types) (never possible); 7 Receive (some message types) (never possible).

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
| 8 | AffectedConfigurationActions | MCInvokeV2 |
| 9 | AffectedConfigurationActions | Propose |
| 10 | AffectedConfigurationActions | ApplyEntry |

## What each config reached

`x` taken, `e` enabled but not taken, `.` never enabled. Retried configs ran a second, longer pass.

| Config | Status | Traces | Seconds | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
|---|---|---:|---:|---|---|---|---|---|---|---|---|---|---|
| `MC.cfg` | budget used | 74 | 180.0 | x | x | . | x | x | x | . | x | x | x |
| `MC_hunt_1_durability.cfg` | budget used | 67 | 180.0 | x | x | . | x | x | x | . | x | x | x |
| `MC_hunt_1_parallel.cfg` | budget used | 68 | 180.0 | x | x | . | x | x | x | . | x | x | x |
| `MC_hunt_1_same_batch.cfg` | budget used | 67 | 180.0 | x | x | . | x | x | x | . | x | x | x |
| `MC_hunt_2_election_transfer.cfg` | budget used | 72 | 180.0 | x | x | . | x | x | x | . | x | x | x |
| `MC_hunt_3_configuration_application.cfg` | budget used | 63 | 180.1 | x | x | . | x | x | x | . | x | x | x |
| `MC_hunt_3_node.cfg` | budget used | 82 | 180.0 | x | x | . | x | x | x | . | x | . | x |
| `MC_hunt_4_replication_snapshot.cfg` | budget used | 68 | 180.1 | x | x | . | x | x | x | . | x | x | x |
| `MC_hunt_5_reads.cfg` | budget used | 63 | 180.0 | x | x | . | x | x | x | . | x | x | x |
| `MC_hunt_5_singleton.cfg` | budget used | 326 | 180.0 | x | x | . | x | x | x | . | x | x | x |
| `MC_hunt_6_outcomes.cfg` | budget used | 64 | 180.0 | x | x | . | x | x | x | . | x | x | x |
| `MC_smoke.cfg` | budget used | 2974 | 180.0 | x | . | . | x | x | . | . | . | . | x |
| `Update_focused.cfg` | budget used | 3865 | 180.0 | x | x | . | x | x | x | . | x | x | x |
| `Update_full.cfg` | budget used | 413 | 180.0 | x | x | . | x | x | x | . | x | x | x |
| `Update_hunt_autoleave.cfg` | budget used | 7589 | 180.0 | x | x | . | x | x | . | . | x | x | x |
| `Update_hunt_joint.cfg` | budget used | 7289 | 180.0 | x | x | . | x | x | . | . | x | x | x |
| `Update_hunt_learner_vote.cfg` | budget used | 1580 | 180.0 | x | x | . | x | x | . | . | x | x | x |
| `Update_hunt_outgoing_snapshot.cfg` | budget used | 633 | 180.0 | x | x | . | x | x | . | . | x | x | x |
| `Update_hunt_ready.cfg` | budget used | 921 | 180.0 | x | x | . | x | x | . | . | . | x | x |
| `Update_hunt_recovery.cfg` | budget used | 6324 | 180.0 | x | x | . | x | x | x | . | x | x | x |
