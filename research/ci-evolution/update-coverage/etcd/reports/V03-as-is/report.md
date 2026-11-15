# V03, as-is

## Checks never run while an action happens

An action marked *never possible* was never enabled in any state visited by the configs that
enable those checks; *possible* means it was enabled there but not taken within the budget.

| Never checked while | Checks | Names |
|---|---:|---|
| 9 MCInvokeV2 (never possible) | 20 | `AckPreservation`, `CampaignDecisionEligibility`, `ConfigurationOrigin`, `ConfigurationTransitionSafety`, `LearnerEligibility`, `NoUnexpectedFatal`, `OutcomeSoundness`, `PromiseBacking`, `ProposalConfigurationDecisions`, `QuorumAccounting`, `QuotaIntegrity`, `ReadApplication`, `ReadBasis`, `ReadCorrelation`, `ReadyAccounting`, `ReplicationEvidence`, `RequestCorrelatedConfigurationEffects`, `SnapshotBacking`, `TransferDecisionEligibility`, `VoteDecisionEligibility` |
| 9 MCInvokeV2 (never possible); 12 MCTransfer (never possible) | 2 | `RecoveryBacking`, `VoteRecovery` |

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
| `MC.cfg` | budget used, retried | 8 | 420.0 | x | x | . | x | x | x | . | x | . | x | x | x | . |
| `MC_hunt_1_durability.cfg` | budget used, retried | 8 | 420.0 | x | x | . | x | x | x | . | x | . | x | x | . | . |
| `MC_hunt_1_parallel.cfg` | budget used, retried | 6 | 420.1 | x | x | . | x | x | x | . | x | . | x | x | . | . |
| `MC_hunt_1_same_batch.cfg` | budget used, retried | 7 | 420.2 | x | x | . | x | x | x | . | x | . | x | x | . | . |
| `MC_hunt_2_election_transfer.cfg` | budget used, retried | 8 | 420.1 | x | x | . | x | x | x | . | x | . | x | x | x | . |
| `MC_hunt_3_configuration_application.cfg` | budget used, retried | 7 | 420.1 | x | x | . | x | x | x | . | x | . | x | x | x | . |
| `MC_hunt_3_node.cfg` | budget used, retried | 20 | 420.1 | x | x | . | x | x | x | . | x | . | . | x | x | . |
| `MC_hunt_4_replication_snapshot.cfg` | budget used, retried | 9 | 420.1 | x | x | . | x | x | x | . | x | . | x | x | x | . |
| `MC_hunt_5_reads.cfg` | budget used, retried | 7 | 420.0 | x | x | . | x | x | x | . | x | . | x | x | x | . |
| `MC_hunt_5_singleton.cfg` | budget used, retried | 64 | 420.0 | x | x | . | x | x | x | . | x | . | x | x | x | . |
| `MC_hunt_6_outcomes.cfg` | budget used, retried | 10 | 420.0 | x | x | . | x | x | x | . | x | . | x | x | x | . |
| `MC_smoke.cfg` | budget used, retried | 8503 | 420.1 | x | . | . | x | x | . | . | . | . | . | x | . | . |
| `Update_focused.cfg` | budget used | 3998 | 180.0 | x | x | . | x | x | x | . | . | x | x | x | . | . |
| `Update_full.cfg` | budget used | 452 | 180.0 | x | x | . | x | x | x | . | x | x | x | x | x | . |
| `Update_hunt_autoleave.cfg` | budget used | 6621 | 180.0 | x | x | . | x | x | . | . | . | x | x | x | . | . |
| `Update_hunt_joint.cfg` | budget used | 6681 | 180.0 | x | x | . | x | x | . | . | . | x | x | x | . | . |
| `Update_hunt_learner_vote.cfg` | budget used | 1445 | 180.0 | x | x | . | x | x | . | . | . | x | x | x | . | . |
| `Update_hunt_outgoing_snapshot.cfg` | budget used | 589 | 180.0 | x | x | . | x | x | . | . | x | x | x | x | . | . |
| `Update_hunt_ready.cfg` | budget used | 1010 | 180.0 | x | x | . | x | x | . | . | x | . | x | x | . | . |
| `Update_hunt_recovery.cfg` | budget used | 5210 | 180.1 | x | x | . | x | x | x | . | . | x | x | x | . | . |
