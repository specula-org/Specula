# Invariant maintenance decision: V03 adjacent update

**Overall: MODIFY.** Most of the suite is kept as is. Three properties are modified, four are added (plus canaries), none are removed, and three obligations are unresolved. Nothing was executed (no TLC, no tests); every verdict below is a prediction for the witness phase.

## What changed in the source (semantic)
| # | Change | Evidence |
|---|---|---|
| S1 | **Leader conf-change admission.** While joint, the leader refuses every conf change with non-empty `Changes`. While not joint, it refuses an empty one. | `raft.go:1052-1071`; `testdata/confchange_v2_add_single_explicit.txt:100-106,165-168` |
| S2 | **Quota.** A proposal whose payload size is 0 is never refused (`s>0`). | `raft.go:1616`; `raft_test.go:189,251-258` |
| S3 | **Auto-leave.** The leave entry has nil Data (size 0), and a refusal panics. `pendingConfIndex` is set to the leave's index. The leave is appended only when `applied` crosses `pendingConfIndex`. Together these fix the old duplicate-leave panic. | `raft.go:556-593`; `rawnode_test.go:317-328`; `confchange_v2_add_double_auto.txt:238-279` |
| S4 | **Lead transfer.** It is aborted when the transferee is demoted, not only when it is removed. | `raft.go:1568-1571`; `raft_test.go:3617` |
| S5 | **Probing on conf change.** A conf change applied at the leader that does not advance commit still probes all replicas. | `raft.go:1556-1567`; `confchange_v2_add_double_auto.txt:53-62` |

**Representation-only changes:**
- New `Progress.Next` is `LastIndex` (`confchange.go:265`).
- Snapshot restore now gives self `Match = s.index-1`.
- The auto-leave entry has weight 0 and the nil-Data encoded size.
- `advance()` reduces the quota before appending.
- Campaign fan-out is sorted.

**No-ops:** ReadState `ri`, `maybeTerm`, `IsEmptyHardState`, the `Describe*` functions, raftpb receivers, test infrastructure, and the moved snapshot test.

## Decisions
| Property | Decision | Kind | Why / where it disagrees |
|---|---|---|---|
| ProposalConfigurationDecisions | **modify** | semantic + observer + repair | Adds the S1 joint/leave refusals and `weight>0` for DropQuota. Adds a requirement-level conjunct: an admitted conf entry implies no conf entry in the log that has not yet been applied to the config. The old version copied `pendingConf`. Witnesses: W-P1 (joint refusal), W-P2 (non-joint leave refusal), W-P3 (quota 3 > max 2, then a weight-0 proposal is Accepted), W-P4 (old model admits a proposal while the auto-leave is unapplied). |
| OutcomeSoundness | **modify** | semantic + representation | Adds `o.weight>0` to the quota rule. The weight must come from the joint-aware rewrite, computed independently of the model's `RewriteConf`. Witness: W-P3. |
| AutoLeaveAdvance / UpdateAutoLeaveAdvance | **modify** | semantic + observer + repair | Becomes `appended <=> eligible`, where eligible means: leader, member, autoLeave, cursor>0, `newApplied >= pendingBefore`, and no conf entry beyond the config's application index. If appended, then `pending' = index` and the state is not Fatal. The obsolete (and stale) DropQuota escape is dropped. Witnesses: W-AL0 and W-AL1 (old model: missing pending bump, duplicate leave), W-AL2 (D1), W-AL3 (D2b), W-AL4 (D2a). |
| PendingConfCoversUnapplied | **add** | semantic | For a leader, every conf entry beyond `applied` must be at or below `pendingConf`. The old model violates this after its first auto-leave. |
| AppliedConfJointDiscipline | **add** | repair + semantic | An applied conf entry is a leave **iff** the config before it is joint. Without this, the apply-time panic is checked only by NoUnexpectedFatal, which is disabled in most configs. The old model violates it through the duplicate leave and through non-leave changes applied while joint. The new model violates it only through D3, and through D2 under EarlyAdvance. |
| LeaderTransferTargetVoter | **add** | semantic | A promotable leader's transfer target must be in `VoterIDs`. Witness: demote s3 while `transfer=s3`. The old model keeps the transfer; the new model aborts it. |
| NewReplicaProbedOnConfApply | **add** (progress, not safety) | semantic | When a conf change is applied at the leader, every new peer gets a MsgApp or MsgSnap in the same step. The old model sends nothing to an added s4 when commit does not move. |
| V03 canaries (7) | **add** | observer | Reachability evidence for each witness. |
| AutoLeaveProgress (liveness) | **unresolved** | semantic | Needs an unbounded harness. AutoLeaveAdvance is the bounded stand-in. |
| AckPreservation, QuotaIntegrity, EffectContract, TransferContract, CampaignContract, ConfigurationTransitionSafety, JointConfigurationShape, ConfigurationOrigin, NoUnexpectedFatal | keep | unchanged | Notes in the JSON. EffectContract cannot see invalid transitions. ConfigurationTransitionSafety skips id=0 leave entries. JointConfigurationShape accepts EmptyConfig. CampaignContract has a pre-existing V2-pending-conf mismatch with `numOfPendingConf`. |
| ElectionSafety, LogMatching, LeaderCompleteness, CommittedHistory, AppliedAgreement, TypeOK, LogStructure, recovery/durability, ReplicationEvidence, Ready*, Read*, V02 Update* properties, MC liveness targets, old canaries | keep | safety controls | Must still hold on both models. Any edit to them is a false edit. |

## Updated behaviors already covered by existing properties
- **AckPreservation.** An Advance appends at most one V2 entry with empty changes and emits no output. It does not say when that may happen.
- **EffectContract.** An id=0 entry must be a leave (nil Data unmarshals to an empty ConfChangeV2).
- **QuotaIntegrity.** Covers the weight-0 leave and the reduce-before-append order.
- **CampaignContract.** Compares the set of vote requests, so the sorted fan-out is invisible.
- **TransferContract.** The MsgTransferLeader decision path is unchanged.
- **Old AutoLeaveAdvance.** Its "eligible => append" direction already flags D1 and D2a on the new source, and that direction is kept.

## Suspected defects (must not be hidden)
- **D1 (high, liveness).** The guard `oldApplied < pendingConfIndex` is strict. A leader elected with `applied == lastIndex` never auto-leaves (W-AL2). The cluster then stays joint, and the new admission rule refuses every non-leave conf change.
- **D2 (high if early Advance is legal).** README.md:122 lets the caller Advance before ApplyConfChange. That can (a) skip the auto-leave, (b) append a duplicate leave that panics at apply, or (c) let admission read a stale joint state.
- **D3 (medium, pre-existing).** The admission check uses `len(Changes)==0` rather than `LeaveJoint()`. As a result, `{JointExplicit|Implicit, []}` proposed while joint is admitted and then panics at apply ("config is already joint").
- **D4 (low).** The new probe loop does not skip `r.id`, so a leader whose own Progress was recreated sends MsgApp to itself.
- **D5 (low, pre-existing).** The auto-leave path assumes `Progress[r.id]` exists, so a non-member leader dereferences nil.
- **D6 (doc).** The comment "Configuration changes are never refused" is too broad; only payloads of size 0 are exempt.
- **Model.** The old model reproduces the old bugs. It needs migrations M1–M9 (listed in the JSON). The new properties must not be weakened to fit an unmigrated model.

## Unresolved
- **U1.** Is EarlyAdvance legal with conf entries? Use EarlyAdvance=FALSE as the primary verdict and TRUE as a D2 hunt.
- **U2.** Auto-leave liveness needs a harness.
- **U3.** Should `{Joint*, []}` be refused while joint? If yes, switch ProposalContract's `JointOK` to `IsLeave`.
- **U4.** Measure the nil-Data entry sizes for Trace.
- **U5.** Decide the status of the probe contract (required or hunt-only).
- **U6.** Build the V03 Update lens and hunt configs (V2 workload, EarlyAdvance both ways, weights {0, >max}, Joining s4).
