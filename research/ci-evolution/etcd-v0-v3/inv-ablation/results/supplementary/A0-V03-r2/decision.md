# V03 property-maintenance decision

**Overall: revise.** Keep the reference suite, revise 4 properties (plus 1 alias) whose guarantee changed, add 6 properties (5 checkable, 1 liveness) and 7 reachability canaries. Three suspected implementation defects (D1–D3) must stay visible. Nothing was run in this call: no TLC, no tests, no spec or code edits.

## What changed in the source (behavior only)
| id | change | evidence |
|---|---|---|
| C1 | `advance`: auto-leave fires only when `applied` crosses `pendingConfIndex` (it used to fire whenever `applied >= pendingConfIndex`). The entry has nil `Data` (payload 0), cannot be refused (a refusal panics), and `pendingConfIndex` is set to the new last index. Quota is reduced first. | raft.go:556-593; double_auto.txt:238-279; rawnode_test.go:319-331 |
| C2 | The leader refuses a conf change if one is pending, if the config is joint and the change is not a leave, or if the config is not joint and the change is a leave (`len(Changes)==0`). | raft.go:1036-1079; add_single_explicit.txt:100-123 |
| C3 | Zero-size entries are never dropped by the uncommitted-size quota (`s>0`). | raft.go:1616; raft_test.go:186-190,251-258 |
| C4 | New progress gets `Next = LastIndex` (was `LastIndex+1`). `switchToConfig` probes new replicas immediately even when nothing new commits. | confchange.go:265; raft.go:1556-1567; double_auto.txt:53-62 |
| C5 | A leader transfer is aborted when the transferee leaves both voter halves (so a demotion now aborts it). | raft.go:1568-1571; raft_test.go:3617-3647 |
| C6–C8 | Dead check removed in `Simple`; sort/refactors with identical behavior; follower-only restore Match side effect. | update.patch:36-45,560-732; raft.go:1483 |

## Decisions
**Revised:**
- `AutoLeaveAdvance` → `AutoLeaveAdvance_new`. Uses the crossing trigger, requires exactly one zero-weight leave entry with `pendingConf' = Last`, drops the DropQuota branch, and requires no change when the trigger does not fire. The observer records raw fields instead of computing an `eligible` guard. `UpdateAutoLeaveAdvance` is re-aliased to it.
- `OutcomeSoundness` → `_new` and `ProposalConfigurationDecisions` → `_new`. Both use the joint-state admission rule (`WantsLeave` = V2 with no changes, as the source does), the `s>0` quota exemption, and the `pendingConf` bump. The weight is computed inside the property rather than taken from the draft's `RewriteConf`.
- `ConfigurationTransitionSafety` → `_new`. Its exclusion is narrowed to real bootstrap entries, so leader-generated leave-joint entries (also `id=0`) are now checked at commit.

**Added:**
- `AutoLeaveInitiated`: a leader that has applied an entry of its own term, whose application has caught up with raft's applied index, and that is still in an autoLeave-joint config must have a leave entry pending. This is the `auto_leave` contract in raft.proto:111-113, stated without copying the source's trigger condition.
- `PendingConfCoverage`: every unapplied conf entry in a leader's log is at an index ≤ `pendingConf`. This is what makes the C2 admission check sound, and the old source violated it.
- `ConfChangeApplyClassification`: an applied conf change is a leave exactly when the config at apply time is joint. It checks the C2 admission through the old ApplyEntry consumer.
- `LeaderTransferAbort`: checks C5 in both directions, including the case where `switchToConfig` returns early.
- `NewReplicaProbe`: a newly added replica receives `MsgApp(index=Last-1, [Last])` in the same step. It catches a draft that implements only one of the two coupled C4 changes.
- `AutoLeaveProgress`: liveness form of the `auto_leave` contract; not enabled in the bounded configs.
- Canaries: `JointConfRefusalNotReached`, `EmptyConfRefusalNotReached`, `NonAutoEmptyV2InJointNotReached`, `DemotedTransfereeAbortNotReached`, `NewReplicaProbeNotReached`, `ZeroWeightQuotaBypassNotReached`, `JointAutoLeaveElectionNotReached`.

**Kept, with the justification rechecked:** every other base, MC, Trace and Update property, including all V02 aliases and canaries and `NoUnexpectedFatal`. `NoUnexpectedFatal` is now the downstream detector for apply panics and should be enabled in the V03 Update configs. `CampaignDecisionEligibility` is kept unweakened despite D4. `JointSnapshotMemberAcceptance` is kept as an open V02 candidate because its guard did not change.

**Configs:** drop the old `AutoLeaveAdvance`, `OutcomeSoundness`, `ProposalConfigurationDecisions` and `ConfigurationTransitionSafety` wherever they are enabled and enable the `_new` versions in their place. Enable the new properties in `Update_full`, `Update_focused`, `Trace` and `TraceCorrespondence`. Add hunt configs for the canaries.

## Already covered by existing properties
- **C1 duplicate-leave fix:** `NoUnexpectedFatal` catches a second leave applied to a non-joint config. `AckPreservation` limits each Advance to one leave entry.
- **C1 reorder:** `QuotaIntegrity`.
- **C4 `Next` change:** `ReplicationEvidence` (a probe accepted at `Last-1` must still be backed), `NoUnexpectedFatal` (next stays ≤ Last+1), `QuotaIntegrity` (inflight).
- **C5 follow-up requests:** `TransferDecisionEligibility` ignores a later transfer to the demoted learner.
- **C2 effects:** `RequestCorrelatedConfigurationEffects` (a nil-Data auto-leave still satisfies `IsLeave`), `ConfigurationOrigin`.
- **C7:** the observers are set/bag based and do not depend on order.

## Suspected defects (do not hide with property edits)
- **D1 (liveness):** a leader elected with `applied == lastIndex` while the config is autoLeave-joint never auto-leaves. `becomeLeader` sets `pendingConfIndex = lastIndex`, so `oldApplied < pendingConfIndex` never holds (raft.go:567,752). Detected by `AutoLeaveInitiated` and `AutoLeaveProgress`; reachability shown by `JointAutoLeaveElectionNotReached`.
- **D2 (panic):** a ConfChangeV2 with no changes and `Transition` JointImplicit or JointExplicit is admitted as a leave in a joint config. On apply it is treated as entering joint, which fails with "config is already joint" and panics (raft.go:1055 vs raftpb/confchange.go:83,103-107). Detected by `ConfChangeApplyClassification` and `NoUnexpectedFatal`. This is only visible if the model's admission uses `changes=<<>>`, not `IsLeave`.
- **D3:** if the application calls Advance before ApplyConfChange (README:122 allows Advance any time after persistence), both the auto-leave trigger and admission read a stale config. The result is a missed or duplicate leave, or a stale admission. Detected by `AutoLeaveInitiated`, `ConfChangeApplyClassification` and `NoUnexpectedFatal` under `EarlyAdvance=TRUE`.
- **D4 (predates this patch):** `CampaignContract` counts unapplied V2 entries as pending, but the source's Hup check (`numOfPendingConf`) counts only V1. Auto-leave entries are V2, so this is now easier to reach.
- **Required model changes (M1/M2):** auto-leave weight, trigger, `pendingConf` bump and Fatal on refusal; quota `Weight>0`; `ChangeProgress` `Next=last`; the probe in `ApplyConfCore`; transfer abort based on `VoterIDs`. If these are done wrong, the revised and new properties catch it.

## Unresolved obligations
- Validation must classify every violation of `AutoLeaveInitiated` and `ConfChangeApplyClassification` (and any panic reported by `NoUnexpectedFatal`) against D1–D3.
- Decide whether calling Advance before ApplyConfChange is a legal caller schedule.
- Add the observer fields listed in the JSON before checking.
- Re-measure the encoded size of the nil-Data leave entry for Trace and regenerate traces from the new source.
- Fix config reachability: TransferLimit, Joining or remove-then-re-add, and a weight above MaxUncommitted.
- Run D4 in a separate hunt config so it does not mask the V03 checks.
- Liveness still needs an unbounded driver.
