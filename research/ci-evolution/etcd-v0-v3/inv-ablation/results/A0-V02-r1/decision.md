# Property maintenance decision for this update

**Decision: revise.** Most properties are kept, 4 are revised, 1 stale canary is removed, and 4 properties, 1 liveness target and 6 reachability canaries are added. No TLC runs or tests were executed, and no spec or code was edited.

## Source changes that matter for properties

| # | Change | Evidence |
|---|---|---|
| 1 | **Learners now answer and grant votes.** The learner early-return in the MsgVote case is gone. | `raft.go:924-972` (rationale and etcd#7625 caveat at 933-950); `TestLearnerCannotVote` became `TestLearnerCanVote` (`raft_test.go:383`) |
| 2 | **The full ConfState is restored at construction and on snapshot.** This includes VotersOutgoing, LearnersNext and AutoLeave, rebuilt via `confchange.Restore`. Any mismatch panics. | `raft.go:360-367, 1435-1446`; `confchange/restore.go`; `util.go:137-143`; `restore_test.go:84` |
| 3 | **RawNode `Ready()` now accepts its output immediately.** `Advance` no longer clears messages, read states or the previous soft state. | `rawnode.go:119-177`; `TestRawNodeConsumeReady` (`rawnode_test.go:928`) |
| – | Changes with no property impact: field rename Nodes→Voters / NodesJoint→VotersOutgoing, sorted `Visit`, logger mutex, `majority.go` refactor, `switchToConfig` refactor | patch |

## Revised (`_new`): the guarantee changed, not because the model fails

- **`LearnerEligibility_new`** `== \A x \in history.campaigns : ~x.learner`
  - The grant clause is dropped because the source now intentionally lets learners vote.
  - The campaign clause is still promised: `MsgHup` and `MsgTimeoutNow` are still gated by `promotable()` (`raft.go:899-904, 1318-1327`).
- **`VoteDecisionEligibility_new`** (`VoteContract_new`):
  - `~o.learner` is removed from `grant`, and `(~stale /\ o.learner)` is removed from `silence`.
  - Every other decision is still checked in both directions, so a learner must now respond exactly like a voter.
- **`ReadyOwnership_new`** (and the `UpdateReadyOwnership` alias): every `Ready` (RawNode and Node) clears output and read states and sets the previous soft state; quota is unchanged.
- **`ReadyAccounting`** (observer only): lost reads are now counted as read states that `Advance` removed and that never reached the application. The old formula would wrongly flag read states produced after `Ready`.

## Removed

- **`JointRecoveryNotReached`** (canary in `Update_hunt_recovery.cfg`). It could only be witnessed through the old projection defect, which is now fixed, and its negation is already conjunct 2 of `JointSnapshotRecovery`. It is replaced by `JointRestartRecoveryNotExercised` and `JointSnapshotRestoreNotExercised`.

## Added

| Property | Kind | Predicate (short) | Evidence |
|---|---|---|---|
| `AdvanceRetainsPostReadyOutput` | safety / interaction | at Advance: `outBefore ⊑ outAfter`, read states and previous soft state unchanged | `rawnode.go:170-177`, `TestRawNodeConsumeReady` |
| `RestoreConfStateEquivalence` | safety | restart: `config = expectedConfig`; snapshot install: `config = snap.config` (all ConfStates, not only joint) | `raft.go:367,1446`, `util.go:137`, `confstate.go:25` |
| `LearnerVoteFreshness` | interaction | if a learner's grant is counted toward a win, the winner's config history `Covers` the learner's | the source claim at `raft.go:947-950` |
| `SnapshotRecipientMembership` | interaction (**violation candidate**) | a newer, non-matching snapshot is installed iff the recipient is in `VoterIDs ∪ learners` (outgoing voters included) | `raft.go:1398-1420`, `raft.proto:99-113`, `restore.go` |
| `AutoLeaveProgress` | liveness (unchecked) | `autoLeave ~> outgoing = {}` under stable leader and fairness | `raft.proto:111-113`, `raft.go:556-583` |
| Reachability canaries | structural | `LearnerVoteGrantNotReached`, `LearnerVoteWinNotReached`, `JointRestartRecoveryNotExercised`, `JointSnapshotRestoreNotExercised`, `OutgoingOnlySnapshotNotReached`, `PostReadyOutputNotReached` | prove the properties above are not vacuous |

The new properties need small ghost-observer extensions (exact fields are in the JSON).

## Kept, with rechecked justification

ElectionSafety, LogMatching, LeaderCompleteness, CommittedHistory, AppliedAgreement, VoteRecovery, RecoveryBacking, PromiseBacking, ConfigurationOrigin, ConfigurationTransitionSafety, QuorumAccounting, ReplicationEvidence, SnapshotBacking, AckPreservation, AutoLeaveAdvance, JointConfigurationShape, JointSnapshotRecovery, QuotaIntegrity, OutcomeSoundness, ReadBasis, ReadApplication, ReadCorrelation, NoUnexpectedFatal, TypeOK/MCTypeOK, LogStructure, CampaignDecisionEligibility, TransferDecisionEligibility, RequestCorrelatedConfigurationEffects, ProposalConfigurationDecisions, the 5 liveness targets, TraceMatched, JointNotReached, AutoLeaveNotAppended.

`JointSnapshotRecovery` and `ConfigurationOrigin` used to detect the restore defect; they are now obligations that must hold.

**Updated behaviors already covered by existing properties:**
- **Joint restore:** JointSnapshotRecovery, ConfigurationOrigin and JointConfigurationShape (with SnapshotBacking on the snapshot path).
- **Restored AutoLeave:** AutoLeaveAdvance and AckPreservation.
- **Joint quorums after restore:** QuorumAccounting, ReadBasis, ElectionSafety, LeaderCompleteness and CommittedHistory.
- **Learner votes:** PromiseBacking (a grant must be backed by the persisted vote), VoteRecovery, and QuorumAccounting (a learner's vote counts only where the candidate's config lists it as a voter).
- **New restore panics:** NoUnexpectedFatal.

## Cfg changes

- **Replace** VoteDecisionEligibility with `_new` in base, MC, all 11 MC_hunt and both Trace cfgs.
- **Replace** LearnerEligibility with `_new` in MC_hunt_2 and both Trace cfgs.
- **Re-point** the UpdateReadyOwnership alias to `ReadyOwnership_new`.
- **Re-enable ConfigurationOrigin in TraceCorrespondence.cfg.** It was left out only because of the old joint-recovery violation.
- **Add to `Update_full`:** ConfigurationOrigin, VoteDecisionEligibility_new, LearnerEligibility_new, AdvanceRetainsPostReadyOutput, RestoreConfStateEquivalence, LearnerVoteFreshness and SnapshotRecipientMembership.
- **Add to `Update_focused`:** the first two above, plus AdvanceRetainsPostReadyOutput and RestoreConfStateEquivalence.
- **New hunt cfgs:**
  - `Update_hunt_learner_vote` for the learner-vote canaries.
  - `Update_hunt_outgoing_snapshot` for the outgoing-only snapshot canary.
- **Update_hunt_recovery:** switch to the two replacement canaries.

## Suspected defects: do not hide these by editing properties

- **D1 (implementation, liveness).** `raft.restore` checks membership only against Voters ∪ Learners (`raft.go:1401-1413`). A voter that is only in the outgoing config ignores valid snapshots, even though it counts toward the outgoing majority. Exposed by `SnapshotRecipientMembership` and `CatchupProgress`.
- **D2 (implementation, upstream etcd#7625, made worse by this update).** Learners now vote, so a candidate whose applied config is stale can count a demoted learner. This is reachable because V2 config entries don't block campaigning (`numOfPendingConf`, `raft.go:1605-1611`) and TimeoutNow skips that check. Exposed by `LearnerVoteFreshness`, ElectionSafety, LeaderCompleteness and ConfigurationTransitionSafety. Do not put learner silence back into the contract.
- **D3 (latent, pre-existing).** `Changer.Simple` swallows a `checkInvariants` error (`confchange.go:145-147`) and is now on the restore path. The equivalence panic mitigates it.
- **M1 (model).** The old model still hard-codes the retired behaviors: `RestoreProjection`, the learner guard in `StepVote`, read-only RawNode `Ready`, and acceptance at `Advance`. The violations this causes are model issues and must not lead to property edits.

## Unresolved obligations

1. Implement the observer extensions.
2. Recheck the preserved properties on the updated model.
3. Run the canaries to show the properties are not vacuous.
4. Validate D1 and D2.
5. The liveness targets still need a harness.
6. Decide whether NoUnexpectedFatal can be enabled in the Update cfgs.
7. Trace instrumentation: field rename, RawNode acceptance at `Ready`, learner vote responses, joint restore.
8. The model must represent `Restore` errors for malformed ConfStates as Fatal.
