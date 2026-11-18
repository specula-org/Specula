# Invariant maintenance decision: etcd-raft adjacent update

**Overall: MODIFY.** No tests or TLC were run and no code or spec was changed. All verdicts below are predictions for the validation phase. Full predicates and witnesses are in `decision.json`.

## What the update changes

| Id | Change | Kind |
|---|---|---|
| U-A | Learners now answer MsgVote/MsgPreVote like voters (`raft.go:924-960`; TestLearnerCannotVote → TestLearnerCanVote) | semantic |
| U-B | `newRaft` and `raft.restore` use `confchange.Restore(ConfState)` and then `assertConfStatesEquivalent`. Joint state (outgoing, learnersNext, autoLeave) now survives restart and snapshot restore. | semantic (fix) |
| U-C | `RawNode.Ready()` now accepts the Ready: it clears msgs and readStates and sets prevSoftSt. `Advance()` no longer clears them. The Node wrapper behaves as before. | semantic (API) |
| U-D | `ConfState.Nodes/NodesJoint` renamed to `Voters/VotersOutgoing`. Proto tags and marshal order are the same, so encoded sizes don't change. | representation |
| U-E | `ProgressTracker.Visit` iterates in sorted order | representation (can't be observed with message bags) |
| U-F | Refactors that don't change behaviour: CommittedIndex, EnterJoint braces, logger mutex, NewRawNode ID check (still rejected by `validate`) | none |

## Decisions

**Semantic requirement changes**
- **VoteDecisionEligibility / VoteContract: modify.** Remove `~o.learner` from `grant` and remove `(~stale /\ o.learner)` from `silence`.
  - Witness: a demoted learner s3 receives a fresh MsgVote at term 3 from s1, whose config still lists s3 as a voter.
  - The old contract expects silence; the new one expects a grant and `afterVote = s1`.
  - TestLearnerCanVote's assertion passes for any MsgVoteResp, so this contract is the only real check that the learner grants.
- **LearnerEligibility: modify.** Drop the `grants` conjunct and keep `campaigns`.
  - Learners still must not campaign: `promotable()` is unchanged.
  - The safety reason for the dropped clause is still enforced by QuorumAccounting (`Won` only counts votes from the winner's own voter set) and ElectionSafety.
- **ReadyOwnership / UpdateReadyOwnership: modify.** For RawNode and Node alike, require `outAfter = EmptyBag /\ readsAfter = <<>>` (quota unchanged).
  - Witness: Ready on a RawNode whose outbox is not empty.
- **AdvanceOutboxPreservation: add.** Advance leaves `out` and `readStates` unchanged (TestRawNodeConsumeReady).
  - Witness: a RawNode steps a heartbeat between Ready and Advance. The old model drops the response.

**Representation / observer migrations**
- **ReadyAccounting: keep the predicate, migrate the observer.**
  - New computation: `lostReads += SeqSet(r.readStates) \ (SeqSet(a.readStates) ∪ SeqSet(app.reads))`.
  - With the old observer, the new model would report a read produced after Ready as lost, which is a false positive.
- **ConfState field rename and Visit order: no property edit.** Update comments and trace instrumentation only.

**Repairs of pre-existing property defects**
- **JointSnapshotRecovery → ConfStateRestoreFidelity: strengthen.**
  - `\A x ∈ recovery: x.config = x.expectedConfig`, plus `alive ⇒ config = ConfigOf(cfgHist)` for every config, not just joint ones.
  - This matches the source, which now asserts equivalence on every restore.
  - Witness: a restart drops a learner from a non-joint config. The old property is silent; the new one is violated.
- **JointRecoveryNotReached: role flip.** It used to be a canary showing the old joint-loss bug. It is now expected to hold.
- **JointRestoreNotReached: add a canary.** It shows the joint restore path is actually exercised, so the fidelity checks aren't vacuous.
- **AutoLeaveSingleFlight: add.**
  - Predicate: a leader has at most one unapplied leave-joint entry from its own term.
  - AutoLeaveAdvance can't see duplicate appends because its eligibility uses the implementation's own `pendingConf`.

**New update obligations**
- **SnapshotAdmission: add.** A follower that is in `VoterIDs(s.config) ∪ learners`, receives a non-stale snapshot beyond its commit, and doesn't already match it must install it, ending with `config = s.config`.
- **LearnerGrantNotReached: add a canary.** It should be reached on the new model and never on the old one.

**Kept unchanged**
- The old properties that already cover update behaviour, with how they cover it, are in `covered_updated_behaviors` in the JSON.
- ConfigurationOrigin, TypeOK and JointConfigurationShape cover the joint restore.
- QuorumAccounting, PromiseBacking and VoteRecovery cover learner votes.
- AutoLeaveAdvance covers auto-leave after a restore.
- NoUnexpectedFatal covers the new restore panics.
- CampaignDecisionEligibility covers "learners still don't campaign".
- Safety controls, each with a control witness in the JSON: ElectionSafety, LogMatching, LeaderCompleteness, CommittedHistory, AppliedAgreement, ConfigurationTransitionSafety, AckPreservation, SnapshotBacking, ReplicationEvidence, QuotaIntegrity, RecoveryBacking, the read properties, the decision contracts, LogStructure, the JointNotReached and AutoLeaveNotAppended canaries, and the liveness properties (still unchecked).

## Suspected defects (do not hide them by editing properties)

- **D1, new source (liveness): snapshots refused by outgoing voters.**
  - `raft.restore` only checks `Voters ∪ Learners` (`raft.go:1398-1420`), so a node that is only in VotersOutgoing (including LearnersNext members) ignores snapshots.
  - The leader keeps sending them; if the outgoing majority depends on that node, the joint config can stall.
  - SnapshotAdmission should catch this. **Expected to FAIL on new/source.**
- **D2, pre-existing (reach widened by U-B): duplicate auto-leave.**
  - After an auto-leave append, `pendingConfIndex` is not bumped (`raft.go:563-583`). A later Advance (via pagination or early Advance) appends a second leave, and applying it panics.
  - AutoLeaveSingleFlight should catch this, with NoUnexpectedFatal downstream. **Expected to FAIL.**
- **D3, pre-existing: V2 conf changes don't block campaigning.** `numOfPendingConf` ignores ConfChangeV2, while CampaignContract treats it as pending. The two have never been checked together, because no cfg combines V2 workloads with that invariant.
- **D4, pre-existing: `Changer.Simple` swallows an error.** When `checkInvariants` fails it returns an empty config with a nil error.
- **M1–M3: model changes required by the new source.**
  - M1: remove the learner short-circuit in StepVote.
  - M2: use the full config in Restore/RestartCore and build prs over all members. Keep the source-faithful admission check so D1 stays visible.
  - M3: for RawNodes, accept at Ready instead of Advance.
- **R1, risk:** learner voting relies on candidate configs being close. Any ElectionSafety violation is a defect; ElectionSafety must not be weakened.

## Config recommendations

- The Update cfgs currently check no vote property at all. Add VoteDecisionEligibility, LearnerEligibility, PromiseBacking, ConfigurationOrigin, NoUnexpectedFatal, ReadyAccounting and the new properties to them.
- Add hunt cfgs for LearnerGrantNotReached and JointRestoreNotReached.
- Use a paginating `MaxReadySize` so AutoLeaveSingleFlight can be reached.

## Unresolved

1. The liveness reason for letting learners vote (a promoted learner's vote is decisive) is not checked. An optional canary is given in the JSON.
2. Whether ElectionSafety holds under the corrected learner-voting model is still to be established by running it.
3. SnapshotAdmission and AutoLeaveSingleFlight are expected to fail on new/source. Whether they gate the suite or are tracked as known defects is the suite owner's call; either way they must not be weakened.
4. The trace instrumentation (ConfState field names, RawNode accepting at Ready) can't be verified because `instrumentation-spec.md` is not in the workspace.
5. These caller contracts are assumed, not checked:
   - Restore panics on malformed ConfStates.
   - In AppliedAdapter mode, `InitialState` must return the full ConfState.
6. Optional: also require RawNodes to accept `prevSS` at Ready.
