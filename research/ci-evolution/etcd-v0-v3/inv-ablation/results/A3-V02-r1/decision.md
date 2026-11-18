# Invariant maintenance for the etcd-raft "joint ConfState restore / learners vote / Ready consumes" update

**Overall: modify.** The old suite needs these changes:
- 4 property changes: VoteDecisionEligibility, LearnerEligibility, ReadyOwnership, and the observer behind ReadyAccounting.
- 2 additions: AdvanceRetention and SnapshotMemberRestore.
- 1 canary retarget: JointRecoveryNotReached.
- Model edits so the model follows the new code (listed at the end).

The joint-restore fix itself is already expressed by kept properties: JointSnapshotRecovery and ConfigurationOrigin. Every semantic edit and every kept property touched by the update was checked by TLC on concrete old and new transitions, and the matching Go behavior was observed in copies of both trees. Records are in `out/evidence.json`; artefacts are in `evidence/`.

## What the update changes (and what it does not)

| Update aspect | Requirement evidence | Effect on suite |
|---|---|---|
| Learners now answer MsgVote/MsgPreVote like voters | `raft.go:933-950`, `raft_test.go:381-397` | semantic change: VoteContract, LearnerEligibility |
| `RawNode.Ready()` now consumes msgs/readStates; `Advance()` no longer clears them | `rawnode.go:119-127`, `rawnode_test.go:928-960` | semantic change: ReadyOwnership; observer migration: lostReads; new AdvanceRetention |
| `newRaft`/`restore` rebuild the full ConfState (VotersOutgoing, LearnersNext, AutoLeave) via `confchange.Restore` | `confchange/restore.go:111-119`, `restore_test.go:84-142`, `raft.proto:99-114` | kept JointSnapshotRecovery/ConfigurationOrigin; model `RestoreProjection` = identity; canary retargeted |
| Renames (Nodes→Voters, NodesJoint→VotersOutgoing), `switchToConfig`, `node` holds `RawNode`, logger mutex, sorted `Visit`, `uint64Slice` removal | — | no property change (Visit ordering is not representable with bag outboxes) |

## Final decisions

| Property | Decision | Kind | Evidence | Key executed result (old → proposed) |
|---|---|---|---|---|
| VoteDecisionEligibility | modify | semantic | E1 E2 E3 | learner grant: FALSE→TRUE; old learner silence: TRUE→FALSE; forged stale-log learner grant: FALSE→FALSE |
| LearnerEligibility | modify (drop grants conjunct) | semantic | E4 E5 E15 | learner grant: FALSE→TRUE; forged learner campaign: FALSE→FALSE |
| ReadyOwnership | modify (raw = Node: Ready accepts) | semantic | E6a E6b E7 | new RawNode Ready: FALSE→TRUE; old read-only Ready: TRUE→FALSE; Node wrapper not accepting: FALSE→FALSE |
| ReadyAccounting | modify observer (`LostReadsAtAdvance`) | observer | E8 | new Advance retaining R2: old observer FALSE (false loss) → TRUE; old Advance dropping R2: FALSE→FALSE |
| AdvanceRetention | **add** | strengthening | E9 E18 | new Advance keeps m2: TRUE; old Advance drops it: FALSE. The old suite stays TRUE in the messages-only variant |
| JointSnapshotRecovery, ConfigurationOrigin | keep | semantic | E10 E11 | new full restore TRUE; old projection FALSE (restart and MsgSnap) |
| JointConfigurationShape | keep | — | E10 | TRUE on restored configs (it is not the detector of the projection) |
| SnapshotMemberRestore | **add** | strengthening | E12 E13 | outgoing-only member ignores a joint snapshot: FALSE (**bug candidate**); incoming voter restores: TRUE; non-member ignores: TRUE; old projection: FALSE |
| QuorumAccounting, ElectionSafety, LeaderCompleteness | keep | — | E15 E19 | raft.go:936-947 learner-vote election executed end to end: TRUE; forged learner-counted win and forged double win: FALSE |
| PromiseBacking | keep | control | E16 | learner grant published after its HardState was persisted: TRUE; unbacked grant: FALSE |
| CampaignDecisionEligibility | keep | — | E17 | campaign after joint restart sends to {2,3}: TRUE |
| AutoLeaveAdvance, AckPreservation | keep | — | E18 | restart into joint auto-leave config, then elected, commits and Advances: leave-joint appended, eligible check recorded, TRUE |
| JointRecoveryNotReached (canary) | modify | representation | E14 | joint restart/MsgSnap recovery: old canary TRUE (misses it); revised canary FALSE (finds the witness) |
| All other properties | keep | unchanged | E10 E19 | TRUE on all executed states; E19 is a low-coverage regression check |

## Changes between the initial and final decisions

1. **JointRecoveryNotReached canary (revised).** My initial canary looked only at `history.recovery`. TLC showed it stays TRUE after a joint MsgSnap restore (`new_snap2` L2), so it missed the snapshot path. The final version also fires on `raft[n].usnap.config.outgoing # {}`. (E14; the initial text is evaluated verbatim in `EvalJoint.tla` as `initialProposalCanary`.)
2. **AdvanceRetention outbox conjunct tightened** from bag inclusion to equality. The requirement test (`rawnode_test.go:957-959`) asserts `raft.msgs == [m2]` after Advance. Verdicts are unchanged: new TRUE, old FALSE.
3. **Clarifications, no decision changes:**
   - JointConfigurationShape and CampaignDecisionEligibility are TRUE on the old projected states too. The detectors of the projection are JointSnapshotRecovery and ConfigurationOrigin.
   - The migrated lostReads observer cannot fire under the proposed model. It remains a regression detector: it fires on the old Advance.

All other decisions match `decision.initial.json`.

## Bug candidates (impl produces it / requirement forbids it)

**D1 — a member of only the outgoing half ignores a joint snapshot.**
- **Code:** `raft.restore()` decides membership by scanning only `cs.Voters` and `cs.Learners` (`new/source/raft.go:1401-1420`).
- **What happens:** a follower that is only in `VotersOutgoing` (an outright removal, or a demotion through `LearnersNext`) drops the snapshot and replies `MsgAppResp index=commit`.
- **Observed:**
  - Go `TestEvOutgoingMemberSnap`, both cases: committed=0, config unchanged.
  - TLC `new_snap3` and `new_snap3_removal`: SnapshotMemberRestore FALSE, while every old property stays TRUE.
- **Why it is forbidden:** the restore code's own comment says to throw away a snapshot only "if recipient is not in the config" (`raft.go:1398-1400`). `raft_test.go:2789-2796` says a member that cannot accept a snapshot "is permanently cut off from the Raft log". `raft.proto:105-110` defines VotersOutgoing as voters of the configuration.
- **Decision:** SnapshotMemberRestore is added and kept strong; it is **not** weakened to exclude outgoing-only members.
- **History:** the defect predates the update. The old check scanned Nodes/Learners and gave the same Go result. It only matters now that joint ConfStates are restored.

No other witness fell in the impl-produces/forbidden cell. Every place the new code violates an old property (learner grants, RawNode Ready clearing, Advance retaining R2) has non-implementation requirement evidence that it is allowed.

## Other suspected defects

- **D2 (test weakness).** In `TestLearnerCanVote`, the check `msg.Type != pb.MsgVoteResp && !msg.Reject` (`raft_test.go:394`) cannot fail for a rejecting MsgVoteResp. Only the exactly-one-message check (`:390-392`) and the `raft.go:933-950` comment carry the requirement.
- **D3 (old observer).** The old lostReads observer (`base.tla:1102-1103`) reports a loss the new code does not commit (E8). It has been migrated.

## Unresolved

- **ElectionSafety with learner votes and stale candidate configs** (`raft.go:948-950`, etcd issue 7625). There is no violation in the directed witnesses. The time-boxed random simulation of the proposed model (E19: about 30M states, no violation) **never reached** a learner grant, a joint config, a joint recovery or an outgoing-member snapshot, according to its coverage canaries. So it is only a no-false-positive check on ordinary election, Ready and Advance paths, not evidence for the update-specific edits. An exhaustive bounded check of the joint and learner scenarios remains open (the BFS attempt reached depth 4 only).
- **Message order from the sorted `Visit`** is not representable, because outboxes are bags.
- **Trace instrumentation** (not supplied) must rename the ConfState fields it maps. The TLA+ field names are unaffected.
- **ReadyOwnership quota conjunct:** no requirement text was found. It is carried over unchanged (E7(b)).
- **PromiseBacking implementation axis:** publication order is a caller-side obligation and was not executed (E16).

## Model edits that accompany the property changes (`evidence/Proposed.tla`, diff in `evidence/logs/Proposed.diff`)

- **Restore and RestartCore:** `RestoreProjection(cfg) == cfg`, with prs built over `VoterIDs(cfg) \cup cfg.learners`. The membership guard is kept faithful to the code (voters ∪ learners).
- **StepVote:** the learner early return is removed.
- **ProtocolReady:** RawNodes now accept the Ready like the Node wrapper does.
- **AdvanceCore:** out, readStates and prevSS are no longer cleared for RawNodes.
- **New observers:** `RestoreObservation` (quality.restores), `AdvanceAck` (acks), `LostReadsAtAdvance`.
