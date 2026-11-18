# Invariant maintenance: etcd-raft V00 → joint consensus / ConfChangeV2 update

**Overall decision: modify.** Most of the old suite stays as it is. The update adds joint configurations (incoming/outgoing voters, LearnersNext, AutoLeave), Changer-based `applyConfChange`, raft-generated auto-leave entries inside `Advance`, and the RawNode/Node Ready/Advance refactor. Because of this, several properties need **observer/helper migrations**, a few need **semantic edits**, and two **new obligations** are added. Three **implementation defects** were reproduced in the new code. The proposed properties keep rejecting them.

Artifacts: `evidence/tla/Proposed.tla` (base.tla with all edits; diff in `evidence/logs/base_to_Proposed.diff`), `evidence/tla/Compare.tla` (59 old-vs-proposed TLC evaluations), `evidence/tla/HelperCheck.tla` (22 helper checks), `evidence/go/{old,new}/zz_evidence_test.go` (Go observations G1–G13), and `out/evidence.json` (60 records). In every record, the claimed truth value matches the TLC value.

## Shared representation migration (needed by most edits)
- Config record: `[voters = Voters[0] (incoming), outgoing = Voters[1], learners, learnersNext, autoLeave]`.
- New helpers: `AllVoters`, `IsJoint`, `JointWon` (both halves; an empty half wins), `Members` includes outgoing voters, and `ConfKinds` includes `"V2"`.
- `ConfigAfter`/`ConfigOf` now mirror `confchange.Changer`. They are validated by TLC against all 22 expected outputs from the confchange testdata, `TestRawNodeProposeAndConfChange`, and Go G3/G5/G6/G10–G12 (OBS-CONFIGAFTER).
- Without these migrations, the old property text still parses, but its meaning changes: it checks only the incoming majority or ignores V2 entries. Examples: E-ORIG-2, E-QA-2, E-CAMP-OUT-1.

## Semantic edits (each executed with TLC + Go)
| Property | Decision | Key evidence (old → new) |
|---|---|---|
| RequestCorrelatedConfigurationEffects | modify | Demotion is now required, backed by `TestAddLearner` "Demote r." and `simple_promote_demote.txt` (E-EFF-DEMOTE-1: F→T; the old no-op now gives T→F). A raft-generated auto-leave (id 0) is a legitimate origin only on a joint autoLeave config, per raft.proto:85,111 (E-EFF-AUTO-1: F→T). Controls: a second auto-leave on a non-joint config and an id-0 leave of an explicit joint config are both still rejected. |
| AckPreservation_LogUnchanged | modify (relax impl-abstraction clause) | Advance may append exactly one zero ConfChangeV2 at a due leader (G1, `rawnode_test.go:343`). E-ACK-1: F→T. Seven controls (lost entry, Normal append, non-leader, no autoLeave, cursor<pending, prefix changed) remain F. |
| AutoLeaveOnePending | **add** | The one-pending-conf rule (node.go:137, raft.go:280, README:195) also binds raft-generated entries. E-ONE-1a shows the relaxation **alone** accepts the observed double auto-leave, so this property is required. E-ONE-1: new F on G2 step 3; legitimate single auto-leaves are T. |
| ConfigurationTransitionOverlap | **add** | Any applied transition must be either a simple change with ≤1 voter changed and a non-empty voter set, or an enter/leave-joint step (confchange.go:129, simple_safety.txt, TestRemoveNode, raft.proto joint doc). Unsafe swap → F; legitimate enter/leave/demote → T; remove-last-voter: old T → new F. |
| QuorumAccounting | modify (joint quorum) | Under both old projections, a commit or win backed by one half only gives old T → new F (E-QA-1/2/3). The code does not commit in that situation (G5). The legitimate joint commit is T/T. The `voters#{}` clause stays **unknown** and unchanged. |
| ConfigurationTransitionSafety | modify | Compares the joint config. The bootstrap exemption is narrowed from `id=0` to `IsBootstrapEntry`, because auto-leave entries also have id 0. The second auto-leave committed under the joint config gives old T → new F (E-CTS-1). A commit by a leader that lost its outgoing half also gives T → F (E-CTS-2). |
| CampaignDecisionEligibility | modify (representation) | Voters = both halves; singleton = joint self-win; pending includes V2. A campaign by an outgoing-only voter gives F→T under the incoming projection (G6). A committed but unapplied V2 entry with the node campaigning gives old T → **new F**: this is the new code's behaviour (G4) and a suspected defect. The requirement clause is not weakened. |
| TypeOK | modify (representation of the tracker.go:36 requirement clause) | Disjointness now covers both voter halves; learnersNext ⊆ outgoing. Not executed. |

## Kept, with helper/observer migration only
ConfigurationOrigin (unchanged text; it flags the restore defect, E-ORIG-1), ProposalConfigurationDecisions (V2 rewrite, E-PROP-1 F→T), TransferDecisionEligibility (outgoing-only target admitted, G13, E-TRANSFER-1 F→T), ReadBasis (JointWon), ReplicationEvidence and SnapshotBacking (joint Members/ConfigOf), OutcomeSoundness (ConfKinds), and LeaderCompleteness (the DurableObligations gate now uses JointWon). ReadBasis, ReplicationEvidence, SnapshotBacking and the DurableObligations change were **not executed** because they are representation-only.

## Kept unchanged (re-examined where the watch list was touched)
ElectionSafety, LogMatching, CommittedHistory, AppliedAgreement, VoteRecovery, RecoveryBacking, PromiseBacking, LearnerEligibility, VoteDecisionEligibility, AckPreservation_SnapshotRetained (*unknown*; the update does not conflict with it), AckPreservation_AppliedCursor, AckPreservation, ReadyAccounting (new environment rule: no Step between Ready and Advance), QuotaIntegrity (the quota reduction moved to Advance; that is a model change only), ReadApplication, ReadCorrelation, NoUnexpectedFatal, and LogStructure*.

Controls: ElectionSafety and AppliedCursor give identical verdicts under the old and new definitions. VoteRecovery is unchanged, yet the **old** code violated it (G8old: term 5 → 1 on an empty-log RawNode) and the new code satisfies it (G8new).

## Suspected implementation defects (reproduced in the new code; not hidden by any edit)
1. **`numOfPendingConf` ignores EntryConfChangeV2.** A node with a committed but unapplied V2 change campaigns (G4). This violates the pending-conf requirement.
2. **Auto-leave does not bump `pendingConfIndex` on success.** With commit pagination, a second auto-leave is appended while the first is still unapplied, and applying it panics with "can't leave a non-joint config" (G2). This violates AutoLeaveOnePending, ConfigurationTransitionSafety, EffectContract and NoUnexpectedFatal.
3. **`restore`/`newRaft` drop NodesJoint/LearnersNext/AutoLeave.** A node restored or restarted in a joint config loses its outgoing majority, and a later LeaveJoint panics (G7).
4. (Not executed) `confchange.Simple` swallows a checkInvariants error and returns an empty config with a nil error. This is probably unreachable.

## Changes between the initial and final decisions
- **ConfigurationTransitionOverlap.** The decision is unchanged. The expression was refined to `b.voters#{} ⇒ a.voters#{}` so that learner-only changes on an empty bootstrap config are not misreported. Those are validity errors, already covered by NoUnexpectedFatal. I also corrected the initial witness claim: the old EffectContract *does* reject the unsafe swap, but it rejects the legitimate enter-joint too, so it does not express the obligation. TLC showed that the revised EffectContract also rejects the swap. The overlap property is therefore partly redundant; I kept it as a check that does not depend on the `ConfigAfter` helper.
- **CampaignDecisionEligibility.** The decision is unchanged. Evidence showed the difference for outgoing-only voters depends on which old projection is used (under the VoterNodes union, old and new agree). The V2-pending difference and the stronger recipient check do not depend on the projection.
- **LeaderCompleteness.** Kept, but the DurableObligations observer was actually migrated to JointWon. It was not executed.
- All other initial decisions were confirmed by the executed evidence.

## Unresolved
- NoUnexpectedFatal clauses for the new Changer panics on user-proposed invalid V2 changes (enter-joint while joint, removing the last voter) remain **unknown**. The only evidence is `TODO(tbg): return the error to the caller`.
- The `voters#{}` clause in QuorumAccounting remains unknown.
- Liveness ("Raft will automatically transition … when this is safe") is not covered by any safety property.
- The full migrated model in Proposed.tla was only parsed and used for definition evaluation. It was **not** model-checked end to end, because the MC wrapper (MC.tla) is not among the inputs.
