# Property maintenance decision: V00 → V01 (etcd-raft joint consensus)

**Decision: revise.** The update adds ConfChangeV2 and joint consensus: the `confchange` package, joint quorums, LearnersNext, and an AutoLeave entry that Raft proposes itself in `raft.advance`. It also moves bootstrap into `RawNode.Bootstrap` and splits Ready handling into `acceptReady`/`commitReady`.

The core Raft safety properties are kept. Properties that assume a flat voter set, single-change effects, an id-0 exemption for bootstrap entries, a rewrite set defined by `pendingConfIndex`, or "Advance never changes the log" are revised. Four properties are added. **No requirement or requirement clause was weakened.** Where V01 looks likely to break a retained requirement, I recorded a suspected defect instead of narrowing the property.

TLC and the tests were not run, and no spec or code was edited. Full entries, expressions and REQ-EVIDENCE blocks are in `out/decision.json`.

## Decisions per property

| Property | Decision | Ledger status | Watch touched | Note |
|---|---|---|---|---|
| ElectionSafety | keep | requirement | no | Joint votes are now reachable; this is the main way to expose D1. |
| LogMatching | keep | requirement | no | |
| LeaderCompleteness | keep | requirement | no | The DurableObligations observer must use JointWon. |
| CommittedHistory | keep | requirement | yes | restore only changed the config rebuild. |
| AppliedAgreement | keep | requirement | yes | |
| VoteRecovery | keep | requirement | yes | NewRawNode no longer re-bootstraps; Bootstrap checks only LastIndex (U8). |
| RecoveryBacking | keep | requirement | yes | |
| PromiseBacking | keep | requirement | yes | Messages are now cleared in acceptReady. |
| ConfigurationOrigin | modify (representation) | requirement | yes | Joint config record. Exposes D3 and D4 (restore/newRaft drop the joint fields). |
| ConfigurationTransitionSafety | **→ `_new`** | requirement | yes | Joint voter pair. The bootstrap exemption is now keyed on the bootstrap entry shape, so auto-leave entries are checked. |
| LearnerEligibility | keep | requirement | yes | Demotion is now possible; nodes in LearnersNext are still voters. |
| QuorumAccounting | **→ `_new`** | mixed | yes | Uses JointWon, backed by `raft.proto:156` and `quorum/joint.go:18`. The unknown clause is kept. |
| ReplicationEvidence | keep | requirement | yes | InitProgress was deleted; progress is preserved on promotion and demotion. |
| SnapshotBacking | keep | requirement | yes | ConfigOf now covers the joint ConfState fields. |
| AckPreservation_LogUnchanged | **→ AckPreservation_LogPreserved** | mixed | yes | Advance may append exactly one auto-leave entry. The impl-abstraction clause is updated; the requirement clause is kept. |
| AckPreservation_SnapshotRetained | keep | unknown | yes | No conflict with V01, so the unknown status stays. |
| AckPreservation_AppliedCursor | keep | requirement | yes | |
| AckPreservation | **→ `_new`** | model-internal | no | Wrapper over the revised part. |
| ReadyAccounting | keep | requirement | yes | New rule that no Step may happen between Ready and Advance (`rawnode.go:122-129`); see U3. |
| QuotaIntegrity | keep | mixed | yes | The quota is now reduced at Advance. |
| OutcomeSoundness | keep | mixed | yes | |
| ReadBasis | **→ `_new`** | mixed | no | Joint confirming quorum; singleton means a non-joint single voter. |
| ReadApplication / ReadCorrelation | keep | requirement | no | |
| NoUnexpectedFatal | modify (ledger only) | mixed | yes | Formula unchanged. The remove-unknown-peer clause is retired because new test data makes that a no-op. New panic paths are added as clauses. |
| TypeOK | **→ `_new`** | mixed | yes | (incoming ∪ outgoing) ∩ learners = {}, per the updated `tracker.go:36`. |
| LogStructure (+ both parts) | keep | requirement / model-internal | no | |
| VoteDecisionEligibility | keep | mixed | no | |
| CampaignDecisionEligibility | modify (representation) | mixed | no* | Voters are incoming ∪ outgoing; singleton uses the joint quorum. **The pending-conf clause still covers V2 entries**, which exposes D1. |
| TransferDecisionEligibility | keep | mixed | no | |
| RequestCorrelatedConfigurationEffects | **→ `_new`** | mixed | yes | V2 Simple/Enter/Leave effects; the "AddLearner of a voter is a no-op" clause becomes demotion; auto-leave correlation added. |
| ProposalConfigurationDecisions | **→ `_new`** | mixed | yes | The rewrite set adds "unapplied conf entry in the leader's log" (`node.go:137`), which exposes D2. |

\*The function bodies are unchanged, but V01 adds a configuration entry type that `numOfPendingConf` does not count, so I re-checked this property anyway.

**Added properties**
- **JointConfigWellFormed** (structural): LearnersNext ⊆ outgoing; learners disjoint from both voter halves; a non-joint config has no staged learners and AutoLeave unset; a non-empty config has incoming voters.
- **ConfigurationStepSafety** (safety): every applied step is either simple (at most one incoming voter changed) or a clean joint enter/leave. It reads the actual before/after configs at apply time.
- **AutoLeaveSoundness** (interaction): an auto-leave entry is only applied to a joint config with AutoLeave set, and a log holds at most one unapplied auto-leave entry.
- **JointAutoLeaveProgress** (liveness): a joint AutoLeave config at a leader eventually leaves joint. It needs a fairness driver.

## Suspected implementation defects (not hidden by property edits)
- **D1 (high, safety):** `numOfPendingConf` ignores `EntryConfChangeV2` (`raft.go:1583`, used at line 907). A node with a committed but unapplied joint entry can campaign under its stale config. In a joint replacement whose old and new majorities can be disjoint, that can produce two leaders in the same term.
- **D2 (high):** The auto-leave append does not raise `pendingConfIndex` on success (`raft.go:572-580`). A later Advance can append a second leave entry, and applying it to a non-joint config panics every node. Client conf changes are also admitted while the leave entry is pending.
- **D3 / D4 (medium):** `restore` (`raft.go:1386-1423`) and `newRaft` (`332-341`) ignore `nodes_joint`, `learners_next` and `auto_leave`, so a joint snapshot or InitialState comes back non-joint. A node present only in the outgoing half rejects such a snapshot.
- **D5 (medium, liveness):** Auto-leave is only triggered in `advance()` when the applied cursor is nonzero. With early Advance, or after a quota-dropped leave, an idle cluster can stay joint.
- **D6 (medium, status unknown):** Nothing checks at proposal time whether a conf change is valid for the current config. Invalid ones are committed and then panic every node at apply (`raft.go:1454-1457`).
- **D7–D9 (low):** A leader that demotes or removes itself keeps leading, and a comment claiming demotions are prevented is stale. `Simple` swallows an invariant error (`confchange.go:148-149`, latent). `Config.Clone` drops AutoLeave, so Status always reports it false.

## Unresolved obligations
- **U1–U2:** Implement the joint config record, V2 entries, ConfigOf, JointWon and the observer changes. Keep the model faithful to D1–D6 (V1-only Hup scan, lossy restore and restart, no `pendingConfIndex` bump on auto-leave, confchange errors as Fatal) so the properties can actually fail.
- **U3:** Decide whether the RawNode caller model must respect the Ready→Advance no-mutation rule. Check how EarlyAdvance interacts with auto-leave.
- **U4:** Settle the unknown clause of NoUnexpectedFatal: should Raft refuse invalid conf changes, or is it a caller contract not to propose them?
- **U5:** The nonempty-voter-set and leader-in-voters clauses remain unknown.
- **U6:** Should a demoted or removed leader step down?
- **U7:** README is stale: it says to call `StartNode(c, nil)`, which now panics, and it still says "one node at a time".
- **U8:** Bootstrap's emptiness check ignores the HardState.
- **U9:** `MCTypeOK` (MC.tla is not in the inputs) must be redefined over `TypeOK_new`.
- **U10:** Liveness needs a fairness driver.
- **U11:** Workloads must include V2 joint changes, including a disjoint-majority replacement, or the new properties are vacuous.

## cfg changes
- Swap the enabled names for the `_new` versions in: base, MC, MC_hunt_1_*, MC_hunt_2, MC_hunt_3_*, MC_hunt_4, MC_hunt_5_*, and Trace.
- In every quality block: replace RequestCorrelatedConfigurationEffects and ProposalConfigurationDecisions with their `_new` versions, and add ConfigurationStepSafety.
- In MC_hunt_3_*: enable AutoLeaveSoundness, JointConfigWellFormed and NoUnexpectedFatal.
- In MC_hunt_4: enable ConfigurationOrigin and JointConfigWellFormed.
- Add a commented `PROPERTY JointAutoLeaveProgress` line.
