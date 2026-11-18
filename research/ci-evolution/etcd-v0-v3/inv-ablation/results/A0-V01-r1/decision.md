# Property maintenance decision: etcd-raft V00 → joint consensus update

**Decision: REVISE.** The core Raft safety properties are kept unchanged. Every property that depends on the old single voter set or on V1-only conf-change semantics is revised to a `*_new` name, and its stale cfg enablement is removed. Four properties are added. Three high-severity implementation defect candidates are recorded. The revised properties are written so these defects surface as violations; none of the properties was weakened to make them pass.

Scope: properties only. Nothing was run (no TLC, no tests) and no code or spec was edited. `MC.tla` is referenced by the cfgs but is not in the inputs, so `MCTypeOK`, `MCSpec`, `StateConstraint`, `TraceSpec` and the five progress properties could not be reviewed.

## What changed (relevant to properties)
- `confchange.Changer` now drives every config change: Simple / EnterJoint / LeaveJoint. Two new behaviours come with it: AddLearner on a voter now **demotes** (or stages the node in `LearnersNext` while joint), and removing an unknown peer is a **no-op**. Removing or demoting the **last voter panics** (`raft.go:1454-1457`).
- New entry type `EntryConfChangeV2` with transition modes Auto, JointImplicit and JointExplicit.
- `ConfState` has new fields: `NodesJoint`, `LearnersNext` and `AutoLeave`.
- For auto-leave configs, the leader appends an empty ConfChangeV2 **from `raft.advance()`** (`raft.go:559-581`).
- `maybeCommit` now runs after every applied conf change, not only after removals.
- `RawNode.Ready()` is now read-only. Messages, read states and the quota are settled at Advance. Bootstrapping moves to `RawNode.Bootstrap`.

## Property decisions

| Property | Action | Why (key evidence) |
|---|---|---|
| ElectionSafety, LogMatching, LeaderCompleteness, CommittedHistory, AppliedAgreement | keep | Still promised. Elections and commits now need both majorities (`quorum/joint.go:46-75`). The "committed" observer `DurableObligations` must use `JointWon`; that is a representation change only. |
| VoteRecovery, RecoveryBacking, PromiseBacking, LogStructure | keep | `loadState` and the persistence contract are unchanged. A restarted Node no longer re-emits an unchanged HardState (`node_test.go:650-711`), which is harmless. |
| LearnerEligibility, VoteDecisionEligibility | keep | `isLearner` is the learner flag on the node's own progress entry, which holds exactly for members of `Learners`. Nodes staged in `LearnersNext` are still outgoing voters. |
| ReplicationEvidence, QuotaIntegrity, OutcomeSoundness, ReadyAccounting, ReadApplication, ReadCorrelation, TransferDecisionEligibility, TraceMatched | keep | Unchanged; helpers and observers just use the new joint representation. The quota release moved to Advance (`raft.go:583`), and the bound still holds. |
| NoUnexpectedFatal | keep, and **enable in hunt_3** | The old "remove unknown peer" fatal is gone. New panics come from applying conf changes, and must stay violations when raft itself causes them. |
| TypeOK → **TypeOK_new** | modify (structural) | Joint config record; `DOMAIN prs = MembersOf(config)`; the disjointness check is kept. |
| ConfigurationOrigin → **_new** | modify | `ConfigOf_new` follows the Changer and compares the full joint record. This is the oracle for restore/restart dropping joint state (D3). |
| ConfigurationTransitionSafety → **_new** | modify | Compares both voter halves. The exemption now covers bootstrap entries only, so auto-leave entries (also id 0) are checked. Exposes D2. |
| QuorumAccounting → **_new** | modify | Recorded wins and commits must satisfy `JointWon`. |
| SnapshotBacking → **_new** | modify | Snapshot config must equal the full ConfState computed by `ConfigOf_new`. |
| AckPreservation → **_new** | modify (the guarantee changed) | Advance may now append exactly one auto-leave entry, under the source's exact conditions (`raft.go:559-571`). All other conjuncts are verbatim. |
| ReadBasis → **_new** | modify | Joint read quorum, and `leader ∈ JointVoters` is **kept**. |
| CampaignDecisionEligibility → **_new** | modify | The pending-conf check covers **V1 and V2** entries. Expected to flag D1. |
| RequestCorrelatedConfigurationEffects → **_new** | modify | Demotion, joint enter/leave, and auto-leave entries without a request id. Each applied change must be valid on its before-config. |
| ProposalConfigurationDecisions → **_new** | modify | V2 is a conf entry. Adds a conjunct from the new `ProposeConfChange` doc (`node.go:135-147`): an admitted conf change implies no unapplied conf entry in the leader's log. This sees D2 through the proposal path. |
| **JointConfigWellFormed** | add (structural) | Mirrors the Changer's own invariant check (`confchange.go:281-337`). |
| **PendingConfIndexCoverage** | add (interaction) | Documented invariant: `pendingConfIndex` ≥ every pending conf entry (`raft.go:280-286`). Directly exposes D2. |
| **ConfChangeApplicability** | add (safety) | Every committed conf-change sequence must apply without a Changer error; a failure panics at apply. |
| **AutoLeaveProgress** | add (liveness, cfg-disabled) | Auto/Implicit joint configs are eventually left. This is the only property that sees the liveness side of D3. |
| MCTypeOK; ElectionProgress, CatchupProgress, ManagementProgress, TransferSettlement, ReadProgress | unresolved | Defined in the absent `MC.tla`. Keep them disabled and recheck for joint semantics. |

Cfg plan:
- **Quality block, all cfgs:** swap in the three `*_new` contracts.
- **hunt_3 cfgs:** add PendingConfIndexCoverage, ConfChangeApplicability and JointConfigWellFormed, and enable NoUnexpectedFatal.
- **hunt_4:** add ConfigurationOrigin_new.
- **Trace.cfg:** enable everything.
- **New `MC_hunt_7_joint.cfg`:** with a V2 workload. The current workload is V1-only, which makes D1–D3 unreachable.

## Updated behaviours already covered by existing properties
- **Joint quorums** for commit, vote, ReadIndex and CheckQuorum: covered end to end by ElectionSafety, LeaderCompleteness and CommittedHistory, once the "committed" observer uses `JointWon`.
- **Demotion** and the **idempotent unknown remove**: covered by the effect contract and ConfigurationOrigin_new. LearnerEligibility and VoteDecisionEligibility check that a demoted node stops voting and campaigning.
- **`maybeCommit` after every conf change:** the resulting commits are checked by QuorumAccounting_new, ConfigurationTransitionSafety_new and CommittedHistory.
- **Quota released at Advance:** QuotaIntegrity and OutcomeSoundness.
- **Read-only RawNode Ready:** ReadyAccounting (no lost read states) and AckPreservation_new.
- **V2 proposals through the pending gate:** ProposalConfigurationDecisions_new.

## Suspected implementation defects (do not hide them with property edits)
1. **D1 – Hup gate ignores V2 (high).** `numOfPendingConf` counts only `EntryConfChange` (`raft.go:907,1580-1588`), while the proposal gate treats both types as conf changes (`raft.go:1016`). A node can therefore campaign under a superseded config. Exposed by CampaignDecisionEligibility_new.
2. **D2 – Auto-leave does not bump `pendingConfIndex` (high).** The index is updated only when the append *fails* (`raft.go:572-580`). Two consequences:
   - A later Advance while the config is still joint appends a second leave entry. Applying it fails with "can't leave a non-joint config", and every node that applies it panics.
   - A user conf change can be admitted while the auto-leave entry is still pending.

   Exposed by PendingConfIndexCoverage, ProposalConfigurationDecisions_new, ConfChangeApplicability, ConfigurationTransitionSafety_new and NoUnexpectedFatal.
3. **D3 – Restore and restart drop the joint state (high).** `restore` and `newRaft` read only `Nodes`/`Learners` (`raft.go:1416-1423,1384-1403,330-365`), although the docs say ConfState "must be recorded in snapshots". A node restored between enter and leave panics when it later applies LeaveJoint; if it leads, it uses only the incoming majority and never auto-leaves. Exposed by ConfigurationOrigin_new, NoUnexpectedFatal and AutoLeaveProgress.
4. **Lower severity:**
   - D4: ReadIndex stalls in a single-voter joint config (`{x}&&{x}` is not treated as a singleton).
   - D5: `Simple` returns an empty config with a nil error when its post-apply invariant check fails (`confchange.go:148-150`). Believed unreachable.
   - D6: `Config.Clone` drops `AutoLeave`, so `Status` always reports false.
   - D7: A demoted or removed leader keeps leading (`raft.go:1476-1489`); this matters for ReadBasis_new triage.
   - B1: A promoted learner is no longer marked recently active (a behaviour change, not necessarily a defect).

## Unresolved obligations (short)
- **O1 – MC.tla:** review it, and make MCTypeOK wrap TypeOK_new.
- **O2 – Model representation:** joint config record, a V2 entry kind, a Changer-exact `ConfigAfter_new`, and joint Won/Lost/QuorumIndex.
- **O3–O5 – Model fidelity:** restore and restart must replay Nodes/Learners only. StepHup must count V1 only. Advance must append the auto-leave entry *without* bumping `pendingConf`. "Fixing" any of these in the model hides D1–D3. Also move the quota decrement from Ready to Advance.
- **O6 – Caller contract for conf proposals:** proposals must be valid against the proposer's applied config. Triage rule: a violation caused by a user-proposed invalid change is an environment issue; one caused by raft-generated entries or a stale `pendingConf` is an implementation defect.
- **O7 – RawNode contract:** no mutating calls between Ready and Advance.
- **O8 – Node removal callback:** propc is disabled iff the node was in Progress before the change and not after; update the model's wrapper.
- **O9 – Observers:** record the joint config and the auto-leave context.
- **O10 – Open question:** a new leader may commit a predecessor conf entry it has not yet applied. Validate such counterexamples before changing anything.
- **O11 – Bounds:** a V2 workload and larger limits are needed to reach joint scenarios.
- **O12 – Trace harness:** capture V2 entries and the full ConfState.
- **O13 – Stale model artifacts:** drop the "remove unknown peer" fatal and `CancelUnknownRemovals`.
- **O14 – Policy:** decide whether a demoted or removed leader continuing to lead is acceptable.

Full predicates, helper definitions (`JointWon`, `ConfigAfter_new`, `ConfValid`, …), per-cfg changes and citations are in `out/decision.json`.
