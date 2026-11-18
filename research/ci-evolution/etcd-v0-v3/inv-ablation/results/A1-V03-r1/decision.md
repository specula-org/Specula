# Invariant maintenance decision: etcd-raft update (auto-leave, joint admission, quota, transfer)

**Overall: MODIFY.**
- 4 properties modified: 3 for semantic changes, 1 as a repair of a pre-existing defect.
- 2 safety properties and 4 reachability canaries added.
- Everything else is kept as a safety control.
- 3 suspected new-source defects (D1–D3) stay visible and are not absorbed by any property edit.

Machine-readable version: `out/decision.json`. It holds the full predicates and the witness IDs used below.

## What changed in the source

| ID | Change | Kind | Evidence |
|---|---|---|---|
| C1 | `advance()` reduces quota first. Auto-leave fires only when `oldApplied < pendingConfIndex ≤ newApplied`. The leave entry has nil Data (payload 0), cannot be refused (panic otherwise), and moves `pendingConfIndex` to the leave index. | semantic | raft.go:556-593, rawnode_test.go:316-329, confchange_v2_add_double_auto.txt:238-240 |
| C2 | The leader rewrites a conf change to a no-op if one is pending, if the config is joint and `Changes` is non-empty, or if the config is not joint and `Changes` is empty. | semantic | raft.go:1052-1072 |
| C3 | Entries with zero payload are never refused for quota. | semantic | raft.go:1616, TestUncommittedEntryLimit |
| C4 | A transfer is aborted when its target is no longer a voter (now including demotion to learner). | semantic | raft.go:1568-1571, TestLeaderTransferDemoteNode |
| C5 | After a config change that does not advance commit, the leader probes all peers. | non-safety | raft.go:1556-1567 |
| C6 | New peers start with `Next = LastIndex`. | non-safety | confchange.go:265 |
| C7 | `Simple()` no longer swallows invariant errors. | latent repair | patch:36-45 |
| C8 | Sorted campaign fan-out, `maybeTerm`/`newRaft`/ReadIndex refactors, harness and docs. | representation | — |

## Property decisions

### Semantic requirement changes

- **AutoLeaveAdvance: modify.** The old version was level-triggered, so it *required* a fresh leave on every Advance while `autoLeave` held, including when a leave was already pending. That is the duplicate append that panics, a defect in the old property. It also allowed `DropQuota`.
  - **New rule:** on each Advance, a leader whose `autoLeave` joint config is in effect, with `cursor ≥ pendingConf` and no unapplied leave entry after `Len(cfgHist)`, must append exactly one leave and set `pendingConf` to its index.
  - **Converse:** a leave may be appended only in that case.
  - **Observer migration:** add `role`, `autoLeave`, `cursor`, `pendingBefore`, `cfgIndex`, `beforeHist` and `fatal` to `autoLeaveChecks`.
  - **Why it stays level-based:** this deliberately keeps the old trigger rather than the source's edge, so D1 and D2a stay visible.
  - **Where old and new disagree:**
    - W-AL0: on the old model `pendingConf` is not bumped.
    - W-AL1: on the old model a second leave is appended (the testdata regression).
    - W-AL2: on the old model the leave is refused for quota.
    - W-AL3: on the new model with early Advance, a duplicate leave is appended.
- **ProposalConfigurationDecisions: modify.**
  - Add the `joint` observation and the phase rule `WantsLeave(e) == V2 ∧ changes = ⟨⟩`.
  - Only an earlier *admitted* conf entry blocks later ones in the same batch.
  - `DropQuota` now requires `weight > 0`.
  - Disagreement witnesses: W-PC1 (Simple change in joint), W-PC2 (leave while not joint), W-PC3 (zero-weight entry with quota 3 > 2).
- **OutcomeSoundness: modify.** `DropQuota` requires `o.weight > 0`. The weight must come from the phase-aware effective entries, not from the model's `RewriteConf`. Witnesses: W-OS1, W-OS2.
- **LeaderTransferTargetVoter: add.**
  - Predicate: a live, promotable leader with `transfer ≠ 0` has `transfer ∈ VoterIDs(config)`.
  - W-TR1/W-TR2: the old model keeps the transfer after the target is demoted (simple or via joint), so the property is violated there; the new model aborts it.
- **ConfigurationPhaseApplicability: add.**
  - Predicate: for every applied conf entry, `IsLeave(e) = (before.outgoing ≠ {})`.
  - Needed because `EffectContract` and `ConfigurationOrigin` both still hold when an invalid conf entry is applied (invalid transitions are no-ops in `ConfigOf`, and the model only Fatal-s). Only `NoUnexpectedFatal` catches it today, and it is not enabled in any V2 cfg.
  - Witnesses: W-PA1/W-PA2 (old model), W-PA3 (new model, which is defect D3).

### Pre-existing property repair

- **ConfigurationTransitionSafety: modify.** Its `id ≠ 0` guard exempts auto-leave entries too, although its comment says the exemption is only for bootstrap entries. Narrow the exemption to bootstrap entries (`id=0 ∧ AddVoter ∧ term=1 ∧ k ≤ Len(BootPeers)`).
  - W-CT1: on the old model, the duplicate leave is committed under the joint config.
  - Get a baseline on the old model first. Do not weaken the property if it also flags a lagging new leader.

### Representation / observer migrations, no requirement change

- **CampaignDecisionEligibility: keep.** The sorted send order is invisible to the set-valued observer.
- **AckPreservation: keep.** It still allows at most one empty-V2 append per Advance; cross-Advance duplicates are now checked by AutoLeaveAdvance.
- **RequestCorrelatedConfigurationEffects: keep.** A nil-Data leave entry is the same model entry, so `id=0 ⇒ IsLeave` still holds.
- **Model constant migration (not a property):** `AutoLeaveWeight = 0` and `AutoLeaveEncoded = 6`. An Entry with nil Data encodes to 6 bytes (Type, Term, Index), per raft.pb.go:825-838.

### Unchanged safety controls (keep)

ElectionSafety, LogMatching, LeaderCompleteness, CommittedHistory, AppliedAgreement, TypeOK/LogStructure, VoteRecovery, RecoveryBacking, PromiseBacking, ConfigurationOrigin, LearnerEligibility, QuorumAccounting, ReplicationEvidence, SnapshotBacking, ReadyAccounting, ReadyOwnership, JointConfigurationShape, JointSnapshotRecovery, JointSnapshotMemberAcceptance, QuotaIntegrity, Read*, NoUnexpectedFatal, Vote/Transfer decision contracts, liveness targets, and the existing canaries.

All of these must still hold on the updated model; a new failure means a model or edit error.

### New hunt canaries (expected to be violated)

`PhaseRefusalNotReached`, `ZeroWeightOverQuotaNotReached`, `TransferDemotionNotReached`, `AutoLeaveJointElectionNotReached`. They show that the changed paths are actually exercised, so passing results aren't vacuous.

## Updated behaviors already covered by existing properties

- **C5 probe and C6 `Next = LastIndex`:**
  - ReplicationEvidence: Match is always backed by acknowledgement evidence.
  - PromiseBacking: commit witnesses on MsgApp are disk-backed.
  - QuotaIntegrity: inflights stay ordered and at most MaxInflight.
  - LogMatching, and NoUnexpectedFatal for the out-of-bounds and snapshot fatals.
  - No property reads `Next`.
- **C1 zero-weight leave and quota reorder:** QuotaIntegrity and AckPreservation. Also ConfigurationTransitionSafety, but only after the repair above.
- **C8 refactors:** CampaignDecisionEligibility, LogMatching/LogStructure/SnapshotBacking, VoteRecovery/RecoveryBacking, ReadBasis.

## Suspected defects (do not hide with property edits)

- **D1 (new, introduced):** a leader elected in an `autoLeave` joint config with `applied == lastIndex` never auto-leaves. `becomeLeader` sets `pendingConfIndex = lastIndex`, and the edge check `oldApplied < pendingConfIndex` is then false. After that, C2 refuses every non-leave conf change. Witness W-AL4.
- **D2 (new, needs the early Advance that README.md:122 permits):**
  - (a) The auto-leave is missed if the Advance crossing `pendingConf` comes before the enter-joint entry is applied (W-AL5).
  - (b) A second leave is appended if the Advance crossing the leave's index comes before the leave is applied; applying it later panics (W-AL3).
- **D3 (new):** the admission check `wantsLeaveJoint := len(Changes)==0` admits V2 `{Changes: [], Transition: JointImplicit/JointExplicit}` in a joint config. On apply it takes the EnterJoint path and panics with "config is already joint" (W-PA3).
- **D4 (pre-existing, inherited by C2):** admission compares against the Advance cursor and against the config as last applied, so an early Advance can admit a change against a stale config.
- **D5 (old, fixed by this update):** duplicate or quota-refused auto-leave, and conf proposals admitted while a leave was pending.
- **M1 (model work, not property work):** AdvanceCore, AppendQuotaExceeded, RewriteConf, the ApplyConfCore abort and probe, ChangeProgress `next = last`, and the auto-leave size constants all need updating in the model.

## Unresolved

- **U1:** auto-leave liveness. A temporal property, `AutoLeaveProgress`, is proposed but needs an unbounded liveness driver to check.
- **U2:** probe latency (C5). This is a performance concern, not safety.
- **U3:** the early-Advance caller contract. Run the update cfgs with both `EarlyAdvance` FALSE and TRUE.
- **U4:** trace re-recording for the changed sizes and `Next` values.
- **U5:** pre-existing mismatch: CampaignContract treats pending V2 entries as blocking Hup, but the source and the model's StepHup count only V1 entries.

## Cfg recommendations

- Add the modified and new properties to `Update_full` and `Update_focused`.
- Run one V2 cfg with MC-style weights (`{0,1,3}`, `MaxUncommitted 2`) so that quota can exceed the limit.
- Keep `NoUnexpectedFatal`, or a scoped variant, in the V2 cfgs.
