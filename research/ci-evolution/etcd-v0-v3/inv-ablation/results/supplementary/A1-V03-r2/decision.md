# Invariant maintenance decision: etcd-raft update (auto-leave, joint admission, probing)

**Overall: MODIFY.** Most of the old suite still states the required contracts and is kept unchanged, including the core safety controls.
- **Modify (3):** `AutoLeaveAdvance`, `ProposalContract`, `ExpectedDecision`.
- **Add (3):** `CommittedConfEntryCoherence`, `LeaderTransfereeIsVoter`, and (recommended) `NewMemberProbe`.
- **Remove:** nothing.

`AutoLeaveAdvance` must **not** be weakened to the source's new "crossing" gate. That gate is where the new source appears to fail its auto-leave contract (D1/D2).

Nothing was executed (no TLC, no tests). Everything below comes from reading the patch, the old and new source, and the old spec.

## What changed (semantics)
| Source change | Effect on requirements |
|---|---|
| `advance()`: quota is reduced first. Auto-leave is appended only if `oldApplied < pendingConf <= newApplied`. The entry has nil Data, so it cannot be refused (a refusal panics). `pendingConf := lastIndex` after the append. | Exactly one leave per joint config; it can never be refused; `pendingConf` must cover it. |
| `stepLeader` refuses a conf change if it is pending, if the config is joint and the change has changes, or if the config is not joint and the change is empty. | New admission rule. |
| `increaseUncommittedSize` adds `s>0`. | A zero-payload batch is never quota-dropped. |
| `initProgress Next = LastIndex`, plus a probe of every progress in `switchToConfig`. | New members are probed immediately (behavioral). |
| Transfer is aborted when the transferee is not in `Voters.IDs()` (demotion included). | The transferee must stay a voter. |
| `Simple` no longer swallows `checkInvariants` errors. Sorted campaign IDs. Refactors (`maybeTerm`, `IsEmptyHardState`, `ri`). | Bug fix or order-only. No requirement change. |

## Decisions
**Modify**
- **AutoLeaveAdvance** (semantic change + repair of a pre-existing property defect + observer migration).
  - Obligation: an Advance with `cursor>0` and `cursor >= pendingBefore` that leaves a leader in an autoLeave config must leave a leave entry pending after `Len(cfgHist)`, with no Fatal.
  - Any growth of the log during Advance must be exactly one raft-generated leave entry, appended only when none is already pending, with `pendingAfter >= index`.
  - The `DropQuota` escape is removed.
  - Disagreements with the old form:
    - In the old model with an intermediate committed batch, the old form *requires* the duplicate L2; the new form forbids it.
    - In the old model, a quota drop satisfies the old form but violates the new one.
    - With a leave already pending and a re-crossing (early Advance), the old form demands another append; the new form forbids it.
- **ProposalContract** (`ProposalConfigurationDecisions`): adds the joint-mismatch refusal. The admitted entry is the earliest admissible conf entry, not "any earlier conf entry". `DropQuota` now requires `weight>0`. The observer gains `joint` and `pendingAfter`.
  - Witness: a leader in a joint config proposes V2 `<<AddLearner s3>>`. The new source rewrites it to a no-op. The old contract fails on that; the new contract fails on the old model.
- **OutcomeSoundness / ExpectedDecision**: `DropQuota` requires `o.weight>0`.
  - Witness: quota 3 > MaxUncommitted 2, then a weight-0 Normal proposal.
  - Note: `o.weight` comes from the model's own `RewriteConf`, so the check is partly circular.

**Add**
- **CommittedConfEntryCoherence**: every committed conf entry `e` satisfies `IsLeave(e) ⇔ ConfigOf(prefix).outgoing≠{}`. It uses application semantics, where a leave requires Transition=Auto.
  - It fails on the old model (joint EnterJoint, duplicate L2), holds on the new model for those cases, and exposes D4.
- **LeaderTransfereeIsVoter**: a live, promotable leader with `transfer≠0` must have `transfer ∈ VoterIDs(config)`.
  - Witness: demote a lagging transferee via a simple AddLearner. The old model keeps the transfer; the new model aborts it.
- **NewMemberProbe** (recommended, not safety): when a leader applies a change that adds peer p and `Last≥First`, a MsgApp or MsgSnap to p is emitted in that same step.
  - Witness: MC.cfg, AddLearner s4.
- **Canaries**: `JointRefusalNotReached`, `ZeroWeightOverQuotaNotReached`, `TransfereeDemotedNotReached`, `NewMemberByLeaderNotReached`, `AutoLeaveDueWithoutCrossingNotReached`.

**Keep (unchanged; these also act as false-edit controls)**
- QuotaIntegrity, AckPreservation, EffectContract, TransferContract, CampaignContract, Vote/Learner, Ready*, Joint* restore/recovery, ConfigurationOrigin/TransitionSafety, QuorumAccounting, ReplicationEvidence, NoUnexpectedFatal.
- ElectionSafety, LogMatching, LeaderCompleteness, CommittedHistory, AppliedAgreement, LogStructure, TypeOK, recovery and read properties.
- Existing canaries.

## Updated behaviors already covered by existing properties
- **Leave-entry shape, at most one entry per Advance:** `AckPreservation` (log grows by at most one V2 entry with empty changes) and `EffectContract` (id=0 ⇒ IsLeave).
- **Auto-leave owed for newly elected leaders and late ApplyConfChange:** the old `AutoLeaveAdvance` eligibility clause already flags D1/D2. The modified form keeps that obligation.
- **Quota bound after the reorder:** `QuotaIntegrity`.
- **Sorted campaign:** `CampaignContract` compares a multiset, so order is invisible.
- **Probes from `Next=LastIndex`:** `ReplicationEvidence` still requires evidence for every Match.
- **Simple's error-swallow fix:** `ConfigurationOrigin` would catch a silent switch to an empty config.

## Suspected defects (do not hide by editing properties)
- **D1 (new source):** a leader elected with `applied==lastIndex` in an autoLeave joint config never auto-leaves. `becomeLeader` sets `pendingConf=lastIndex`, so `oldApplied < pendingConf` is never true. (raft.go:567, 752)
- **D2 (new, early Advance is allowed by README:122):** if the crossing Advance happens before `ApplyConfChange(E)`, auto-leave never happens.
- **D3 (new, early Advance):** if the Advance crossing the leave index runs before `ApplyConfChange(L)`, a duplicate L2 is appended. Applying it later panics on every replica.
- **D4 (new):** `wantsLeaveJoint` ignores Transition. In a joint config, `V2{<<>>, JointExplicit}` is admitted, then applied as EnterJoint, which panics.
- **D5 (pre-existing):** with early Advance, admission can use a stale config.
- **D6 (pre-existing):** `numOfPendingConf` counts only V1 entries, so a node with a pending V2 conf entry can campaign. Keep `CampaignContract` as is.
- **D7–D9:**
  - The old duplicate-append bug. The old property mandated it.
  - The stale `decision` field that could satisfy the old DropQuota disjunct.
  - Minor doc and representation issues.

## Model migrations (not property changes)
- `AutoLeaveWeight=0` and `AutoLeaveEncoded=EmptyEncoded`.
- `AppendQuotaExceeded` gets `Weight>0`.
- `AdvanceCore` follows the source (reduce first, crossing gate, `pendingConf:=Last`, Fatal on refusal).
- `RewriteConf` gets the joint refusal.
- `Next=Last` for Changer progress and Bootstrap. Restore sets self `match=s.index-1` and `next=s.index`.
- `ApplyConfCore`: probe members with `sendEmpty=FALSE`, and abort the transfer if the target is not a voter.
- Update cfgs: list the new and modified properties, add Proposal/Outcome/Quota/Transfer contracts, and add TransferLeader to the concrete view.

## Unresolved
- **U1:** Is "ApplyConfChange before Advance" a caller obligation? This decides whether D2/D3/D5 are source defects. Run with EarlyAdvance both FALSE and TRUE.
- **U2:** Is the benign over-refusal of an empty enter-joint acceptable?
- **U3:** Auto-leave liveness (`AutoLeaveProgress`) cannot be checked with bounded MC.
- **U4:** Should `NewMemberProbe` be required?
- **U5:** Multi-entry proposal batches are never generated by the model.
- **U6:** `pendingConf` is bumped even on a quota-dropped proposal (pre-existing).
- **U7:** Trace equality fails until the model is migrated.
