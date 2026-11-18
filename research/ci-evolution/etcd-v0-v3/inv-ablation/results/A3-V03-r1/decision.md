# Invariant maintenance for the etcd-raft update (auto-leave, joint admission, transfer abort)

## Bottom line

The update changes three behaviours that old properties observe. Final decisions:

| Property | Decision | Kind |
|---|---|---|
| `AutoLeaveAdvance` | **modify** + observer migration | strengthening; also repairs a property defect |
| `ProposalConfigurationDecisions` (`ProposalContract`) | **modify** + observer migration | semantic change + zero-weight quota relaxation (**revised after evidence**) |
| `OutcomeSoundness` (`ExpectedDecision`) | **modify** + observer migration | zero-weight quota relaxation |
| `LeaderTransferTarget` | **add** | strengthening (demoted transferee) |
| Implementation model (`AdvanceCore`, `RewriteConf`, `AppendQuotaExceeded`, `ChangeProgress`, `ApplyConfCore`, `Restore`, `AutoLeaveWeight`) | migrate the model, not a property | representation |
| Every other property (`AckPreservation`, `RequestCorrelatedConfigurationEffects`, `QuotaIntegrity`, `ReplicationEvidence`, `TypeOK`, `LogStructure`, `CampaignDecisionEligibility`, `NoUnexpectedFatal`, the standard safety set, …) | **keep** | unchanged |

The proposed text is in `evidence/tla/Proposed.tla`; its diff against base is in `evidence/logs/Proposed.diff`.

There are **four bug candidates in the new code** (the implementation produces the behaviour and the requirement forbids it). I kept the stronger properties for all of them; none was weakened to accept the code. Details are in the bug-candidate section below.

## How the evidence was produced

- **Go:** one harness, `evidence/go/ev_update_test.go`, was compiled unchanged into copies of both trees. It drives RawNode clusters and logs a record for every leader Advance (cursor, oldApplied, pendingConf before and after, appended kind, leaveInFlight). It also logs admission outcomes, quota, transfer abort, progress initialisation, restore, and vote order. Logs are in `evidence/logs/go_{old,new}_tree.log`.
- **TLC:** `evidence/tla/Witness.tla` instantiates the real `base.tla` (a byte-identical copy), `Proposed.tla` and `ProposedInitial.tla`.
  - Pre-states are mapped from the Go runs (model index = Go index + 2).
  - Post-states are computed by the model operators themselves (old vs new `AdvanceCore`, `Step`, `ApplyConfCore`, `Restore`).
  - Observer records come from the spec's own observer expressions. The migrated observers keep the old fields; a projection-equality check passed.
  - All 50 TLC evaluations matched their claimed values (`ALL-CLAIMS-MATCH TRUE`, `EXTRA-CLAIMS-MATCH TRUE`). The diagnostic lines (lengths, pendingConf, decisions, transferee, Next/Match) agree with the Go logs.
- To reproduce everything: `evidence/run_all.sh`.

## Key results

| Witness | old | proposed | Code (new) | Requirement | Outcome |
|---|---|---|---|---|---|
| AL-dup-old (old code appends a 2nd leave; Go old panics) | T | **F** | not produced | forbidden (`confchange_v2_add_double_auto.txt:238-240`) | strengthening accepted |
| AL-nobump-old (leave appended, pendingConf not bumped) | T | **F** | not produced | forbidden (`rawnode_test.go:319-331`) | accepted |
| AL-quota-old (DropQuota retry) | T | **F** | not produced (0-byte leave) | forbidden (`raft_test.go:251-258`, `raft.go:577,1620-1623`) | accepted |
| AL-normal-new / AL-dup-new / AL-quota-new | T | T | produced | allowed | controls pass |
| AL-newleader-new (BC1) | **F** | **F** | produced | forbidden | bug candidate; detection kept |
| AL-early-miss-b-new (BC2a) | **F** | **F** | produced | forbidden | bug candidate; detection kept |
| AL-early-dup-new (BC2b) | T | **F** | produced (Go panics) | forbidden | bug candidate; stronger (proposed) property kept |
| PC1/PC2/PC5 new code rewrites a joint non-leave / non-joint leave | F | T | produced | required (`confchange_v2_add_single_explicit.txt:100-106,165-168`) | accepted |
| PC1/PC2/PC5 old code admits (Go old panics) | T | F | not produced | forbidden | accepted |
| PC4 joint + empty JointExplicit admitted (BC3) | T | **F** | produced (Go panics) | forbidden | bug candidate; stronger property kept |
| PC8 zero-weight proposal at quota > max | F (new) / T (old drop) | T / F | new accepts | allowed / drop forbidden (`raft_test.go:251-258`) | relaxation accepted; PC9 forbidden control still rejected |
| OS1 / OS2 outcome quota and migrated weight | F | T | produced | allowed | accepted |
| TT-demote-oldcode (transferee demoted to learner, transfer kept) | old suite all T | **F** | not produced (new aborts) | forbidden (`TestLeaderTransferDemoteNode`) | accepted; joint-phase and removal controls are T |
| Keep checks (AckPreservation, EffectContract, ReplicationEvidence, TypeOK, LogStructure, QuotaIntegrity, CampaignDecisionEligibility) on new-code states | T | T | produced | allowed | keeps confirmed |
| Unaffected controls (ElectionSafety … JointConfigurationShape) | identical | identical | — | — | edits do not change their verdicts |

## Initial vs final decision

The only change is to **`ProposalConfigurationDecisions`**.

- **What the initial decision said.** The frozen initial contract was deterministic. Outside a joint config it admitted a conf change iff `changes # <<>>`.
- **What the evidence showed.** Witness PCinit-nonjoint-empty-explicit-old: on the old code's admission of an empty JointExplicit change (a valid no-op enter-joint, `joint_safety.txt:24-27`), the initial contract evaluates FALSE. That behaviour is allowed, and dropping it is also allowed (`node.go:136-139`). The new code does not produce it. So the initial strengthening forbade an allowed behaviour.
- **What changed.** The final contract makes that single case an optional drop: it quantifies over choice sets `S` of optional positions.
- **Detection is kept.** The nearby forbidden cases are still rejected: PC4 (empty JointExplicit admitted while joint) and PC5-old (leave admitted while not joint).

All other entries are unchanged from the initial decision. Evidence IDs are attached in `out/decision.json`.

## Bug candidates (implementation produces it, requirement forbids it)

1. **BC1 — a new leader never auto-leaves (regression).**
   - A follower applies a JointImplicit/Auto joint entry and is elected while `applied == lastIndex`. `becomeLeader` sets `pendingConfIndex = lastIndex` (`raft.go:752`), and `advance` requires `oldApplied < pendingConfIndex` (`raft.go:567`), so the auto-leave is never issued.
   - Go: the new tree stays in `voters=(1 2 3)&&(1 2 3) … autoleave` indefinitely; the old tree leaves.
   - Requirement: `testdata/confchange_v2_add_double_implicit.txt:4-5` and `raft.proto:85-86,111-112,164-166`.
   - Both the old and proposed `AutoLeaveAdvance` reject it.
2. **BC2a — early Advance loses the auto-leave (regression).**
   - `README.md:122` and `node.go:164-167` allow calling Advance before applying. When Advance runs over the joint entry before `ApplyConfChange`, the crossing is consumed while the config is not yet joint, and the leave is never issued.
   - Go: the new tree stays joint; the old tree leaves on the next Advance.
   - Both properties reject it.
3. **BC2b — early Advance duplicates the leave (pre-existing, not fixed by the update).**
   - When Advance runs over the leave entry before it is applied, a second leave is appended. Applying it panics with "can't leave a non-joint config", in both trees.
   - The old `AutoLeaveAdvance` accepts this. The proposed one rejects it (leaveInFlight).
   - `NoUnexpectedFatal` catches the apply-time Fatal in the model, but it is not enabled in the Update cfgs.
4. **BC3 — an empty JointExplicit/JointImplicit change is admitted while joint.**
   - Admission uses `len(Changes)==0` as the test for "leave" (`raft.go:1055`). By `raftpb/confchange.go:71-73,100-102`, such a change is EnterJoint, so applying it panics with "config is already joint" (Go confirms this in both trees).
   - The old contract accepts it; the proposed one rejects it.

## Behaviour the update fixed (old-code defects, not new bugs)

- Duplicate auto-leave in the normal flow (AL-dup-old).
- Admitting a leave outside a joint config, or a membership change inside one (PC1/2/5-old; the old code panics on apply).
- Keeping a leadership transfer to a demoted learner (TT-demote-oldcode).
- Refusing zero-size entries under quota (PC8-old).

## Still open

- **Liveness.** Eventual auto-leave is not expressible by the per-Advance safety check. A liveness property such as `joint /\ autoLeave /\ stable leader ~> ~joint` should be added; it was not executed.
- **How BC2a/BC2b were driven.** I drove them with RawNode in Node's call order (`node.go:356,388-389`). They are reachable through `Node.Advance`, but not by a RawNode caller that follows `rawnode.go:170`.
- **No full model check.** `Proposed.tla` was only parsed and evaluated on the witnesses. No bounded TLC run of the full spec was done. I recommend adding `LeaderTransferTarget` and `NoUnexpectedFatal` to `Update_focused.cfg`; this was not run.
- **Pre-existing, not update-related, not executed.** `CampaignContract` counts V2 entries as pending conf changes, while the code and model count only EntryConfChange (`base.tla:267` vs `684`; `raft.go:1652-1660`).
- **Kept without execution.** The read, recovery and snapshot properties were kept from patch review alone; none of them is touched by the update.
