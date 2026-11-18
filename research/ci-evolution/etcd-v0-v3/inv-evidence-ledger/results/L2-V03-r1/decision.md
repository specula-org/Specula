# Invariant maintenance for the update (etcd-raft: auto-leave, joint-state admission, quota, transfer demotion)

## Overall decision: modify 4 properties, add 1 new one, keep the rest

The update changes four contracts the old suite observes. The update's own tests and comments support each change:

| Update behaviour | Non-implementation evidence |
|---|---|
| Auto-leave happens **once** per joint configuration, `pendingConfIndex` moves to the auto-leave index, and the entry (nil Data) can never be refused | `testdata/confchange_v2_add_double_auto.txt:238-240` (repeated auto-leave was a bug that panicked), `rawnode_test.go:319-331`, `raft.go:282-287`, `raft.go:567-579` |
| The leader rewrites a non-leave conf change while joint, and a leave while not joint, to an empty entry | `testdata/confchange_v2_add_single_explicit.txt:100-106, 165-168` |
| Empty-payload proposals are never dropped by the uncommitted-size quota | `raft.go:1616-1623` comment, `raft_test.go:251-258` |
| A pending leadership transfer is aborted when the transferee is **demoted**, not only when it is removed | new `TestLeaderTransferDemoteNode`, `raft.go:1568` |

| Property | Decision | Kind | Evidence |
|---|---|---|---|
| `AutoLeaveAdvance` (mixed) | **modify** | Semantic strengthening and observer migration | EV-AL-1…8 |
| `ProposalConfigurationDecisions` (mixed) | **modify** | Semantic (rewrite set extended; quota drop needs weight>0) and observer gains `joint` | EV-PC-1…4, EV-D3 |
| `OutcomeSoundness` (mixed) | **modify** | Semantic (weight>0) and outcome weight migrated to the new rewrite | EV-OS-1, EV-OS-2 |
| `ConfigurationTransitionSafety` (requirement) | **modify** | Repair: only bootstrap entries are excluded now, so auto-leave entries are checked | EV-CTS-1…3 |
| `PendingTransferVoter` | **add** | New requirement: a promotable leader's transferee is a (joint) voter | EV-PTV-1, EV-PTV-2 |
| All other properties | keep | Watch-touched ones re-examined against new/source (see `decision.json`) | EV-CTL-1, EV-D3 |

### Detail on the edits

**`AutoLeaveAdvance`**
- **What changed:**
  - "Due" means: auto-leave config, leader, `cursor>0`, `cursor >= pendingBefore`, and no leave entry already in the not-yet-applied log.
  - A due Advance must append exactly one empty V2 entry, and `pending` must be at least that entry's index.
  - An Advance that is not due must not append one.
  - The quota-retry (`DropQuota`) branch is removed.
- **Deliberately not done:** I did not narrow eligibility to the source's edge trigger `oldApplied < pendingConfIndex <= newApplied`. That alternative (EV-AL-7, rejected) evaluates TRUE on every defect below.
- **Observer:** `autoLeaveChecks` gains `autoLeave, leader, cursor, pendingBefore, appliedBefore, cfgApplied, beforeHist`. The legacy `eligible` field is kept.

**`ProposalConfigurationDecisions` and `OutcomeSoundness`**
- The rewrite set adds the joint-state admission rule.
- The quota drop now requires a non-empty effective payload.
- Without migrating the outcome weight, the new `ExpectedDecision` raises a false alarm on legitimate new behaviour (EV-OS-2).

**`ConfigurationTransitionSafety`**
- The old `id#0` filter also hid Raft's own auto-leave entries.
- With the repair, the old code's duplicate leave is caught when it is committed (WC1).
- The legitimate single leave (WC2) and bootstrap records (WC3) still pass.

**`PendingTransferVoter`**
- No old property observed the new demotion rule.
- During a joint demotion the transferee is still an outgoing voter, so the transfer may stay pending (control WT2).

## Executed evidence (summary)

**TLC** (`evidence/tla/Witness.tla`): 47 rows. How the rows were built:
- Pre-states are mapped from the Go scenarios.
- Transitions are computed by the **actual** `base`/`Proposed` operators (`AdvanceCore`, `Step`, `ApplyConfCore`, `MaybeCommit`).
- Records are built with the old and the migrated observers.
- Properties are evaluated through `INSTANCE … WITH history <- {record}`.

Key `AutoLeaveAdvance` rows (old definition / proposed definition):

| Witness | old / proposed |
|---|---|
| WA3: old code appends a duplicate leave | TRUE / **FALSE** |
| WA2: old code does not advance `pendingConf` | TRUE / **FALSE** |
| WA4: old `DropQuota` branch | TRUE / **FALSE** |
| WA5: new code appends a second leave after an early Advance | TRUE / **FALSE** |
| WA1: new code, fresh leader never leaves | FALSE / FALSE |
| WA6: new code misses the edge after an early Advance | FALSE / FALSE |
| WA2: new code, ordinary auto-leave | TRUE / TRUE |
| WA1: correctly fixed trigger | TRUE / TRUE |

Controls:
- Proposal rows: forged over-rewrites and a forged non-empty overflow acceptance are FALSE under both definitions.
- `AckPreservation`, `ReplicationEvidence` and `QuotaIntegrity` are TRUE in every row.

**Go** (`evidence/go/zz_evidence_test.go`, run identically in `old_tree` and `new_tree`):

| Test | Old code | New code |
|---|---|---|
| G1 | duplicate leave, then panic `can't leave a non-joint config` | single leave |
| G2 | a freshly elected leader in an auto-leave joint config leaves it | stays joint forever |
| G3 | empty proposal over quota dropped | accepted; the 1-byte proposal is still dropped in both; leave entry size measured as 0/6 bytes |
| G4 | joint non-leave and non-joint leave are admitted and then panic | rewritten to empty entries |
| G5 | transferee kept after demotion | transfer aborted |
| G6 / G7 | early-Advance duplicate and panic | duplicate and panic; plus the missed edge (G7) |

**Reachable-state checks were inconclusive** (EV-HUNT): bounded BFS and random simulation never reached an auto-leave state within the time caps. I make no claim from them.

## Suspected implementation defects (kept visible, not hidden by edits)

- **D1** (new code): a leader elected in an auto-leave joint config whose log is fully applied never auto-leaves, because the edge trigger `<` never fires. Both the old and the proposed `AutoLeaveAdvance` flag it.
- **D2a** (both revisions): if Advance for the auto-leave entry runs before `ApplyConfChange`, a second leave is appended and the apply panics. Only the proposed property flags it.
- **D2b** (new code only): if Advance for the entering entry runs before `ApplyConfChange`, the auto-leave is never initiated.
- **D3** (both revisions): `ConfChangeV2{Transition: JointExplicit}` with no changes is admitted while joint and panics at apply. The kept `NoUnexpectedFatal` flags it.
- **D4** (doc): the comment "Configuration changes are never refused" (raft.go:1609) is only true for empty payloads.

## What changed between the initial and final decisions

- **No property decision changed.** Every proposed edit was confirmed by the TLC witnesses and the Go runs. The one alternative I tested, edge-trigger eligibility, was rejected.
- **Defect attribution refined:** D2a and D3 also exist in the old code. Only D1 and D2b are regressions introduced by the update.
- **U3 resolved:** the auto-leave entry's encoded size was measured as 6 bytes.
- **New unresolved items:** U4 (should admission use `LeaveJoint()`?) and U5 (model-level reachability not shown).
- **Citations fixed:** some line numbers in the REQ-EVIDENCE blocks were off by one in the initial file. The content is unchanged.

## Open obligations

- **U1:** Is Advance before `ApplyConfChange` of a conf change a supported caller pattern? This decides whether D2a and D2b are library defects.
- **U2:** A leader that removes or demotes itself is outside `PendingTransferVoter`'s scope (untested branch in `switchToConfig`).
- **U4:** Should the admission rule use `LeaveJoint()` instead of "no Changes"? (D3)
- **U5:** A deeper, directed model run is needed to show the auto-leave paths are reachable in the model.

Files: `evidence/tla/Proposed.tla` (edited spec with the updated REQ-EVIDENCE blocks; diff in `evidence/logs/base_vs_proposed.diff`), `evidence/tla/Witness.tla`, `evidence/logs/*`, `evidence/go/*`.
