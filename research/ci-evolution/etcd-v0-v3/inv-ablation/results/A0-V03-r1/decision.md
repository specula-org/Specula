# V03 property decision: **revise**

The full record is in `out/decision.json`. Nothing was executed and no spec, cfg or code was edited.

## What changed semantically (from `update.patch` and `new/source`)
| ID | Change | Evidence |
|---|---|---|
| U1 | **Auto-leave changes.** It now fires on an edge: `oldApplied < pendingConfIndex <= newApplied`. The entry has nil Data (payload 0), so it can't be refused (refusal now panics). It sets `pendingConfIndex` to the leave index. Quota is reduced before the append. | raft.go:556-593; testdata `confchange_v2_add_double_auto.txt:238-279` (the old multi-leave panic regression); rawnode_test.go:317-330 |
| U2 | **Joint-aware conf-change admission.** A non-empty change is refused while joint, and an empty change is refused while not joint. A refused entry becomes an empty `EntryNormal`. | raft.go:1036-1073; `confchange_v2_add_single_explicit.txt:100-106,165-168` |
| U3 | **Quota exemption.** Zero-payload batches are never quota-refused (`s>0`). | raft.go:1610-1628; `TestUncommittedEntryLimit` |
| U4 | **Immediate probing of new peers.** `initProgress` sets `Next=LastIndex`, and `switchToConfig` probes peers immediately, so new peers get a non-empty MsgApp right away. | confchange.go:256-273; raft.go:1556-1567; `confchange_v2_add_double_auto.txt:53-62` |
| U5 | **Transfer abort on demotion.** The transfer is aborted when the transferee is no longer in `Voters.IDs()` (demotion now counts, not just removal). | raft.go:1568-1571; `TestLeaderTransferDemoteNode` |
| R | **Representation only:** sorted campaign order, `maybeTerm` refactor, `IsEmptyHardState`, lease `ri`, `Simple` redundant check, `Describe*` helpers, test harness. | — |

## Property decisions
**Kept (all must be rechecked):**
- ElectionSafety, LogMatching, LeaderCompleteness, CommittedHistory, AppliedAgreement
- VoteRecovery, RecoveryBacking, PromiseBacking
- ConfigurationOrigin, ConfigurationTransitionSafety, LearnerEligibility, QuorumAccounting
- ReplicationEvidence, SnapshotBacking, AckPreservation, ReadyAccounting, ReadyOwnership
- JointConfigurationShape, JointSnapshotRecovery, JointSnapshotMemberAcceptance (carried-over V02-U4 candidate, not weakened)
- QuotaIntegrity, ReadBasis, ReadApplication, ReadCorrelation, NoUnexpectedFatal
- TypeOK/MCTypeOK, LogStructure
- Vote/Campaign/Transfer DecisionEligibility, RequestCorrelatedConfigurationEffects
- All MC liveness targets, TraceMatched (traces need regenerating), the V02 `Update*` aliases and canaries

**Revised (stale cfg enablement removed, `_new` enabled in the same cfgs):**
- `AutoLeaveAdvance` → **`AutoLeaveAdvance_new`**. The old one encoded the level-triggered behavior and the DropQuota retry, which is exactly the bug the regression test removes. The new one checks both directions: an eligible Advance (computed from raw `oldApplied`, `cursor`, `pendingBefore` and `autoLeave`) appends exactly one leave with weight 0 and bumps `pendingConf`; an ineligible one appends nothing. `UpdateAutoLeaveAdvance` is re-pointed to it.
- `ProposalConfigurationDecisions` → **`_new`**. It adds the `s>0` quota rule and the joint admission rules. It also fixes the old "any earlier conf entry in the batch" clause: an entry refused by the joint rule doesn't bump the pending index. It checks the `pendingAfter` bookkeeping too.
- `OutcomeSoundness` → **`_new`**. Same `s>0` and joint rules; the expected weight is now recomputed from raw entries instead of the draft's `RewriteConf`.

**Added:**
- `AutoLeaveUnique` (safety/interaction): no two leave entries in a log without an enter-joint entry between them.
- `AutoLeaveNotStranded` (bounded safety proxy): a leader in an AutoLeave joint config with `applied >= pendingConf` must have a pending leave entry in its log.
- `AutoLeaveProgress` (liveness, unchecked): from the raft.proto AutoLeave promise.
- `ConfChangeApplicationTotal` (interaction): applying an admitted conf change, or the auto-leave, never fails.
- `TransferTargetVoter` (safety): a promotable leader's transfer target is always a voter.
- `ConfigChangeProbes` (interaction): new peers are probed with a non-empty MsgApp at `next=LastIndex`, or get a snapshot. This fails if the model keeps `Next=LastIndex+1`.
- `LeaderProgressNextBounds` (structural): a leader's peer progress always has `1 <= next <= Last+1`.
- Six V03 reachability canaries, for hunt cfgs only.

**Unresolved:** `ConfChangeNeverQuotaRefused`. The doc comment at raft.go:1609 says conf changes are never refused, but the code only exempts zero-payload entries. It goes in a validation cfg only, not the gate.

The revised properties need extra observer fields: ProposalObservation, the outcomes record, autoLeaveChecks and EffectObservation. These are representation-only changes that let the properties judge from raw state instead of the draft's guards.

## Suspected defects (record, don't hide)
- **D1 (high):** the strict `<` edge trigger can strand an AutoLeave joint config. A follower is elected with `applied == lastIndex == pendingConfIndex` and the leave entry never reached it. Nothing ever fires again; the old code would have fired. The testdata TODO at `confchange_v2_add_double_implicit.txt:4-5` says this case is untested.
- **D2 (high):** the auto-leave check reads `Config.AutoLeave` at Advance time. node.go allows Advance before applying. That gives either a missed leave (stranded) or a duplicate leave, whose apply panics with "can't leave a non-joint config".
- **D3 (medium):** admission treats `len(Changes)==0` as a leave, but apply requires `Transition==0`. So `{JointImplicit/Explicit, no changes}` proposed while joint is admitted, then every replica panics with "config is already joint".
- **D4 (medium):** joint admission reads the applied config, while the pending check reads the Advance cursor. With an early Advance, a stale config can admit a simple change that later applies inside a joint config.
- **D5:** the quota doc comment overclaims (see Unresolved above).
- **D6 (low):** the probe loop includes the leader itself. If the leader's own progress is recreated in the same change (`r<self> v<self>`), it sends itself a MsgApp.

## Key obligations
- **Modeling:** the draft model must actually implement U1–U5 so the properties test it rather than restate it.
- **Cfg reachability:**
  - `Update_full` can't reach the zero-weight-over-quota case; it needs an oversized payload weight.
  - Add an `EarlyAdvance=FALSE` variant to separate D2 from the normal path.
  - Add a hunt restricted to well-formed leave entries to separate D3.
  - Add a leader-change hunt for D1.
  - Every V03 canary must be shown to be violated (reachable).
- **Traces:** regenerate them before relying on TraceMatched.
- **Pre-existing mismatch:** CampaignContract treats V2 entries as pending conf changes, but the source's pending count only includes V1 entries. Validation should classify this; it isn't part of this update.
