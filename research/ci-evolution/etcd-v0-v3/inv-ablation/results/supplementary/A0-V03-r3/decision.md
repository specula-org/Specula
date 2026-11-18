# V03 property maintenance decision

**Decision: revise.** Most properties are kept (their justification must be rechecked). Five are revised, eight are added, and the stale cfg enablements are replaced. No property definition is deleted outright. Full predicates and evidence are in `decision.json`.

## What changed in the source that affects properties

| # | Change | Source |
|---|---|---|
| 1 | Auto-leave is now edge-triggered (`oldApplied < pendingConfIndex <= newApplied`). The entry has nil Data (size 0), a refusal panics, and `pendingConfIndex` is set to the leave entry's index. The quota is reduced before the append. | raft.go:556-584 |
| 2 | The leader refuses non-leave conf changes while joint, and empty conf changes while not joint. Refused entries are rewritten to EntryNormal. | raft.go:1052-1073 |
| 3 | Zero-size appends are never quota-refused (`s > 0`). | raft.go:1616; raft_test.go:251-265 |
| 4 | A transfer is aborted when its target is no longer in `Voters.IDs()` (either joint half). This now covers demotion as well as removal. | raft.go:1568-1571; TestLeaderTransferDemoteNode |
| 5 | New Progress starts at `Next = LastIndex`, and new replicas are probed when the config switches. | confchange.go:265; raft.go:1556-1567; confchange_v2_add_double_auto.txt:53-62 |
| — | No semantic change: sorted campaign IDs, `maybeTerm` refactor, `IsEmptyHardState`, lease `ri`, value receivers, Simple's dead `checkInvariants`. | patch |

## Property decisions

**Modified**
- **ProposalConfigurationDecisions → `_new`**: adds the joint/non-joint refusal rules (only an *accepted* conf entry blocks later ones), requires `w > 0` for a quota refusal, and checks that `pendingConf` moves to the accepted entry's index.
- **OutcomeSoundness → `_new`**: requires `w > 0`. The weight now comes from the independent admission oracle; the old version called the draft's own `RewriteConf`.
- **AutoLeaveAdvance → `_new`** (and `UpdateAutoLeaveAdvance` rebound):
  - The DropQuota escape is removed, the leave entry must have weight 0, and `pendingConf` must equal the leave entry's index.
  - A converse is added: no leave may be appended while a conf entry is still unapplied by the application (the dedupe regression from the source test).
  - **Not weakened:** a leader that is in an autoLeave joint config with `applied >= pendingConf` must still append the leave. The obligation is not narrowed to the new edge trigger.
- **ConfigurationTransitionSafety → `_new`**: only bootstrap entries are excluded now. The old version excluded every `id=0` entry, which also hid auto-leave entries, and those are quorum decisions.

**Added**
- **JointStateConsistency** (interaction): every committed leave entry follows a joint config, and every other committed conf entry follows a non-joint config. Applying an entry that breaks this panics.
- **LeaderTransfereeVoter** (state) and **TransferConfigAbort** (step): a promotable leader's transfer target is always a voter. Applying a conf entry keeps the transfer exactly when the target is still a voter, and aborts it otherwise.
- **NewReplicaProbe** (interaction): every newly added member gets a MsgApp or MsgSnap in the same step, unless the leader's log is fully compacted and either commit did not advance or no snapshot is available.
- **ProgressNextBounds** (structural): `next >= 1` for every live node; `next <= Last + 1` for leaders.
- **ConfigurationApplyNoFatal**: `NoUnexpectedFatal` scoped to the apply-time and auto-leave panic paths.
- **AutoLeaveProgress** (liveness, unchecked like the other progress properties).
- **Reachability canaries**: JointAdmissionRefusal, ZeroWeightQuotaBypass, TransfereeDemotionAbort, NewReplicaProbe, AutoLeaveAfterElection.

**Kept** (recheck justification): ElectionSafety, LogMatching, LeaderCompleteness, CommittedHistory, AppliedAgreement, VoteRecovery, RecoveryBacking, PromiseBacking, ConfigurationOrigin, LearnerEligibility, QuorumAccounting, ReplicationEvidence, SnapshotBacking, AckPreservation, ReadyAccounting, ReadyOwnership, JointConfigurationShape, JointSnapshotRecovery, JointSnapshotMemberAcceptance, QuotaIntegrity, Read*, NoUnexpectedFatal, the five decision contracts other than Proposal, TypeOK/MCTypeOK, LogStructure, the five liveness targets, TraceMatched, the V02 aliases and the existing canaries.

**Unresolved**: the transfer of a removed or demoted leader (raft.go:1537-1548 returns early; the source marks the branch untested and states no promise).

## Updated behaviors that existing properties already cover
- Auto-leave appends at most one empty V2 entry per Advance, the entry is a leave, and its effect equals `ConfigAfter` → **AckPreservation**, **RequestCorrelatedConfigurationEffects**.
- Refused proposals never change the config → **ConfigurationOrigin**.
- Zero-size and auto-leave entries keep quota bounded → **QuotaIntegrity**.
- Vote requests are still a complete, duplicate-free set → **CampaignDecisionEligibility**.
- A demoted transferee that receives TimeoutNow does not campaign → **LearnerEligibility**.
- Commits of leave entries use both joint halves → **QuorumAccounting**.

## Suspected defects (must not be hidden by property edits)
- **D1 — a new leader never auto-leaves.** `becomeLeader` sets `pendingConfIndex = lastIndex` (raft.go:752). If the leader had already applied its whole log, the strict `<` in raft.go:567 never fires again. The joint config then stays forever unless the application proposes a leave, which breaks the raft.proto auto-leave promise (raft.proto:85-91,111-113). The old level trigger did fire in this case. This is the strongest candidate.
- **D2 — duplicate leave under early Advance.** If Advance runs before `ApplyConfChange` of the leave entry, `AutoLeave` is still true, so a second leave is appended. Applying it calls `LeaveJoint` on a non-joint config and panics.
- **D3 — admission and apply disagree on "leave".** Admission treats any V2 with empty `Changes` as a leave (raft.go:1055). `LeaveJoint()` also requires a zero Transition. So an empty JointImplicit/JointExplicit proposal is admitted while joint and then panics at apply. When not joint it is now refused, even though the Changer would accept it.
- **D4 — stale joint check.** The `alreadyJoint` check reads the applied-by-app config. Under early Advance it can admit a Simple change that panics when applied.
- **Model gaps M1–M8** (old level-triggered AdvanceCore with DropQuota retry, nonzero auto-leave weight, quota rule without `w > 0`, missing joint admission rules, `Next = last + 1`, transfer abort over members, missing probe, self-referential outcome weight). The revised properties will flag all of them; the fix belongs in the model, not in the properties.

D2 and D4 depend on the caller contract: Node allows early Advance (node.go:162-167), but `RawNode.Advance` says "has applied". The model's `EarlyAdvance` ignores this distinction.

## Cfg actions
- Replace the old names with the `_new` variants wherever they are enabled: ProposalConfigurationDecisions (MC, base, all MC_hunt, Trace*), OutcomeSoundness (MC_hunt_3*, MC_hunt_6, Trace*), ConfigurationTransitionSafety (MC_hunt_3*, Trace*), and `UpdateAutoLeaveAdvance` (Update_full and Update_focused).
- In the V03 Update cfgs, enable the new properties together with QuotaIntegrity, RequestCorrelatedConfigurationEffects, ConfigurationOrigin and ProgressNextBounds.

## Open obligations
1. Triage D1–D4 in validation.
2. Settle the early-Advance contract separately for RawNode and Node; checking D2/D4 needs a non-RawNode server.
3. The current Update cfgs cannot reach the zero-weight quota bypass, and Update_focused cannot reach any transfer. Add hunt cfgs and confirm each canary is reached before trusting a pass.
4. Add the ghost observer fields listed in the JSON. No protocol guard may read them.
5. Regenerate the traces; the auto-leave entry size, Next values and probe messages have changed.
6. Decide whether a promise exists for the removed-leader transfer.
7. Recheck ConfigurationTransitionSafety for leaders whose applied config lags (a pre-existing caveat).
8. JointStateConsistency may get expensive on long logs; memoize it as a ghost if needed, without weakening the predicate.
9. AutoLeaveProgress needs an unbounded fair driver to be checked.
10. Have source owners confirm that refusing empty non-Auto V2 proposals is intended.

No tests or TLC were run, and no code, spec or cfg files were changed.
