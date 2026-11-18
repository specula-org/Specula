# Property decision: V02 → V03 (update.patch)

**Overall: revise.** All Raft safety contracts are kept. 3 properties and 1 alias are revised, 11 properties are added (6 checks and 5 reachability canaries), and 1 candidate is left unresolved. No requirement-level property is weakened. Full predicates, evidence and `REQ-EVIDENCE` blocks are in `decision.json`.

Inputs only: no TLC, no tests, and no spec or code edits.

## What the update changes (property-relevant)

| Change | Source |
|---|---|
| Auto-leave is now **edge-triggered** (`oldApplied < pendingConfIndex <= newApplied`). The entry has nil Data (zero payload), a refused append panics, and `pendingConfIndex` is set to the leave entry. | raft.go:556-593 |
| Conf-change admission now also refuses a **non-leave change while joint** and a **leave while not joint**. "Leave" is detected as `len(Changes)==0`. | raft.go:1036-1073 |
| Zero-payload proposals are never quota-refused. A new doc comment says "Configuration changes are never refused." | raft.go:1604-1628 |
| `switchToConfig` probes all peers (`sendIfEmpty=false`) and aborts a transfer when the transferee is **removed or demoted**. | raft.go:1556-1571 |
| `initProgress` sets `Next = LastIndex` (was +1). | confchange.go:265 |
| `Simple` no longer swallows a `checkInvariants` failure (it used to return an empty config with nil error). | confchange.go:130-147 |
| Semantics-preserving: sorted campaign order, `maybeTerm` refactor, `IsEmptyHardState`, lease-read `ri`, raftpb value receivers. | — |

## Decisions

**Revised (old cfg enablement removed and replaced):**
- **AutoLeaveAdvance → AutoLeaveAdvance_V03** (mixed). The old formula, "every eligible Advance appends", encoded V02's re-append bug and would now fail on correct no-re-append behavior. The new formula keeps the requirement (raft.proto:111) and adds two clauses:
  - When no leave entry is pending beyond the applied config, an eligible Advance appends exactly one zero-payload Auto V2 entry and sets `pendingConfIndex` to it.
  - While a leave entry is pending, Advance appends no further one.
  - The DropQuota retry branch is retired, because the append can no longer be refused (TestUncommittedEntryLimit).
- **ProposalConfigurationDecisions → _V03** (mixed). Adds the joint/leave refusal rules, backed by interaction test `confchange_v2_add_single_explicit.txt:100,165`, and the zero-payload exemption. It also blocks on an unapplied conf entry in the leader's log (README.md:195), not only on the model's `pendingConf`. A leave request is defined per raft.proto:166-168 (Auto transition, no changes).
- **OutcomeSoundness → _V03** (mixed). The quota drop now requires a non-zero effective payload (test-backed). The weight is recomputed independently under the V03 rewrite rules.
- **UpdateAutoLeaveAdvance**: alias retargeted to `AutoLeaveAdvance_V03`.

**Added:**

| Property | Kind | Why |
|---|---|---|
| TransfereeIsVoter | safety (requirement) | A promotable leader never keeps a transfer to a non-voter (TestLeaderTransferDemoteNode/RemoveNode). Nothing else observes this. |
| ConfigurationTransitionSafety_AutoLeave | interaction (requirement) | An auto-leave (id 0) entry is committed under the joint config it leaves. The old property's `id#0` filter skipped these. |
| CommittedConfigEntriesJointConsistent | interaction (mixed) | Every committed conf entry fits the joint state in log order. It sees the admission and auto-leave changes through the `ApplyConfChange` consumer, which panics on a mismatch. |
| ConfigChangeProbe | interaction (mixed) | A newly added member gets a probe carrying the last entry. It checks the `Next=LastIndex` and `sendIfEmpty=false` changes together. |
| AutoLeaveProgress | liveness (requirement, unchecked) | An auto-leave joint config is eventually left. |
| ProgressNextBounds | structural | A leader's peer `Next` stays in `1..Last+1`. |
| 5 canaries | model-internal | `AutoLeaveLeaderChangeNotReached`, `EarlyAdvanceJointCrossingNotReached`, `JointAdmissionRefusalNotReached`, `TransfereeDemotionAbortNotReached`, `NewPeerProbeNotReached` |

**Unresolved:** `ConfChangeNeverQuotaRefused` (unknown). The new comment at raft.go:1609 conflicts with the code at raft.go:1616 and the test, which only exempt empty payloads. It is checked only in a non-gating candidate cfg.

**Kept (64):** every other annotated property. All 37 annotated entries whose `watch` locations the patch touches were re-examined against the new source. Notable points:
- `CampaignDecisionEligibility`: recipient order is unobservable. The `numOfPendingConf` gap (D6) persists.
- `JointSnapshotMemberAcceptance`: only a comment in the restore pre-check changed, so D5 persists.
- `AckPreservation_LogUnchanged` and `ReadyOwnership_QuotaUntouched` (impl-abstraction): rechecked and still accurate.
- `NoUnexpectedFatal`: the expression is unchanged, but its `watch` list should gain advance, MsgProp and Simple (rule 7).

## Updated behaviors already covered by existing properties
- **Simple no longer swallows invariant failures.** `RequestCorrelatedConfigurationEffects` (`after=ConfigAfter(before,e)`, never EmptyConfig) and `ConfigurationOrigin` would flag the old wipe. In V03 the error panics, which `NoUnexpectedFatal` reports.
- **Probes emitted between Ready and Advance.** `AckPreservation_OutputPreserved` and `ReadyOwnership_OutputAccepted` make sure they are not lost; `PromiseBacking` checks their commit prefix is on disk.
- **Quota reorder and zero-payload exemption.** Covered by `QuotaIntegrity` and `ReadyOwnership_QuotaUntouched`.
- **Nil-data auto-leave entry.** Covered by `AckPreservation_LogUnchanged` and the EffectContract origin clause.
- **`pendingConfIndex` bump for auto-leave.** Covered by `ConfigurationTransitionSafety` and the new `PendingConfInLog` clause.
- **Sorted vote requests.** `CampaignDecisionEligibility` compares a multiset, so order does not matter.

## Suspected defects (must not be hidden by property edits)
| ID | Summary | Observed by |
|---|---|---|
| D1 | A leader elected with `applied == lastIndex` (= `pendingConfIndex`, raft.go:752) never auto-leaves, because raft.go:567 uses `<`. | AutoLeaveAdvance_V03, AutoLeaveProgress |
| D2 | If Advance runs before ApplyConfChange (allowed by README.md:122), the cursor crosses the joint entry while AutoLeave is still false, and the crossing never recurs. | AutoLeaveAdvance_V03, AutoLeaveProgress |
| D3 | Under the same early-Advance pattern, a second leave entry is appended while the first is unapplied; applying it hits "can't leave a non-joint config" and panics. | AutoLeaveAdvance_V03, CommittedConfigEntriesJointConsistent, CTS_AutoLeave, NoUnexpectedFatal |
| D4 | The doc comment "Configuration changes are never refused" disagrees with the code, which only exempts empty payloads. | ConfChangeNeverQuotaRefused (candidate) |
| D5 | (V02) The restore pre-check ignores outgoing-only members. | JointSnapshotMemberAcceptance |
| D6 | (V02) `numOfPendingConf` ignores ConfChangeV2, which now includes auto-leave entries. | CampaignDecisionEligibility |
| D7 | An empty ConfChangeV2 with a non-Auto transition is admitted while joint (leave detected by `len(Changes)==0`) but routed to EnterJoint at apply, where it panics. | ProposalConfigurationDecisions_V03, CommittedConfigEntriesJointConsistent |
| D8 | With early Advance, a simple change can be admitted after an unapplied joint entry; applying it panics. | CommittedConfigEntriesJointConsistent, NoUnexpectedFatal |

## Unresolved obligations
- **U1, D4:** need a test or doc on whether conf changes with payload are quota-droppable.
- **U2:** the outcome of an empty non-Auto ConfChangeV2 outside a joint config. The code refuses it, but the docs call it enter-joint.
- **U3:** whether README.md:122 early Advance is legal for Readies that contain conf entries. This decides whether D2, D3 and D8 are code defects or caller-contract violations.
- **U4:** the general log-order applicability clause of `CommittedConfigEntriesJointConsistent` is still labelled unknown.
- **U5:** the model must change before these properties mean anything.
  - Next=Last, the probe else-branch, and the VoterIDs-based transfer abort.
  - In AdvanceCore: edge trigger, reduce-first ordering, `pendingConf` bump, Fatal on refusal, and `AutoLeaveWeight=0`.
  - RewriteConf joint/leave refusals, and the quota rule requiring Weight>0.
  - New observer fields: `joint`, outcome entries, autoLeave check fields, and the effect probe/transfer fields.
  - Trace replay depends on all of these.
- **U6:** retarget `Update.tla`'s focus to the V03 actions, then add the aliases and hunt cfgs (see `cfg_plan`). Enable `NoUnexpectedFatal` in `Update_full.cfg`.
- **U7:** refresh the ledger. Line references have shifted (for example, TestStepIgnoreConfig is now at raft_test.go:3056), and NoUnexpectedFatal's `watch` list has gaps.
- **U8:** liveness is still unchecked under finite budgets.
- **U9:** `ConfigurationTransitionSafety` and its new `_AutoLeave` companion may flag a new leader committing two conf entries in one step under its pre-joint config. This may be pre-existing and safe by quorum overlap; validation must classify it before anything is weakened.
