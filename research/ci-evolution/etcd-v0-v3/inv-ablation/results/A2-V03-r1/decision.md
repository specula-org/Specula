# Invariant maintenance: etcd-raft update (auto-leave, conf-change admission, transfer abort)

**Overall: modify.** Of the old properties, 4 need edits (one is an observer-only migration), 1 property is added, and all others are kept. Every update-related edit was tested with executed concrete-state evidence: 45 TLC witness runs over Go-mapped states, 7 Go scenarios run on both trees, and forbidden-observation controls. All 32 evidence records match the values predicted before the runs.

Process note: before `decision.initial.json` was written, one no-op `echo` command ran by mistake. It read and changed nothing. The initial file was not edited afterwards.

## Decisions

| Property | Decision | Kind |
|---|---|---|
| `AutoLeaveAdvance` | modify | semantic + observer migration |
| `autoLeaveChecks` observer | modify | observer only |
| `ProposalContract` (`ProposalConfigurationDecisions`) | modify | semantic + observer (`joint`) |
| `ExpectedDecision` (`OutcomeSoundness`) | modify | semantic relaxation + observer weight |
| `TransferTargetVoter` | **add** | strengthening |
| Everything else (`AckPreservation`, `QuotaIntegrity`, `EffectContract`, `JointConfigurationShape`, `CampaignContract`, `NoUnexpectedFatal`, standard safety…) | keep | unchanged; controls |

### AutoLeaveAdvance (modify)
- **Old rule:** every eligible Advance must append a leave, unless a quota drop happened.
- **Proposed rule:** when an Advance is "due" (leader, autoLeave config, cursor > 0, cursor ≥ pendingConf):
  - if a leave already sits in the log after the last applied conf entry, nothing may be appended;
  - otherwise exactly one id-0 leave is appended, it is never quota-refused, and `pendingConf` must cover it.
- **Observer:** adds `cursor`, `cfgLen`, `appliedOK`; the old fields are unchanged.

Evidence (old → proposed values, from TLC):

| Witness | Old | Proposed | Source |
|---|---|---|---|
| D1: old code duplicates the leave under the ordinary schedule | TRUE | FALSE | Go: panic "can't leave a non-joint config" |
| D1: new code (no append) | TRUE | TRUE | |
| D1 with corrected behavior | FALSE | TRUE | relaxation |
| E: early Advance, new **and** old code duplicate the leave | TRUE | FALSE | Go: panic in both trees |
| E with corrected behavior | FALSE | TRUE | |
| D2: old code drops auto-leave for quota | TRUE | FALSE | |
| D2: new code | TRUE | TRUE | |
| D3: new code never auto-leaves after an election with applied==pendingConf | FALSE | FALSE | edit does not hide the defect |
| D3: old code appends but doesn't bump pendingConf | TRUE | FALSE | |

### ProposalContract / ExpectedDecision (modify)
- **Admission:** a conf entry is refused if a conf change is pending, or `joint ∧ ¬IsLeave(e)`, or `¬joint ∧ empty V2`. Only *admitted* entries make later entries in the batch pending.
- **Quota:** refuse only when `quota>0 ∧ weight>0 ∧ quota+weight>Max`.

| Witness | Old code (old/proposed) | New code (old/proposed) | Notes |
|---|---|---|---|
| P1: joint config + simple add | TRUE/FALSE | FALSE/TRUE | old code panics at apply |
| P2: non-joint leave | TRUE/FALSE | FALSE/TRUE | old code panics at apply |
| C1, C2: legitimate allowed controls | TRUE/TRUE | TRUE/TRUE | |
| P4: zero-weight proposal over quota | TRUE/FALSE | FALSE/TRUE | relaxation |
| Q1 and hypothetical weight-1 acceptance | — | — | stay rejected by both contracts (forbidden control) |
| P5: joint config + empty JointExplicit | TRUE/FALSE | TRUE/FALSE | both versions admit it, then panic "config is already joint"; flagged, not weakened |
| P6: non-joint + empty JointExplicit | TRUE/FALSE | FALSE/TRUE | new code refuses it |

P6 is a judgment call. It follows the new code's `len(Changes)==0` and "refusing empty conf change" design. Admitting it was harmless in the old code, and the testdata only exercises the Auto case.

### TransferTargetVoter (add)
A promotable leader's non-zero transfer target must be in `VoterIDs(config)`.
- Old model after demoting s3: transfer stays s3 → FALSE. Go old tree: transferee=3.
- New model: TRUE. Go new tree: transferee=0.
- Controls: an outgoing-only voter during joint and a voter are TRUE; a learner and a non-member are FALSE.

### Unchanged-property controls
On all 45 post-states, 15 unchanged properties are TRUE and identical when evaluated through `base` and `Proposed`, including AckPreservation, QuotaIntegrity, EffectContract, LogMatching, CommittedHistory and NoUnexpectedFatal. Every witness produced a non-empty observation record of the relevant kind.

## Implementation defects found (not hidden by property edits)
1. **New code: no auto-leave after an election.** A leader elected with `applied == pendingConfIndex` in an autoLeave joint config never auto-leaves, because `oldApplied < pendingConfIndex` is false. Go shows the config still joint after 3 more rounds.
2. **New and old code: duplicate leave with early Advance.** If Advance runs before ApplyConfChange of the leave entry, a second leave is appended and applying it panics. Early Advance is allowed by node.go and the README.
3. **New and old code: invalid admission.** An empty non-Auto V2 is admitted in a joint config and panics at apply.
4. **Suspected, not executed:** with early Advance, if the joint entry is applied after the crossing Advance, auto-leave never fires.

## Changes from the initial decision
- **OutcomeSoundness observer weight.** It is now computed from the contract's rewrite (`ContractEffective`), not from the migrated implementation `RewriteConf`. Reason: P5 showed the code-faithful rewrite differs from the contract, so an implementation-derived weight would let the oracle inherit implementation defects.
- **New unresolved obligation.** Bounded model checking of the edits on reachable states was **inconclusive and vacuous**. BFS was aborted at 18.6M states, and simulation covered 23M+ states. The auto-leave canary held throughout, so auto-leave was never reached, and these runs are not counted as support.
- **Observer field set.** Two diagnostic fields (`oldApplied`, `afterFatal`) were added to the auto-leave record; no property reads them.

Every other initial decision was confirmed unchanged.

## Remaining obligations
- A scenario-directed model check of the edited properties on reachable states.
- Probing of new replicas (`Next=lastIndex`, probe in `switchToConfig`) is liveness only; no property was added.
- The `ConfigurationTransitionSafety` id=0 exemption repair was not executed.
- "Admitted conf changes are applicable" is only partly covered (e.g. removing the last voter).
- Pre-existing and outside this update: `CampaignContract` counts V2 entries as pending conf, while `numOfPendingConf` counts only legacy entries.

## Artifacts
- `evidence/Proposed.tla`: edited properties, observers, and the model migration (`ImplModel` ∈ old/new/fixed).
- `evidence/EvWitness.tla`, `evidence/EvForbidden.tla`: witnesses and forbidden controls.
- `evidence/run_all.sh` and `evidence/cfg/`: run configurations.
- `evidence/logs/`: TLC and Go logs, plus `tlc_summary.txt`.
- `evidence/go/zz_evidence_test.go`: Go scenarios, run in `evidence/{old,new}tree`.
