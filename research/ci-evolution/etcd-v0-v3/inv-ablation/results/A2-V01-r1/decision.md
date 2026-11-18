# Invariant maintenance: etcd-raft joint consensus (ConfChangeV2) update

**Overall: modify.** The update replaces single-voter-set configurations with joint configurations: incoming/outgoing voters, learners, learnersNext and autoLeave. It also changes what single configuration changes do:
- AddLearner on an existing voter now demotes it.
- A change that would leave zero voters is refused (the code panics).
- Removing an unknown peer is now a no-op.

The core Raft safety properties do not change. Every property that reads `config.voters` or `ConfigOf` has to move to the joint representation. In several cases the old text becomes too weak in joint configurations (it only checks an incoming majority), too strong (it rejects voters that are only in the outgoing set), or both. Two new obligations are needed.

The proposed definitions are in `evidence/tla/Proposed.tla` (marked `PROPOSED`). Evidence: `out/evidence.json` has 39 executed checks. TLC evaluated both `base.tla` (a verbatim copy) and `Proposed.tla` on witness states mapped from Go runs of the old and new code.

## Decisions

| Property | Decision | Kind | Key executed evidence |
|---|---|---|---|
| ElectionSafety, LogMatching, LeaderCompleteness, CommittedHistory, AppliedAgreement | keep | unchanged controls | Same values in old and new, including an injected violation (EV-CTRL) |
| DurableObligations (observer) | modify | observer → joint quorum | Old records an obligation that is durable on an incoming majority only (EV-E14) |
| QuorumAccounting | modify | joint quorum; old was too weak **and** too strong | Incoming-only win/commit: old T / new F (code stays Candidate). Legit joint commit with an outgoing-only ack: old F / new T (EV-E4a–d) |
| ConfigurationTransitionSafety | modify | joint comparison + bootstrap exemption keyed on `IsBootstrap` instead of `id#0` | Real auto-leave trace {L,L'}: old T / new F. Each half of the edit alone stays T (EV-E5a–c) |
| ConfigurationOrigin | keep text, migrate `ConfigOf` | representation | Legit joint restore: old F / new T. The code's restore drops outgoing and is caught: new F (EV-E6a,b) |
| EffectContract (RequestCorrelatedConfigurationEffects) | modify | **semantic** | Demotion: old F / new T. Last-voter refusal: old F / new T. Enter/leave joint and staged learner: new T. Second auto-leave: new F (EV-E1–E3, E8, E11) |
| ConfigurationChangeOverlap | **add** | new obligation (quorum overlap of consecutive configs) | (s1)→() and a two-voter change without joint: F. All legit transitions: T (EV-OVL) |
| PendingConfigurationDiscipline | **add** | new obligation (one unapplied conf entry, now also covering auto-leave) | Go trace with L and L' unapplied: F. Inherited unapplied entries: T (EV-E13a,b) |
| TypeOK (+JointConfigWellFormed) | modify | structural (confchange.checkInvariants) | Legit joint: old F / new T. Three malformed configs: old T / new F (EV-E11t) |
| CampaignContract | modify | joint voters; `pending` text unchanged but ConfKinds now includes V2 | (1)&&(1 2) campaign: old F / new T. Pending V2 campaign (new code): old T / new F (EV-E7a–c) |
| TransferContract | modify | membership includes outgoing | Transfer to an outgoing-only voter: old F / new T. Learner target still rejected (EV-E10a) |
| ProposalContract | modify | membership includes outgoing; V2 content compared | Outgoing-only leader accepts: old F / new T. Altered V2 changes: old T / new F (EV-E10b,c) |
| ReadBasis | modify | joint quorum; leader may be outgoing-only | Incoming-only acks pass the old text even on migrated helpers (too weak). Outgoing-only leader: old F / new T (EV-E9a,b) |
| VoteContract, LearnerEligibility | keep | learner flag = membership in `learners` (staged learners still vote) | Same values in old and new; control rejected (EV-E12) |
| SnapshotBacking, ReplicationEvidence, OutcomeSoundness, QuotaIntegrity, AckPreservation, ReadyAccounting, PromiseBacking, VoteRecovery, RecoveryBacking, ReadApplication, ReadCorrelation, NoUnexpectedFatal, LogStructure | keep | joint meaning comes through the migrated helpers | SnapshotValid on a joint snapshot: new T (EV-E6c). NoUnexpectedFatal is F on every confchange panic. Random simulation shows no violations (EV-SIM, sanity only) |

## Defects in the new code (not hidden by property edits)
- **D1 (confirmed, EV-E7b):** `numOfPendingConf` ignores `EntryConfChangeV2`. A node with a committed but unapplied V2 change campaigns, which violates CampaignContract.
- **D2 (confirmed, EV-E8b/E13a/E5a):** the auto-leave in `raft.advance` sets `pendingConfIndex` only when the append fails. With paginated Readys the leader appends a second leave-joint entry. Applying it panics with "can't leave a non-joint config".
- **D3 (confirmed, EV-E6a):** `restore` and `newRaft` ignore `NodesJoint`, `LearnersNext` and `AutoLeave`, so the joint config silently collapses to its incoming half. A node that is only an outgoing voter rejects the snapshot.
- **D4 (behaviour confirmed, requirement unresolved):** invalid configuration proposals are accepted and committed, then panic on every node at apply time. Examples: leaving joint when not joint, entering joint when already joint, a simple change while joint, and leaving zero voters. NoUnexpectedFatal flags this.
- D5–D7 (not executed): the leader can demote itself and keep leading as a learner; a latent nil-error path in `Simple`; `Config.Clone` drops AutoLeave, and promotion no longer sets RecentActive.

## Changes from the initial decision
- **No property decision changed.**
- QuorumAccounting: the rationale now also records that the old `matches ⊆ voters` is too strong for joint commits (EV-E4d). The expression is unchanged.
- ReadBasis: one of my own evidence controls was wrong. Acks {1,2} *are* a joint quorum of (1 2)&&(1 2 3). I replaced it with {1,3}, which the proposed property rejects (EV-E9b, verdict "revised"). The expression is unchanged.
- D1–D3 went from suspected to confirmed by executed Go tests. D3 is broader than first thought: AutoLeave is also dropped, and the snapshot is rejected by outgoing-only nodes.
- New unresolved items:
  - The model's client actions cannot yet generate joint configurations. Invoke only creates empty V2 lists, so the simulation does not exercise joint semantics.
  - The model still allows core calls between a RawNode Ready and Advance, which the new contract makes illegal.

## Still unresolved
- Whether raft must filter invalid configuration proposals (D4) or whether avoiding them is the caller's job.
- Auto-leave progress (that a joint config is eventually left) is a liveness property.
- The `node.go` proposal-blocking rule has no property.
- The model actions still need: V2 client requests, the auto-leave step (`AutoLeaveCore` is provided, with the required `pendingConf` bump), fresh RawNodes starting at term 0, and the new RawNode caller contract.
