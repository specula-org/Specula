# Invariant maintenance decision: etcd-raft joint consensus / ConfChangeV2 update

**Overall: MODIFY.** Keep 19, modify 10, add 4, remove 0. Three observers also need migrating.
Nothing was executed (no tests, no TLC). This is the frozen initial judgment. Full predicates and witnesses are in `decision.json`. The shared TLA+ helper definitions are in `shared_definitions` there.

## What changed in the source
- **Joint consensus and ConfChangeV2.** A configuration is now `in`/`out` voters plus `learners`, `LearnersNext` and `AutoLeave`. There are three transitions: Simple, EnterJoint and LeaveJoint. A leader proposes LeaveJoint by itself from `raft.advance`.
- **Simple-change semantics are different.**
  - AddLearner on a voter now demotes it.
  - Removing an unknown id is a no-op.
  - Zero incoming voters, or more than one voter changing, is an error and causes a panic.
  - `maybeCommit` now runs after every conf change, not only removals.
- **All quorum decisions are joint:** commit, vote tally, CheckQuorum, read-index acks, and the singleton read.
- **`node.run` is rebuilt on RawNode.**
  - Quota is released at Advance.
  - RawNode `Ready()` no longer changes state; Advance clears messages and read states.
  - After a restart, HardState is not re-emitted.
  - `NewRawNode` takes no peers; `Bootstrap` replaces that.

## Decisions on old properties
| Property | Decision | Kind |
|---|---|---|
| ElectionSafety, LogMatching, LeaderCompleteness, CommittedHistory, AppliedAgreement | keep | unchanged |
| VoteRecovery, RecoveryBacking, PromiseBacking | keep | unchanged |
| LearnerEligibility, VoteDecisionEligibility | keep | unchanged ("learner" means `config.learners` only, not LearnersNext) |
| ReplicationEvidence, ReadyAccounting, QuotaIntegrity, OutcomeSoundness | keep | unchanged (OutcomeSoundness uses a migrated RewriteConf) |
| ReadApplication, ReadCorrelation, NoUnexpectedFatal, LogStructure | keep | unchanged |
| TransferDecisionEligibility | keep | unchanged (voters = in ∪ out) |
| RequestCorrelatedConfigurationEffects | **modify** | semantic: demotion, no-op unknown removal, invalid change is fatal, joint transitions, raft-generated id-0 LeaveJoint |
| AckPreservation | **modify** | semantic: Advance may append exactly one raft-generated LeaveJoint, only under the auto-leave trigger |
| QuorumAccounting | **modify** | semantic: `JointWon` |
| ReadBasis | **modify** | semantic: joint ack quorum; singleton means one incoming voter and no outgoing |
| ConfigurationOrigin, SnapshotBacking | **modify** | representation: `ConfigOf2` over the full joint config |
| ConfigurationTransitionSafety | **modify** | representation: compares the full config; exempts only real bootstrap entries, not every id-0 entry |
| CampaignDecisionEligibility | **modify** | representation: pending scan over V1+V2 kinds; voters = in ∪ out |
| ProposalConfigurationDecisions | **modify** | representation: rewrite rule covers V2 entries |
| TypeOK | **modify** | representation: new config record shape |

Observers to migrate:
- `DurableObligations` must use `JointWon`.
- The ghost records (`wins`, `commitUses`, Effect, Ack, Campaign, Read records) must store the full config. The Effect record also needs `fatal`; the Ack record also needs role, term and the pendingConf index before and after.
- `RewriteConf` must cover V2 entries.

## Added properties
- **PendingConfCoverage.** Every unapplied conf entry in a leader's log has index ≤ `pendingConf`. This is the documented contract at `raft.go:280-286`. It also closes an old gap: ProposalContract reads `pendingConf` to justify itself.
- **JointConfigWellFormed.** The `confchange.checkInvariants` rules hold, and once any conf entry has been applied there is never a config with zero incoming voters.
- **RaftGeneratedConfChangeApplicability.** Raft-generated conf entries (bootstrap entries and auto-leave) always apply cleanly. Every auto-leave entry follows a joint prefix.
- **AutoLeaveInitiation.** A decision-time stand-in for the liveness requirement that the joint config is eventually left.

## Example disagreements (old vs new properties)
- **Demotion.** `AddLearner(s3)` with s3 a voter: the old EffectContract and ConfigurationOrigin flag the correct new result.
- **Valid joint win.** Config `in={s2,s3,s4}, out={s1,s2,s3}`, votes from `{s2,s3}`: this is a joint win, but old QuorumAccounting flags it.
- **Invalid joint win.** Config `in={s1,s4}, out={s1,s2,s3}`, votes from `{s1,s2,s3}`: this is not a joint win, but old QuorumAccounting accepts it.
- **Auto-leave append.** Advance on a leader whose joint config has auto-leave set appends one LeaveJoint: old AckPreservation flags it.
- **V2 proposal rewrite.** A V2 proposal arrives while a conf change is pending: the source rewrites it to a no-op, but the old ProposalContract expects it appended unchanged.

## Suspected defects (must stay visible)
- **D1 (high).** Auto-leave appends LeaveJoint without updating `pendingConfIndex` (`raft.go:561-581`).
  - A later Advance appends a second LeaveJoint. Applying it panics on every node ("can't leave a non-joint config").
  - The same gap lets user conf changes be admitted while the leave is pending.
  - `rawnode_test.go:316` asserts the un-updated value, so the test pins the defect.
  - Caught by: PendingConfCoverage, RaftGeneratedConfChangeApplicability, ConfigurationTransitionSafety, NoUnexpectedFatal.
- **D2 (medium).** `numOfPendingConf` ignores `EntryConfChangeV2` (`raft.go:1580`), so a node can campaign with a committed but unapplied V2 change. Caught by CampaignDecisionEligibility. Do not narrow it to V1.
- **D3 (high).** `restore()` and `newRaft(InitialState)` drop NodesJoint, LearnersNext and AutoLeave.
  - The restored node decides on the incoming half only. Example: a split-brain with two leaders in the same term in a 4-server model.
  - Caught by: ConfigurationOrigin, ElectionSafety, CommittedHistory.
  - The membership check also ignores NodesJoint, so an outgoing-only voter rejects every snapshot (liveness).
- **D4 (medium).** With early Advance, a user conf change can be admitted before the app has applied a committed EnterJoint. It then panics when applied inside the joint config. Caught by NoUnexpectedFatal.
- **Low severity, D5–D9:**
  - D5: `Simple` returns an empty config with a nil error when its invariant check fails (believed unreachable).
  - D6: `Config.Clone` drops `AutoLeave` (Status only).
  - D7: `StartNode` ignores Bootstrap's error, and the README is stale (empty-peers start now panics; V2 entries are never mentioned).
  - D8: Stepping a RawNode between Ready and Advance now loses messages and read states.
  - D9: Promoting a learner no longer marks it RecentActive.
- **D10 (model).** `base.tla` must be migrated faithfully, including the defects above. Idealising Restore, the Hup check or advance would hide D1–D3.

## Unresolved
1. Auto-leave liveness: no liveness properties are defined in `base.tla`.
2. Whether a caller conf change that was admitted must stay valid until it is applied (D4).
3. Semantics of cancelling a V2 change: zeroing every NodeID in an EnterJoint still enters the joint config.
4. How to model the RawNode rule "no state change between Ready and Advance".
5. Node proposal-channel gating after self-removal (no property; needs a model migration).
6. Snapshot catch-up for outgoing-only voters (liveness).
7. Joining-node initial term (0 vs 1) and Bootstrap.
8. Reads that never complete in single-voter joint configs such as `(s1)&&(s1)` (liveness).
9. The model's V2 workload and entry representation, which are needed before any witness above is reachable.
