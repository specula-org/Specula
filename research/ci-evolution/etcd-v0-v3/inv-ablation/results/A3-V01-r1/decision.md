# Invariant maintenance: etcd-raft update (Changer / joint consensus / RawNode Ready refactor)

**Overall: modify.** The old suite stays the backbone.

- **Kept: 21 properties.** Two of them, ConfigurationOrigin and SnapshotBacking, change meaning only through the migrated helper.
- **Modified: 7 properties.** EffectContract, NoUnexpectedFatal and AckPreservation change because the requirement changed. ConfigurationTransitionSafety, QuorumAccounting, ReadBasis and TypeOK are migrated to joint configurations.
- **Migrated helpers:** ConfigAfter/ConfigOf, ConfKinds and the joint-quorum helpers.
- **Unresolved:** CampaignDecisionEligibility.

Every edit and every kept property touched by the update was executed in two ways:

- **TLC:** 129 TLC checks evaluate the actual old (`base.tla`) and proposed (`evidence/Proposed.tla`) definitions on concrete states. Every check printed the claimed value; there were no mismatches (`evidence/tlc_witness.log`).
- **Go:** 23 probes drive the real old and new code to the matching states (`evidence/go_new.log`, `evidence/go_old.log`).

Two random simulations (8000 traces each, about 380k states) of the old and migrated models raised no violations. That is a smoke test only: random traces rarely apply conf changes.

## What the update changes (relevant to the suite)

| Behaviour | Old code | New code | Requirement source |
|---|---|---|---|
| AddLearner on an existing voter | ignored | **demotes**, keeps Progress | raft_test.go:3120-3128, simple_promote_demote.txt:34-41 |
| Remove/demote the last voter | voters = {} | **panic** "removed all voters" | raft_test.go:3183-3190, 3207-3214 |
| Remove an unknown peer | panic | no-op | simple_idempotency.txt:66-69, joint_idempotency.txt:1-2 |
| Joint consensus (V2) | n/a | two-majority quorums, LearnersNext, AutoLeave | raft.proto:85-114, 153-157 |
| Auto-leave | n/a | Advance appends an empty ConfChangeV2 | rawnode_test.go:322-357 |
| RawNode restart, empty log | term reset to 1, vote lost | persisted term/vote kept | README.md:116-118 |
| RawNode Ready | clears msgs/quota | read-only; work happens at Advance; Step between Ready and Advance is illegal | rawnode.go:120-129 |

## Final decisions

| Property / helper | Decision | Kind | Evidence |
|---|---|---|---|
| RequestCorrelatedConfigurationEffects (EffectContract) | **modify** | semantic + observer (`fatal`) | EV01-EV04, EV08 |
| ConfigAfter / ConfigOf (shared helper) | **modify** | semantic helper migration | EV09, EV11-EV13 |
| ConfigurationOrigin | keep (text; meaning via helper) | unchanged | EV09, EV10, EV35 |
| SnapshotBacking | keep (text; meaning via helper) | unchanged | EV11, EV35 |
| ConfigurationTransitionSafety | **modify** | representation (joint quorum, bootstrap-only exemption) | EV12-EV14 |
| QuorumAccounting | **modify** | strengthening (CfgWon) + observer `config` | EV18-EV20, EV29 |
| ReadBasis | **modify** | representation + strengthening | EV21, EV22 |
| Joint helpers/observers (AllVoters, CfgWon, QuorumIndex, Members, DurableObligations, …) | **modify** | representation | EV23 |
| AckPreservation | **modify** | relaxation (one raft-initiated LeaveJoint) + observer | EV15-EV17 |
| ConfKinds (+V2 kinds) | **modify** | representation | EV25, EV27, EV28 |
| CampaignDecisionEligibility | **unresolved** (text kept, not weakened) | — | EV25, EV26 |
| ProposalConfigurationDecisions | keep | unchanged | EV27, EV28 |
| VoteRecovery | keep | unchanged (flags the old defect) | EV24 |
| LearnerEligibility, VoteDecisionEligibility, TransferDecisionEligibility | keep | unchanged | EV29, EV31, EV32 |
| NoUnexpectedFatal | **modify** | relaxation: `{"removed all voters"}` only | EV05-EV07 |
| ReadyAccounting | keep (+ RawIdle model guard) | unchanged | EV34 |
| QuotaIntegrity | keep | unchanged | EV33 |
| OutcomeSoundness | keep (demoted-leader aspect unresolved) | unchanged | EV30 |
| TypeOK | **modify** | structural joint clauses | EV38 |
| WinnerIsVoter (candidate) | **unresolved**, not adopted | — | EV29 |
| Status/Config.Clone | **unresolved** (no observer) | — | EV36 |
| ElectionSafety, LogMatching, LeaderCompleteness, CommittedHistory, AppliedAgreement, RecoveryBacking, PromiseBacking, ReplicationEvidence, ReadApplication, ReadCorrelation, LogStructure | keep (controls) | unchanged | EV37, EV39 |

The model also had to change where it would otherwise misrepresent the new code. These are model changes, not property edits: `ApplyConfCore`, `AdvanceCore` (including the auto-leave behaviour as implemented), RawNode `Ready`, the `RawIdle` caller guard, `RestartCore`, `Restore`, `StepHup` and the proposal-blocking rule. Each change that is executed agrees with a Go probe (the `W*.model.*` checks). **The workload still issues only V1 changes, so MC never generates joint states.** That is a stated coverage gap.

## Changes between the initial and final decisions

1. **ConfigurationTransitionSafety.** My initial predicate kept the old `id # 0` exemption. TLC shows it **accepts** two raft-initiated LeaveJoint entries committed together (W5i = TRUE), because auto-leave entries also have id 0. The final predicate exempts only bootstrap `AddVoter` entries, and it rejects that state (EV13).
2. **NoUnexpectedFatal: keep → modify.** The strict text rejects the zero-voter refusal panic that the tests require. Per the decision table that state is "impl produces / allowed", so I relaxed it for exactly that one reason string. Other panics (for example "can't leave a non-joint config") are still rejected (EV05, EV06).
3. **EffectContract is stronger than initially proposed.** Non-refused changes must now also have `fatal = ""`. The old contract could not see the old "remove unknown peer" panic (EV08). Raft-initiated LeaveJoint entries are exempt from request correlation.
4. **TypeOK: keep → modify.** It now includes the joint well-formedness that `confchange.checkInvariants` states (EV38).
5. **New unresolved entries.** WinnerIsVoter (a demoted candidate wins as a learner, Go N13) and the Status/Clone observer (Go N9).

All other initial decisions were confirmed by their separating states. Examples: old FALSE / new TRUE on demotion (EV01, EV09, EV12); old TRUE / new FALSE on incoming-only joint quorums (EV18, EV19).

## Bug candidates: implementation produces it, requirement forbids it

The stronger properties are kept; none was edited to accept these states.

- **B1: duplicate auto-leave proposals** (`raft.go:572-580`). `pendingConfIndex` is bumped only when the append is *refused*. A second Advance that applies entries appends a second LeaveJoint, and applying it panics "can't leave a non-joint config" (Go N6). This is forbidden by doc.go:184-188, node.go:136-139 and confchange.go:81-82. It is detected by the migrated ConfigurationTransitionSafety (EV13), by AckPreservation, whose relaxation admits only a single leave (EV16), and by NoUnexpectedFatal (EV06). The old suite missed it.
- **B2: joint ConfState lost on restore and restart** (`raft.go:1418-1423`, `330-341`). NodesJoint, LearnersNext and AutoLeave are dropped (Go N8). This is forbidden by raft.proto:99-114, node.go:173-174 and raft.go:1416. ConfigurationOrigin (kept) rejects it; the old representation cannot separate the buggy restore from the correct one (EV35).
- **B3: `tracker.Config.Clone` drops AutoLeave**, so `Status().Config` misreports the config (Go N9; tracker.go:94). No spec observer can see this.
- **B6 (model environment, not library):** the old model allowed Step/Tick/Propose on a RawNode between Ready and Advance, which is now illegal (rawnode.go:122-129) and loses reads (Go N12). I fixed it with a model guard; ReadyAccounting is kept unchanged (EV34).

## Suspected, unresolved (requirement unknown)

These are recorded, not edited toward the implementation.

- **B4:** `numOfPendingConf` ignores V2 entries. A node campaigns while a committed V2 change is unapplied (Go N7), unlike V1. CampaignContract keeps the stronger form (EV25).
- **B5:** demotion is reachable although raft.go:1478-1489 claims it is prevented. A demoted candidate can win as a learner (N13), and a demoted leader keeps leading and accepting proposals (N15). EV29, EV30.

## Other findings

- **B7:** a pre-existing OLD-code defect that the update fixes. The old RawNode reset term/vote when the log was empty (Go O5). The kept VoteRecovery flags the old code and accepts the new code (EV24).
- **B8, latent, not executed:** `Changer.Simple` can return an empty config with a nil error (confchange.go:148-150).

## Remaining obligations

- Add V2/joint requests to the workload so MC exercises the joint properties. Today they are checked only on constructed states.
- Requirement text is needed for B4 and B5.
- The simulations did not measure how often conf-change paths were covered.

## Reproduce

```
cd evidence && java -cp /tmp/tools/tla2tools.jar:/tmp/tools/CommunityModules-deps.jar tlc2.TLC -config Witness.cfg -workers 1 -metadir tlc_meta Witness.tla
cd evidence/new_tree && GOFLAGS=-mod=mod GOPROXY=off go test -vet=off -v -run TestEv ./ ./quorum/
cd evidence/old_tree && GOFLAGS=-mod=mod GOPROXY=off go test -vet=off -v -run TestEv .
```

Proposed definitions: `evidence/Proposed.tla` (diff in `evidence/Proposed.diff`). Per-check records: `out/evidence.json`. Final decisions: `out/decision.json`. Frozen first judgment: `out/decision.initial.json`.
