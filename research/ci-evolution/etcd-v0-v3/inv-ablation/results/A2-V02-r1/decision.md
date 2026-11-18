# Invariant maintenance for the etcd-raft update (old → new)

## What the update changes

| Change | Effect on the suite |
|---|---|
| **Learners can vote** (`raft.go` Step: the learner early-return is gone, replaced by a design comment; `TestLearnerCannotVote` → `TestLearnerCanVote`) | Relaxes `VoteContract` and `LearnerEligibility` |
| **`RawNode.Ready()` now consumes output** (`readyWithoutAccept` + `acceptReady`); **`Advance()` no longer clears it** (`TestRawNodeConsumeReady`) | Changes `ReadyOwnership`; adds an Advance-retention obligation; migrates the `lostReads` observer |
| **Snapshot restore and restart rebuild the full joint ConfState** (`confchange.Restore` + `assertConfStatesEquivalent`) | Already required by `JointSnapshotRecovery` and `ConfigurationOrigin`, which are **kept**. The old code violated them; the new code satisfies them. |
| ConfState renames, `Visit` order, logger mutex, quorum slice refactor, `node.go` plumbing, `NewRawNode` ID-0 panic (still enforced by `validate()`) | Representation only, or not observable. No property edit. |

## Final decisions

No decision changed from `decision.initial.json`.

| Property | Decision | Kind | Key evidence |
|---|---|---|---|
| `VoteDecisionEligibility` / `VoteContract` | **modify**: drop `~o.learner` from `grant` and `(~stale /\ o.learner)` from `silence` | semantic relaxation | E1, E1b, E2a–e |
| `LearnerEligibility` | **modify**: `\A x\in history.campaigns:~x.learner` (grant conjunct removed) | semantic relaxation | E3, E3c |
| `ReadyOwnership` (`UpdateReadyOwnership`) | **modify**: every Ready leaves `out=EmptyBag`, `readStates=<<>>`, quota unchanged | semantic | E4, E4b, E4c, E5r |
| `AdvanceOutputRetention` | **add**: `\A a\in history.acks: a.outBefore \sqsubseteq a.outAfter /\ Covers(a.readsAfter,a.readsBefore)`; acks gain out/reads fields | semantic strengthening + observer extension | E5, E5r, E5c, E5n |
| `ReadyAccounting` (`lostReads` observer) | **modify the observer**: lost = `(SeqSet(r.readStates)\SeqSet(a.readStates))\SeqSet(app.reads)`; predicate text unchanged | observer migration | E6, E6c, E6b |
| `JointSnapshotRecovery`, `ConfigurationOrigin` | **keep** | unchanged requirement | E7, E8 |
| `JointRecoveryNotReached` (canary) | **modify**: the witness is "a joint config was recovered", not "it was lost" | canary (not a safety property) | E9 (E9b: hunt found no witness) |
| `ElectionSafety`, `CampaignDecisionEligibility` | **keep**; both catch pre-existing defects (below) | unchanged | E15, E12 |
| All other properties | **keep** | safety controls | E11d |

The required model migrations are in `evidence/tla/Proposed.tla` (diff: `evidence/logs/base_vs_Proposed.diff`):
- `StepVote` loses its learner guard.
- `RestoreProjection(cfg)==cfg`, and progress is tracked for all members.
- `ProtocolReady` accepts output for every node.
- `AdvanceCore` no longer clears output.

## Executed evidence

TLC evaluated the actual old and proposed definitions; the Go tests ran on copies of both trees.

- **Learner vote (E1, E1b).** Pre-state as in `TestLearnerCanVote`; the observation comes from each model's `Step` and `VoteObservation`.
  - The new grant: old FALSE, proposed TRUE.
  - The old silence: old TRUE, proposed FALSE.
  - Go: the old code is silent; the new code grants.
- **Learner-vote controls (E2a–e).** The proposed contract still rejects a learner grant when:
  - the learner already voted for someone else, the candidate's log is stale, or the leader lease applies;
  - the implementation makes learners always reject. This is an executed mutant, and the upstream `TestLearnerCanVote` **passes** against it.
- **Learners still cannot campaign (E3c).** True in both the model and the code.
- **Ready/Advance (E4–E6, E5r).** These are full action runs: Ready → persist/install/publish/queue → new output arrives (injected, or a real `Receive` of a leader heartbeat) → Advance.
  - The proposed `ReadyOwnership` accepts only the consuming Ready.
  - `AdvanceOutputRetention` is FALSE for the old raw `AdvanceCore` and TRUE for the new one. The old core drops the heartbeat response before it reaches the wire, exactly as old `RawNode.Advance` drops it in Go.
  - The retention property still accepts a legitimate auto-leave Advance.
  - The **old `lostReads` observer reports a retained read as lost**: same text, different meaning. The migrated observer still reports a real loss.
- **Joint restore and restart (E7, E8).**
  - Old model and old code: `voters=(1 2)` only, so `JointSnapshotRecovery` and `ConfigurationOrigin` are FALSE.
  - New model and new code: `(1 2)&&(1 2 3) learners_next=(3) autoleave` with `Equivalent()==nil`, so both are TRUE.
  - Forged partial restores (autoLeave dropped, or learnersNext dropped) are still rejected.
- **Reachable states (E11).** `PUpdate.tla` is MC/Update rebased on `Proposed`.
  - Plain random simulation turned out to be **vacuous**: the injected tick/campaign budgets are spent before any node applies its bootstrap entries, so no election or message ever happens (E11a).
  - A guarded subset of `FullUpdateNext` fixes this; canaries show it reaches a raw Ready with output (depth 24) and an Advance with pending output (depths 67 and 81).
  - Final run (E11d, `EarlyAdvance=FALSE`): **10.3M states, 2,264 traces, no violation** of any edited or kept property in the run.
  - The old `ReadyOwnership` text fails on a reachable proposed-model state (depth 38).
  - **No learner grant (E13) and no joint recovery (E9b) was reached** by any search. For those edits, the evidence is the mapped witnesses plus Go.

## Suspected defects (not hidden by any property edit)

1. **New, pre-existing: campaigning over a pending `ConfChangeV2`.** `numOfPendingConf` counts only `EntryConfChange`, so a node campaigns while a committed `ConfChangeV2` is still unapplied. Reproduced in the old and new code and in both models (E12). Caught by the unchanged `CampaignDecisionEligibility`, which the old `Update_full.cfg` did not enable.
2. **New, pre-existing: two leaders in one term after restart replay.** A node restarts without a snapshot and replays its bootstrap conf entries. The caller calls Advance early, which `node.go:164-167` allows. After applying only `AddNode(self)`, the node wins term 2 **alone**, while nodes 2 and 3 can elect another leader in the same term. Reproduced in the old and new code (Go: `StateLeader term=2`) and in both models (E15). Caught by `ElectionSafety`; `QuorumAccounting` does not catch it.
3. **An outgoing-only voter ignores a joint snapshot** (`restore()` checks only Voters and Learners). Same in the old and new code (E10). This is a progress problem.
4. **Old model/observer divergence.** The old model dropped raw read states at Advance even when the Ready carried none, and the old observer masked it; the old Go code keeps them (E6b).
5. **`TestLearnerCanVote` cannot tell a grant from a rejection** (E2e).

## Unresolved

- Reachability of learner grants and of joint recovery in the model (E13, E9b).
- The liveness motivation for learner voting (`ElectionProgress` is not checked).
- Snapshot acceptance by outgoing-only voters.
- Whether defect 2 is a code bug or a caller-contract gap: `NewRawNode`'s doc discourages log-based bootstrap.
- Trace instrumentation must follow the field renames and the new Ready/Advance ownership.

## Initial → final

All property decisions are unchanged. What the evidence added:
- Concrete separating states for every edit.
- Two pre-existing safety-relevant defects found by simulation (E12, E15). They are recorded and do not justify weakening any property.
- Confirmation of the suspected test weakness (E2e) and of the old observer masking (E6b).
- The finding that plain random simulation of this spec is vacuous unless the injected actions are guarded (E11a).
