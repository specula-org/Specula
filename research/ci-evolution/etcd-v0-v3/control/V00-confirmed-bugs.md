# Confirmation Report — etcd-raft

## Final Result

Reproduced bugs: 5 = 5 NEW + 0 KNOWN-unfixed + 0 KNOWN-fixed + 0 UNKNOWN
Masked live findings: 0
Env-limited findings: 0
False positives: 0
Dropped: 1
Needs more info: 0
Pending repair: 0
Incomplete: 0
Deferred: 0
Total disposition entries: 6
Dispositions: 6 total = 5 reproduced + 0 env-limited + 0 masked + 0 false-positive + 0 needs-more-info + 1 dropped + 0 pending-repair + 0 incomplete + 0 deferred
| Entry | Finding | Status | Counts as final bug? |
|---|---|---|---|
| 1 | CR-1 | REPRODUCED | yes |
| 2 | CR-2 | REPRODUCED | yes |
| 3 | CR-3 | REPRODUCED | yes |
| 4 | CR-4 | DROPPED | no |
| 5 | CR-5 | REPRODUCED | yes |
| 6 | CR-6 | REPRODUCED | yes |

## Entry 1: Protocol promises cross Ready, durability, and recovery boundaries

- **Finding ID**: CR-1
- **Status**: REPRODUCED
- **Debate**: not run
- **Transcript**: /home/ubuntu/specula-etcd-ci-init-20260912.FNeLj3NS/ci-clean/runs/20260912-155814-e83f/etcd-raft/.specula-output/confirmation/CR-1/debate.md

- **Source**: Code Review
- **Novelty**: NEW
- **Location**: rawnode.go:85

## Description
`RawNode.NewRawNode` loads saved `HardState`, then uses `Storage.LastIndex()==0` to infer “new node” and calls `becomeFollower(1, None)`. If a node has persisted a term/vote but still has an empty log, restart regresses the durable term/vote and allows the node to vote again in the same term.

## Trigger scenario
A joining RawNode starts with an empty peer list and empty log, receives a valid vote request, persists `HardState{Term:2, Vote:2}`, sends the vote response, advances, crashes, and restarts from the same empty-log storage. Restart emits `HardState{Term:1, Vote:0}`; after persisting that Ready, the node grants a second term-2 vote to candidate 3. Both candidate RawNodes consume real `MsgVoteResp` messages and become leaders in term 2.

## Developer intent
The code has a TODO at `rawnode.go:87` to rethink whether applications need to tell RawNode whether it expects to exist. Related prior PRs exist for Ready durability semantics, especially etcd PR #14413 (`raft: don't emit unstable CommittedEntries`) and raft PR #8 (async storage writes), but tracker searches did not find the same `RawNode` empty-log HardState regression / duplicate-vote mechanism.

## Reproduction result
Reproduction test: `/home/ubuntu/specula-etcd-ci-init-20260912.FNeLj3NS/ci-clean/runs/20260912-155814-e83f/etcd-raft/.specula-output/repro/test_bugCR-1_rawnode_emptylog_vote_restart.sh`

Command:
```bash
timeout 3m /home/ubuntu/specula-etcd-ci-init-20260912.FNeLj3NS/ci-clean/runs/20260912-155814-e83f/etcd-raft/.specula-output/repro/test_bugCR-1_rawnode_emptylog_vote_restart.sh
```

Checklist:
1. Did Level 0 or Level 1 alone trigger it? yes, Level 0 only.
2. Level 2/3 injection used? no.
3. Real consumer/caller observing wrong outcome: candidate RawNodes consume `MsgVoteResp` in `raft.go:1224` and both become leaders via `raft.go:1232`.
4. Bad state permanent or masked? Not masked; the regressed HardState is persisted from Ready and produces two leaders in the same term.

Output:
```text
node1 initial empty-log join: Ready HardState{Term:1 Vote:0 Commit:0} Entries:0 Committed:0 Messages:[] MustSync:true
node1 grants candidate2 before crash: Ready HardState{Term:2 Vote:2 Commit:0} Entries:0 Committed:0 Messages:[MsgVoteResp 1->2 term=2 reject=false] MustSync:true
node1 restart from empty log: Ready HardState{Term:1 Vote:0 Commit:0} Entries:0 Committed:0 Messages:[] MustSync:true
observed regression: persisted HardState moved from Term:2 Vote:2 to Term:1 Vote:0 while log remained empty
node1 grants candidate3 after restart: Ready HardState{Term:2 Vote:3 Commit:0} Entries:0 Committed:0 Messages:[MsgVoteResp 1->3 term=2 reject=false] MustSync:true
candidate2 status after node1 vote: state=StateLeader term=2 lead=2
candidate3 status after node1 second vote: state=StateLeader term=2 lead=3
BUG REPRODUCED: node1 cast two durable votes in term 2 (Vote=2 then Vote=3), allowing candidate2 and candidate3 to both observe quorum and become leaders.
```

## Recommendation
Do not infer “new RawNode” from an empty log alone after loading non-empty HardState. Preserve recovered term/vote when `HardState` is non-empty, or require an explicit bootstrap/restart mode so empty-log recovery cannot reset durable election state.

---

## Entry 2: Election and transfer eligibility depend on local configuration progress

- **Finding ID**: CR-2
- **Status**: REPRODUCED
- **Debate**: not run
- **Transcript**: /home/ubuntu/specula-etcd-ci-init-20260912.FNeLj3NS/ci-clean/runs/20260912-155814-e83f/etcd-raft/.specula-output/confirmation/CR-2/debate.md

- **Source**: Code Review
- **Novelty**: NEW
- **Location**: raft.go:1280

## Description
Leadership transfer can bypass the pending-configuration election guard. A node with a committed-but-unapplied `ConfChangeRemoveNode` is correctly blocked from ordinary `MsgHup`, but `MsgTimeoutNow` only checks `promotable()`, so the removed-soon transferee can become leader before applying its own removal. After applying it, the node remains `StateLeader` with no self progress and drops client proposals.

## Trigger scenario
Three voters elect node 1. Node 1 commits `ConfChangeRemoveNode(2)` but node 2 has not applied it yet. A transfer to node 2 sends `MsgTimeoutNow`; node 2 campaigns under its stale local config, wins, applies its removal, remains leader, then returns `ErrProposalDropped` for a proposal.

## Developer intent
`MsgHup` explicitly refuses to campaign with pending config entries (`raft.go:873`). `applyConfChange` has a TODO saying a removed/demoted leader should step down (`raft.go:1481`). Existing tests cover already-removed nonmembers and learners receiving `MsgTimeoutNow`, but not committed-unapplied self-removal during transfer.

## Reproduction result
Repro test: `/home/ubuntu/specula-etcd-ci-init-20260912.FNeLj3NS/ci-clean/runs/20260912-155814-e83f/etcd-raft/.specula-output/repro/test_bugCR-2_transfer_pending_conf.sh`

Command executed:
```sh
timeout 7m /home/ubuntu/specula-etcd-ci-init-20260912.FNeLj3NS/ci-clean/runs/20260912-155814-e83f/etcd-raft/.specula-output/repro/test_bugCR-2_transfer_pending_conf.sh
```

Key output:
```text
=== RUN   TestBugCR2TransferBypassesPendingRemovalConfig
raft... WARN: 2 cannot campaign at term 1 since there are still 1 pending configuration changes to apply
    bug_cr2_transfer_pending_conf_test.go:54: control: MsgHup blocked while ConfChangeRemoveNode(2) was committed but unapplied (committed=2 applied=0)
raft... INFO: 1 sends MsgTimeoutNow to 2 immediately as 2 already has up-to-date log
raft... INFO: 2 [term 1] received MsgTimeoutNow from 1 and starts an election to get leadership.
raft... INFO: 2 became leader at term 2
    bug_cr2_transfer_pending_conf_test.go:62: BUG TRIGGERED: MsgTimeoutNow transfer elected node 2 while ConfChangeRemoveNode(2) was still committed but unapplied (committed=3 applied=0 term=2)
raft... INFO: 2 switched to configuration {(1 3) map[]}
    bug_cr2_transfer_pending_conf_test.go:84: BUG TRIGGERED: after applying its own removal, node 2 remains StateLeader with no self progress; client proposal returns raft proposal dropped; confstate=nodes:1 nodes:3 
--- PASS: TestBugCR2TransferBypassesPendingRemovalConfig (0.00s)
PASS
ok  	go.etcd.io/etcd/raft	0.003s
```

Checklist:
1. Level 0 alone triggered it: yes.
2. No Level 2/3 injection was used.
3. Real consumer/caller observing wrong outcome: proposal caller through `raft.Step`/`RawNode.Propose` path observes `ErrProposalDropped` at `raft.go:969`.
4. Bad state is permanent until another leadership change: no downstream sync/resend/guard stepped the removed leader down; the proposal guard only exposes the bad state by dropping proposals.

## Recommendation
Apply the same pending-conf guard used by `MsgHup` before `campaign(campaignTransfer)`, and make self-removal/self-demotion while leader step down instead of returning as leader.

---

## Entry 3: Released application work and effective membership are different state

- **Finding ID**: CR-3
- **Status**: REPRODUCED
- **Debate**: not run
- **Transcript**: /home/ubuntu/specula-etcd-ci-init-20260912.FNeLj3NS/ci-clean/runs/20260912-155814-e83f/etcd-raft/.specula-output/confirmation/CR-3/debate.md

- **Source**: Code Review
- **Novelty**: NEW
- **Location**: raft.go:985

## Description
`Advance` can move `raftLog.applied` past a committed config-change entry before the application has called `ApplyConfChange`. `stepLeader` then admits a second `EntryConfChange` because it checks `pendingConfIndex > raftLog.applied`, even though effective membership is still the old configuration.

## Trigger scenario
Start a singleton cluster, elect node 1, propose `ConfChangeAddNode(2)`, receive it as committed, persist it, call `Advance` before `ApplyConfChange`, then propose `ConfChangeAddNode(3)`. The second config change is committed before node 2 has become effective.

## Developer intent
Docs and comments state one config change should be in process at a time: `node.go:135-137`, `raft.go:279-285`, `README.md:193-195`. Prior-report search found no exact match. `etcd-io/raft#43/#44` concern `ProposeConfChange` result waiting/ignored proposal reporting, not this `Advance` versus `ApplyConfChange` split.

## Reproduction result
Checklist:
1. Did Level 0 or Level 1 alone trigger it? **yes**, Level 0 public API only.
2. Level 2/3 injection or patch used? **no**.
3. Real consumer/caller observing wrong outcome: the application Ready loop documented in `doc.go:127`/`doc.go:135-141` observes and applies committed config entries; the repro observes the second committed `EntryConfChange` through public `Node.Ready`.
4. Permanent or masked? **permanent** once applied; no downstream mechanism revalidates the second config entry against the intermediate membership.

Command:
```sh
timeout 2m go run /home/ubuntu/specula-etcd-ci-init-20260912.FNeLj3NS/ci-clean/runs/20260912-155814-e83f/etcd-raft/.specula-output/repro/test_bugCR-3_double_confchange.go
```

Output:
```text
bootstrap: ready entries=1 committed=1 mustSync=true
applied confchange index=1 type=ConfChangeAddNode node=1 -> voters=[1] learners=[]
campaign: ready entries=1 committed=1 mustSync=true
first-confchange: ready entries=1 committed=1 mustSync=true
first confchange committed at index=3 for node=2; intentionally delaying ApplyConfChange
called Advance for first confchange Ready before ApplyConfChange
second-confchange: ready entries=1 committed=1 mustSync=true
BUG: second confchange committed at index=4 for node=3 before first ApplyConfChange ran
applied confchange index=3 type=ConfChangeAddNode node=2 -> voters=[1 2] learners=[]
applied confchange index=4 type=ConfChangeAddNode node=3 -> voters=[1 2 3] learners=[]
REPRODUCED: raft accepted and committed two membership changes while only released, not applied, progress separated them
```

## Recommendation
Gate new config-change admission on effective config application, not only `raftLog.applied` advanced by `Advance`. For example, track a separate config-applied cursor updated only by `ApplyConfChange`, or prevent early `Advance` from satisfying `pendingConfIndex` for committed config entries.

---

## Entry 4: Replication evidence and snapshot boundaries change at different times

- **Finding ID**: CR-4
- **Status**: DROPPED
- **Debate**: not run
- **Transcript**: /home/ubuntu/specula-etcd-ci-init-20260912.FNeLj3NS/ci-clean/runs/20260912-155814-e83f/etcd-raft/.specula-output/confirmation/CR-4/debate.md

- **Source**: Code Review
- **Novelty**: KNOWN (cite: https://github.com/etcd-io/etcd/issues/9079; fix-status: unfixed)
- **Location**: `raft.go:869`

## Description
CR-4 duplicates an already-reported etcd Raft defect: after snapshot restore, `committed` and `firstIndex()` advance to the snapshot boundary while `applied` remains behind, and campaign scans `applied+1..committed+1` without clamping to `firstIndex()`. The known report shows this exact path panicking with `unexpected error getting unapplied entries (ErrCompacted)` from `raft.Step` via `tickElection`.

## Trigger scenario
A follower receives/restores a valid snapshot, but before the snapshot Ready is applied/advanced, an election timeout or public campaign reaches `MsgHup`. The campaign pending-conf scan slices from the stale applied cursor into compacted snapshot-covered space.

## Developer intent
Docs allow Ready/Advance/application to move on different schedules, and `nextEnts` already clamps with `max(applied+1, firstIndex())`. The campaign path lacks that safeguard. Upstream issue `#9079` contains production logs with snapshot restore followed by the same panic stack.

## Reproduction result
Per the pinned `bug-confirmation` guide, this is the Phase-1 pre-filter case: Code Review source plus an already reported exact defect, so Phase 2 is not run and no repro test is written.

Relevant search output:
`gh search issues 'unexpected error getting unapplied entries' --repo etcd-io/etcd --limit 20`
returned:
`etcd-io/etcd 9079 closed raft err :unexpected error getting unapplied entries type/bug, area/raft, stale`

## Recommendation
Treat CR-4 as duplicate of the known report. The supplied V00 checkout still has the vulnerable campaign scan at `raft.go:869`; the semantic fix is to avoid scanning compacted snapshot-covered entries, e.g. by clamping the scan lower bound to `firstIndex()` or reusing the safe `nextEnts`-style boundary logic.

---

## Entry 5: ReadIndex evidence must survive membership and application interleavings

- **Finding ID**: CR-5
- **Status**: REPRODUCED
- **Debate**: not run
- **Transcript**: /home/ubuntu/specula-etcd-ci-init-20260912.FNeLj3NS/ci-clean/runs/20260912-155814-e83f/etcd-raft/.specula-output/confirmation/CR-5/debate.md

- **Source**: Code Review
- **Novelty**: NEW
- **Location**: raft.go:1002

## Description
CR-5 is reproduced. A leader that has applied its own removal remains `StateLeader`; proposals are guarded against this, but `MsgReadIndex` is not. A delayed ReadIndex heartbeat response can later satisfy the current `{2}` voter config and release a read captured before removal, even after node 2 has committed a newer value.

## Trigger scenario
Using public `RawNode` APIs only: elect node 1 in a two-node cluster, issue `ReadIndex` and delay its heartbeat proof, commit/apply removal of node 1, let node 2 elect itself and apply a newer write, then deliver the old heartbeat response to removed leader node 1.

## Developer intent
Developer comments already flag self-removal as suspicious: `raft.go:1481-1491` says the removed/demoted leader should step down “for sanity” but currently returns. I found no upstream issue, closed/merged PR, or commit message reporting this exact ReadIndex/self-removal mechanism.

## Reproduction result
Test written and executed:

`/home/ubuntu/specula-etcd-ci-init-20260912.FNeLj3NS/ci-clean/runs/20260912-155814-e83f/etcd-raft/.specula-output/repro/test_bugCR-5_removed_leader_readindex.sh`

Command:

```text
timeout 5m /home/ubuntu/specula-etcd-ci-init-20260912.FNeLj3NS/ci-clean/runs/20260912-155814-e83f/etcd-raft/.specula-output/repro/test_bugCR-5_removed_leader_readindex.sh
```

Relevant real output:

```text
LEVEL 0: public RawNode API with ordinary message delay/reordering
hold: MsgHeartbeat 1->2 term=2 ctx="cr5-stale-read"
checkpoint: read requested on node 1 at committed index 4 while node 1 is still a voter
apply: node=1 index=5 confchange type=ConfChangeRemoveNode node=1 voters=[2] learners=[]
apply: node=2 index=5 confchange type=ConfChangeRemoveNode node=1 voters=[2] learners=[]
checkpoint: node1 status after applying self-removal state=StateLeader term=2 commit=5 applied=5 progressIDs=[2] selfInProgress=false
hold: MsgHeartbeatResp 2->1 term=2 ctx="cr5-stale-read"
apply: node=2 index=7 normal value="value-after-removal"
readstate: node=1 index=4 ctx="cr5-stale-read" applied=5 value="value-before-removal"
checkpoint: node2 committed newer value at index=7 applied=7 before old proof was released
checkpoint: removed node1 emitted ReadState index=4 with applied=5 local value="value-before-removal"
BUG TRIGGERED: Ready.ReadStates on removed leader 1 authorizes a read at the old index after node 2 already committed/applied a newer value.
```

Checklist:
1. Did Level 0 or Level 1 alone trigger it? **yes**, Level 0.
2. State injection/source patch used? **no**.
3. Real consumer/caller: `Ready.ReadStates` returned to the documented application consumer at `node.go:63` / `rawnode.go:276`.
4. Masking/resolution: no mask before observation. `CheckQuorum` may later step the removed leader down, but it does not revoke the emitted `ReadState`; the stale read basis has already reached the caller.

## Recommendation
Reject `MsgReadIndex` when the local leader is not a current voter/promotable, or step down immediately on self-removal and clear pending ReadIndex state. Add a regression test with delayed ReadIndex heartbeat responses across leader self-removal.

---

## Entry 6: Admission, rejection, cancellation, and retry are protocol outcomes

- **Finding ID**: CR-6
- **Status**: REPRODUCED
- **Debate**: not run
- **Transcript**: /home/ubuntu/specula-etcd-ci-init-20260912.FNeLj3NS/ci-clean/runs/20260912-155814-e83f/etcd-raft/.specula-output/confirmation/CR-6/debate.md

- **Source**: Code Review
- **Novelty**: NEW
- **Location**: node.go:456

## Description
`Node.ProposeConfChange` hands a conf-change `MsgProp` to `Node.Step`, which uses the non-waiting proposal path and returns `nil` after channel handoff. If raft admission then rejects the proposal with `ErrProposalDropped`, `node.run` discards that error because no result channel was attached. `RawNode.ProposeConfChange` and `Node.Propose` do return the admission error, so `Node.ProposeConfChange` gives callers an incorrect success outcome.

## Trigger scenario
Level 0 public API only: start a singleton `Node`, process the bootstrap `Ready`, campaign to leader, set `MaxUncommittedEntriesSize` to one payload, accept one normal proposal, leave its `Ready` unread so quota remains charged, then call `Node.ProposeConfChange`. In the same state, a second normal `Node.Propose` returns `ErrProposalDropped`, while `Node.ProposeConfChange` returns `nil` and no conf-change entry appears in `Ready`.

## Developer intent
`raft.go:71` says `ErrProposalDropped` exists so “the proposer can be notified and fail fast.” Prior issue/PR search found related ordinary-proposal work in https://github.com/etcd-io/etcd/issues/8975 and https://github.com/etcd-io/etcd/pull/9137, but no report for this exact `Node.ProposeConfChange` wrapper site. Local tests already assert fail-fast behavior for `Node.Propose` and core raft admission drops.

## Reproduction result
Test: `/home/ubuntu/specula-etcd-ci-init-20260912.FNeLj3NS/ci-clean/runs/20260912-155814-e83f/etcd-raft/.specula-output/repro/test_bugCR-6_admission_result.sh`

Command:
```bash
timeout 5m /home/ubuntu/specula-etcd-ci-init-20260912.FNeLj3NS/ci-clean/runs/20260912-155814-e83f/etcd-raft/.specula-output/repro/test_bugCR-6_admission_result.sh
```

Output:
```text
=== RUN   TestBugCR6NodeConfChangeLosesAdmissionError
    test_bugCR6_admission_result_test.go:152: control: RawNode ProposeConfChange returned ErrProposalDropped when quota admission rejected it
    test_bugCR6_admission_result_test.go:165: observed: Node ProposeConfChange returned <nil> under the same quota-exceeded admission state
    test_bugCR6_admission_result_test.go:176: post-call Ready: entries=1 committed=1 contains_conf_change_for_node_2=false
    test_bugCR6_admission_result_test.go:185: BUG TRIGGERED: Node ProposeConfChange reported nil, while the conf-change proposal was rejected before appearing in Ready
--- PASS: TestBugCR6NodeConfChangeLosesAdmissionError (0.00s)
PASS
ok  	go.etcd.io/etcd/raft	0.003s
```

Checklist:
1. Did Level 0 or Level 1 alone trigger it? yes, Level 0 alone.
2. Level 2/3 precondition sequence: N/A.
3. Wrong outcome observer: an external public API caller of `Node.ProposeConfChange` (`node.go:138`, documented at `doc.go:156`) observes `nil` despite admission rejection.
4. Permanent or masked: not masked. The dropped conf change never appears in `Ready`, and no downstream mechanism converts the returned `nil` into `ErrProposalDropped` or automatically retries it.

## Recommendation
Route `Node.ProposeConfChange` through the waiting proposal path, as `Node.Propose` already does, so raft admission errors such as quota, leadership transfer, no-leader, or removed-leader drops are returned to the caller.

---
