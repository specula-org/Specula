# Confirmation: Bug A

## Verdict

Status: **REPRODUCED** on V01, V02, and V03.

Source: MC counterexample. Novelty: **KNOWN** to supplied dataset `etcd-raft-ci-sequence-20260912 label A`; fix-status in supplied historical snapshots: **unfixed through V03**.

V00 result: V00 predates `ConfChangeV2` / `EntryConfChangeV2`, so the V2 witness cannot be run through public APIs there. The equivalent legacy pending-configuration control blocks campaign.

## Public Reachability

The reproduction uses only public RawNode APIs and real raft messages:

- startup: `RawNode.Bootstrap` on V01-V03, legacy `NewRawNode(config, peers)` on V00;
- normal `Ready` handling with `MemoryStorage.Append`, `SetHardState`, `Advance`, and `ApplyConfChange`;
- `Campaign`, `ProposeConfChange`, and `Step` for real peer messages.

The branch state is reached by a valid scheduler: node 2 has received and committed index 5, but the application has not yet polled the next Ready. Thus `commit=5`, `applied=4`, no active Ready, and entry 5 is a committed but unapplied `EntryConfChangeV2`.

## Observed Consequence

Node 2 campaigns despite the pending V2 config entry. It emits higher-term `MsgVote` requests to old voters 1 and 3. Delivering the vote to node 1 disrupts an established live leader: node 1 steps down from leader term 2 to follower term 3, grants the vote, and node 2 can become leader in term 3.

This is not a same-term two-leader claim.

## MC Witness Match

The reproduced branch matches the compact witness:

- pre-branch node 2: `Follower`, term 2, `commit=5`, `applied=4`, `PreVote=false`;
- active config still old voters `{1,2,3}`;
- entry 5 is V2 replacement `remove 3`, `add 4`, `TransitionAuto`;
- `Campaign` transitions node 2 to `Candidate`, term 3;
- vote requests are emitted to node 1 and node 3 with `index=5`, `logTerm=2`.

The root cause is the same code path: `MsgHup` calls `numOfPendingConf`, and `numOfPendingConf` only counts `EntryConfChange`, not `EntryConfChangeV2`.

## Exact Command

Representative V01 run:

```sh
timeout 5m env GOTOOLCHAIN=local GOCACHE=/workspace/out/gocache GOTMPDIR=/workspace/out/gotmp GOPROXY=off /workspace/out/repro/test_bugA_runner.sh V01 v2 rep1
```

All repeated run outcomes and source hashes are in `out/results.json`. Full logs are in `out/logs/`.

## Relevant Output

From `out/logs/V01_v2_rep1.log`:

```text
BRANCH before campaign node2={id:2 state:StateFollower term:2 vote:1 commit:5 applied:4 lead:1} hasReady=true activeReady=false pendingEntry=EntryConfChangeV2@5
CAMPAIGN after node2={id:2 state:StateCandidate term:3 vote:2 commit:5 applied:4 lead:0} emittedVotes=[2->1 MsgVote term=3 index=5 logTerm=2 commit=0 entries=0 reject=false, 2->3 MsgVote term=3 index=5 logTerm=2 commit=0 entries=0 reject=false]
CONSEQUENCE leaderBefore={id:1 state:StateLeader term:2 vote:1 commit:5 applied:5 lead:1} leaderAfterVote={id:1 state:StateFollower term:3 vote:2 commit:5 applied:5 lead:0}
RESULT reproduced=true finalNode1={id:1 state:StateFollower term:3 vote:2 commit:5 applied:5 lead:0} finalNode2={id:2 state:StateLeader term:3 vote:2 commit:5 applied:5 lead:2}
```

Legacy negative control from the same run:

```text
CONTROL legacy before={id:2 state:StateFollower term:2 vote:1 commit:5 applied:4 lead:1} afterCampaign={id:2 state:StateFollower term:2 vote:1 commit:5 applied:4 lead:1} emittedVotes=[]
CONTROL_RESULT legacyBlocked=true leader={id:1 state:StateLeader term:2 vote:1 commit:5 applied:5 lead:1}
```

## Recommendation

Campaign eligibility should treat `EntryConfChangeV2` as a pending configuration entry in the same way proposal-side logic already does, preferably via one shared helper for configuration-entry classification.
