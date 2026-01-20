# etcd/raft Bug Reproduction via TLA+ Spec Reversion

This directory contains TLA+ specs that reproduce known etcd/raft bugs by reverting fixes in the specification. Each bug can be detected by TLC model checking when the corresponding invariant is violated.

## Bugs Overview

| Bug ID | Issue | Description |
|--------|-------|-------------|
| 76f1249 | [commit](https://github.com/etcd-io/raft/commit/76f1249) | MsgApp panic after log truncation |
| bd3c759 | [commit](https://github.com/etcd-io/raft/commit/bd3c759) | Auto-leave joint config multiple attempts |
| 12136 | [issue](https://github.com/etcd-io/etcd/issues/12136) | Joint state stuck after leader change |
| 7280 | [issue](https://github.com/etcd-io/etcd/issues/7280) | Async apply confchange safety |
| 124 | [issue](https://github.com/etcd-io/raft/issues/124) | Progress state transition bug |

## Bug Details

### 1. Bug 76f1249: MsgApp Panic After Log Truncation

**Directory:** `76f1249_prevLogTerm_panic/`

**Problem:** After log compaction, leader sends MsgApp with `prevLogTerm=0` for truncated entries, causing follower panic.

**Reversion:** Removed guard `range[1] >= log[i].offset` in `AppendEntriesInRangeToPeer`, allowing MsgApp to be sent even when entries are compacted.

**Invariant:** `AppendEntriesPrevLogTermValidInv`
```tla
AppendEntriesPrevLogTermValidInv ==
    \A m \in DOMAIN messages \union DOMAIN pendingMessages :
        (m.mtype = AppendEntriesRequest /\ m.mprevLogIndex > 0) =>
            m.mprevLogTerm > 0
```

---

### 2. Bug bd3c759: Auto-Leave Joint Config Multiple Attempts

**Directory:** `bd3c759_auto_leave_multiple/`

**Problem:** Auto-leave mechanism proposes multiple leave-joint entries and doesn't update `pendingConfIndex`.

**Reversion:**
- Removed `pendingConfChangeIndex[i] = 0` check in `ProposeLeaveJoint`
- Changed `pendingConfChangeIndex' = [...]` to `UNCHANGED <<pendingConfChangeIndex>>`

**Invariant:** `SinglePendingLeaveJointInv`
```tla
SinglePendingLeaveJointInv ==
    \A i \in Server :
        (state[i] = Leader /\ IsJointConfig(i) /\ config[i].autoLeave) =>
            Cardinality({uncommitted leave-joint entries}) <= 1
```

---

### 3. Bug 12136: Joint State Stuck After Leader Change

**Directory:** `12136_joint_state_stuck/`

**Problem:** When leader steps down in joint config, new leader cannot trigger auto-leave because `pendingConfChangeIndex` is reset to `lastIndex`.

**Reversion:** Added condition `pendingConfChangeIndex[i] < LastIndex(log[i])` in `ReplicateImplicitEntry`, which blocks auto-leave for newly elected leaders.

**Invariant:** `JointStateAutoLeavePossibleInv`
```tla
JointStateAutoLeavePossibleInv ==
    \A i \in Server :
        (state[i] = Leader /\ IsJointConfig(i) /\ config[i].autoLeave) =>
            (applied[i] >= pendingConfChangeIndex[i]) =>
                pendingConfChangeIndex[i] < LastIndex(log[i])
```

---

### 4. Bug 7280: Async Apply ConfChange Safety

**Directory:** `7280_async_apply_confchange/`

**Problem:** Candidate can start election before applying committed config changes, using wrong quorum.

**Reversion:** The spec already has this bug - `Timeout` action doesn't check if all committed configs are applied before starting election.

**Invariant:** `NoConfigGapDuringElectionInv`
```tla
NoConfigGapDuringElectionInv ==
    \A i \in Server :
        state[i] = Candidate =>
            {committed but unapplied config entries} = {}
```

---

### 5. Bug 124: Progress State Transition

**Directory:** `124_progress_state_transition/`

**Problem:** StateSnapshot to StateReplicate transition uses exact equality check, causing follower to get stuck when matchIndex exceeds pendingSnapshot.

**Reversion:** Changed `newMatchIndex + 1 >= pendingSnapshot[i][j]` to `newMatchIndex = pendingSnapshot[i][j]` in `canResumeFromSnapshot`.

**Invariant:** `SnapshotTransitionCorrectInv`
```tla
SnapshotTransitionCorrectInv ==
    \A i, j \in Server :
        (state[i] = Leader /\ progressState[i][j] = StateSnapshot) =>
            matchIndex[i][j] <= pendingSnapshot[i][j]
```

---

## File Structure

Each bug directory contains:
- `etcdraft_bug.tla` - Modified spec with bug injected
- `MCetcdraft.tla` - Model checking wrapper (extends etcdraft_bug)
- `MCetcdraft.cfg` - TLC configuration with invariant to check
