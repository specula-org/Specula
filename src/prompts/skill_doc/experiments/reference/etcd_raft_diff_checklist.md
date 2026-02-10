# etcd/raft Implementation vs Raft Paper: Key Differences

This checklist highlights where the etcd/raft implementation differs from the Raft paper. Pay special attention to these when writing the spec.

## 1. Extra State Variables (not in paper)

| Variable | Location | Purpose |
|----------|----------|---------|
| `lead` | raft.go:380 | Tracks known leader ID |
| `Progress.State` | tracker/progress.go | Probe/Replicate/Snapshot state machine |
| `Progress.Match/Next` | tracker/progress.go | Per-follower replication tracking |
| `pendingConfIndex` | raft.go:390 | Prevents concurrent config changes |
| `preVote` | raft.go:412 | PreVote feature flag |
| `checkQuorum` | raft.go:411 | CheckQuorum feature flag |

## 2. Vote Logic Differences

**Paper says**: A server votes if it hasn't voted in this term.

**Code says** (raft.go:1206-1210):
```go
canVote := r.Vote == m.From ||
    (r.Vote == None && r.lead == None) ||  // <-- Extra condition!
    (m.Type == pb.MsgPreVote && m.Term > r.Term)
```

The `r.lead == None` check prevents a server from voting if it already knows a leader, reducing disruption from partitioned nodes.

## 3. PreVote (not in paper)

- PreVote is a two-phase election: PreVote then real Vote
- PreVote does NOT increment term (raft.go:1107-1108)
- PreVote responses use `m.Term` not `r.Term` (raft.go:1243)

## 4. Progress State Machine (not in paper)

Leaders track each follower's state:
- `StateProbe`: Sending one message at a time, waiting for response
- `StateReplicate`: Optimistic pipelining, sending multiple messages
- `StateSnapshot`: Sending snapshot, paused until complete

Transitions:
- Probe → Replicate: on successful append response
- Replicate → Probe: on rejected append response
- Any → Snapshot: when log is truncated past follower's Next

## 5. Heartbeat Commit Calculation

**Paper says**: Send commitIndex in heartbeat.

**Code says** (raft.go:694-700):
```go
commit := min(pr.Match, r.raftLog.committed)
```

Leader sends `min(match, committed)` to avoid forwarding commit to unmatched index.

## 6. AppendEntries Rejection Optimization

**Paper says**: Decrement nextIndex by 1 on rejection.

**Code says** (raft.go:1383-1501): Uses `RejectHint` and `LogTerm` for fast backtracking, potentially skipping entire terms.

## 7. Configuration Change

**Paper says**: Single-server changes only.

**Code says**: Supports joint consensus for multi-server changes (EnterJoint/LeaveJoint).

## 8. CheckQuorum (not in paper)

Leader steps down if it doesn't hear from a quorum within election timeout (raft.go:1273-1285).

## Summary: Must-Model Items Often Missed

1. ✓ `lead` variable
2. ✓ `lead == None` in vote condition
3. ✓ Progress states (Probe/Replicate/Snapshot)
4. ✓ PreVote doesn't change term
5. ✓ Heartbeat uses `min(match, committed)`
