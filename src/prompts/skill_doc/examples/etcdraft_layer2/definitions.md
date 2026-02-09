# Definitions — etcd/raft

## Constants

- `Server`: Set of all server IDs
- `Nil`: Placeholder for "none"

---

## State Variables

### Per-Node State

| Variable | Type | Description | Source |
|----------|------|-------------|--------|
| `currentTerm` | Server → Nat | Current term number | `raft.Term` |
| `votedFor` | Server → (Server ∪ {Nil}) | Vote granted in current term | `raft.Vote` |
| `state` | Server → {Follower, Candidate, PreCandidate, Leader} | Current role | `raft.state` |
| `lead` | Server → (Server ∪ {Nil}) | Known leader | `raft.lead` |
| `log` | Server → Seq(Entry) | Log entries, each entry = (term, index, type, data) | `raft.raftLog` |
| `commitIndex` | Server → Nat | Highest committed index | `raft.raftLog.committed` |

### Leader-Only State

| Variable | Type | Description | Source |
|----------|------|-------------|--------|
| `nextIndex` | Server → (Server → Nat) | Next index to send to each follower | `tracker.Progress.Next` |
| `matchIndex` | Server → (Server → Nat) | Highest replicated index for each follower | `tracker.Progress.Match` |
| `progressState` | Server → (Server → {Probe, Replicate, Snapshot}) | Replication state per follower | `tracker.Progress.State` |

### Election State

| Variable | Type | Description | Source |
|----------|------|-------------|--------|
| `votesGranted` | Server → (Server → Bool) | Votes received from each server | `tracker.Votes` |

### Configuration State

| Variable | Type | Description | Source |
|----------|------|-------------|--------|
| `config` | Server → Configuration | Cluster membership | `tracker.Config` |

Configuration structure:
- `voters`: Set(Server) — voting members (in joint: incoming voters)
- `votersOutgoing`: Set(Server) — outgoing voters in joint config
- `learners`: Set(Server) — non-voting members
- `autoLeave`: Bool — auto-transition out of joint config

### Snapshot State

| Variable | Type | Description | Source |
|----------|------|-------------|--------|
| `pendingSnapshot` | Server → (Snapshot ∪ {Nil}) | Snapshot being sent/received | `raft.raftLog.unstable.snapshot` |

### Network State (Global)

| Variable | Type | Description | Source |
|----------|------|-------------|--------|
| `messages` | Set(Message) | In-flight messages | `raft.msgs` |

---

## Message Types

| Type | Fields | Description |
|------|--------|-------------|
| `MsgVote` | from, to, term, lastLogTerm, lastLogIndex | Vote request |
| `MsgVoteResp` | from, to, term, reject | Vote response |
| `MsgPreVote` | from, to, term, lastLogTerm, lastLogIndex | PreVote request |
| `MsgPreVoteResp` | from, to, term, reject | PreVote response |
| `MsgApp` | from, to, term, prevLogIndex, prevLogTerm, entries, commitIndex | AppendEntries |
| `MsgAppResp` | from, to, term, index, reject, rejectHint | AppendEntries response |
| `MsgHeartbeat` | from, to, term, commitIndex | Heartbeat |
| `MsgHeartbeatResp` | from, to, term | Heartbeat response |
| `MsgSnap` | from, to, term, snapshot | InstallSnapshot |
