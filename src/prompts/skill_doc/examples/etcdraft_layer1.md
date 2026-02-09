# Layer 1: System Context — etcd/raft

## 1. System Overview

**etcd/raft** is the Go implementation of the Raft consensus algorithm used in etcd. It is a library that provides the core Raft state machine logic, decoupled from storage and network layers.

### Core Responsibilities
- **Leader Election**: Elect a single leader among a cluster of nodes using randomized election timeouts and majority voting
- **Log Replication**: Replicate log entries from leader to followers, ensuring all nodes eventually have the same log
- **Safety**: Guarantee that committed entries are durable and will not be lost, even in the presence of failures
- **Membership Changes**: Support dynamic configuration changes (adding/removing nodes) via joint consensus

### System Boundaries
- **Input**: Messages from other nodes (via network), local timer ticks, client proposals
- **Output**: Messages to send to other nodes, committed entries to apply to state machine

---

## 2. Feature Scope

### 2.1 Leader Election

| Feature | In Scope | Notes |
|---------|----------|-------|
| Election timeout triggers candidacy | ✓ | Core |
| Vote request and response | ✓ | Core |
| Vote granted only if candidate's log is up-to-date | ✓ | Core |
| Become leader on quorum votes | ✓ | Core |
| PreVote phase | ✓ | Used in production etcd, prevents disruption |
| Check quorum (leader step-down if no quorum) | ✗ | Availability optimization, not safety-critical |

### 2.2 Log Replication

| Feature | In Scope | Notes |
|---------|----------|-------|
| Leader appends entries to local log | ✓ | Core |
| Leader sends AppendEntries to followers | ✓ | Core |
| Follower rejects if log doesn't match at prevLogIndex | ✓ | Core |
| Follower appends entries on match | ✓ | Core |
| Leader updates matchIndex on success | ✓ | Core |
| Leader decrements nextIndex on reject | ✓ | Core |
| Fast log backtracking (rejectHint + logTerm) | ✗ | Optimization, basic decrement sufficient |
| Heartbeat (empty AppendEntries) | ✓ | Needed for leader liveness and commit propagation |

### 2.3 Commit

| Feature | In Scope | Notes |
|---------|----------|-------|
| Leader commits when entry replicated to quorum | ✓ | Core |
| Only commit entries from current term | ✓ | Core (Figure 8 safety) |
| Follower advances commitIndex via AppendEntries | ✓ | Core |

### 2.4 Progress Tracking (Leader's View of Followers)

| Feature | In Scope | Notes |
|---------|----------|-------|
| matchIndex / nextIndex per follower | ✓ | Core |
| Progress state: Probe | ✓ | Needed to understand replication state machine |
| Progress state: Replicate | ✓ | Needed to understand replication state machine |
| Progress state: Snapshot | ✓ | Needed for snapshot modeling |
| Inflights / flow control | ✗ | Performance optimization |
| MsgAppFlowPaused | ✗ | Performance optimization |

### 2.5 Snapshot

| Feature | In Scope | Notes |
|---------|----------|-------|
| Leader sends snapshot to lagging follower | ✓ | Needed for log compaction scenarios |
| Follower applies snapshot and resets log | ✓ | Needed for log compaction scenarios |
| Snapshot metadata (index, term, config) | ✓ | Required for correct snapshot handling |
| Log truncation after snapshot | ✗ | Simplify: assume log starts from snapshot index |

### 2.6 Configuration Changes

| Feature | In Scope | Notes |
|---------|----------|-------|
| Single-member change (add/remove one node) | ✓ | Basic config change support |
| Joint consensus (ConfChangeV2) | ✓ | Required for multi-member changes in etcd |
| Quorum from both old and new config in joint state | ✓ | Required for joint consensus correctness |
| Auto-leave joint config | ✓ | Used in production |
| Learners (non-voting members) | ✓ | Used in production etcd |
| Leader step-down on removal | ✗ | Edge case, not core safety |

### 2.7 Leader Transfer

| Feature | In Scope | Notes |
|---------|----------|-------|
| MsgTransferLeader initiates transfer | ✗ | Graceful handoff, not core safety |
| MsgTimeoutNow triggers immediate election | ✗ | Part of transfer flow |
| Abort transfer on timeout | ✗ | Part of transfer flow |

### 2.8 Network Model

| Feature | In Scope | Notes |
|---------|----------|-------|
| Message delivery (unordered) | ✓ | Core |
| Message loss | ✓ | Essential for safety verification |
| Message duplication | ✓ | Can happen with retries |
| Partition (bidirectional loss between node subsets) | ✓ | Implied by message loss model |

### 2.9 Persistence Model

| Feature | In Scope | Notes |
|---------|----------|-------|
| Atomic state updates (term, vote, log) | ✓ | Assumed |
| Crash and recovery | ✗ | Not modeling node restarts |
| Partial writes / corruption | ✗ | Out of scope |

---

## 3. Out of Scope (Not Modeled)

| Aspect | Reason |
|--------|--------|
| Actual network transport (TCP, gRPC) | Abstracted as message set |
| Disk I/O, storage engine | Abstracted as atomic state |
| Application state machine | External to Raft |
| Logging, metrics, tracing | No state effect |
| ReadIndex / LeaseRead | Read optimization, orthogonal |
| AsyncStorageWrites, MsgStorageAppend/Apply | Internal async mechanism |
| Memory allocation, buffer management | Implementation detail |

---

## 4. Source Code Reference

| Component | File |
|-----------|------|
| Main state machine | `raft.go` |
| Log management | `log.go` |
| Progress tracking | `tracker/progress.go` |
| Configuration | `tracker/tracker.go` |
| Quorum calculation | `quorum/` |
| Message types | `raftpb/raft.proto` |
