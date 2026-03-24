# Example: hashicorp/raft Spec Generation

A complete worked example showing how the Modeling Brief drove spec design decisions.

## Input: Modeling Brief Summary

The Modeling Brief identified 5 Bug Families. The top 3 for TLA+ modeling:

| Family                            | Mechanism                                             | Priority |
| --------------------------------- | ----------------------------------------------------- | -------- |
| Leader Cannot Self-Detect Failure | Heartbeat runs independently, doesn't check resp.Term | HIGH     |
| Configuration Change Safety       | Inconsistent committed vs latest config usage         | HIGH     |
| Non-Atomic Persistence            | persistVote writes term and votedFor separately       | MEDIUM   |

## Spec Design Decisions

### Extension 1: Separate Heartbeat Path (Family 1)

**What the brief said**: Three code paths handle AppendEntries responses — `replicateTo()` (line 239), `pipelineDecode()` (line 548), and `heartbeat()` (line 423). Only heartbeat skips `resp.Term` check.

**Spec design**:

- Split `AppendEntriesRequest` send into `ReplicateEntries` and `SendHeartbeat`
- Split response handling into `HandleReplicateResponse` and `HandleHeartbeatResponse`
- `SendHeartbeat` has no `~diskBlocked[i]` guard (heartbeat works when disk is blocked)
- `HandleHeartbeatResponse` has no term check (models the bug)
- Use `msubtype` field ("heartbeat" vs "replicate") to distinguish

### Extension 2: Leader Lease (Family 1)

**What the brief said**: `checkLeaderLease()` uses `latestConfig` (not `committedConfig`) and counts `setLastContact()` calls toward quorum.

**Spec design**:

- `leaseContact` variable tracks which followers the leader believes it has contacted
- `HandleReplicateResponse` adds to `leaseContact` on success
- `HandleHeartbeatResponse` adds to `leaseContact` unconditionally (models the bug)
- `CheckLeaderLease` checks quorum using `latestConfig` (not `committedConfig`)

### Extension 3: Disk Blocking (Family 1)

**What the brief said**: Heartbeat's raison d'etre is to run when disk IO blocks replicate.

**Spec design**:

- `diskBlocked` boolean per server
- `ReplicateEntries` and `ClientRequest` require `~diskBlocked[i]`
- `SendHeartbeat` has NO disk guard (this is the key difference)
- `DiskBlock`/`DiskUnblock` toggle the flag

### Extension 4: Dual Configuration (Family 2)

**What the brief said**: Different code paths use different config versions:

- `quorumSize()`, `checkLeaderLease()`, `electSelf()` use `latestConfig`
- Leader step-down check uses `committedConfig`

**Spec design**:

- `committedConfig` and `latestConfig` per server
- `ProposeConfigChange` updates `latestConfig` only
- `AdvanceCommitIndex` updates `committedConfig` when config entry is committed
- `HandleAppendEntriesRequest` updates both from received log entries
- `BecomeLeader` quorum check uses `latestConfig` (matching code)
- `Crash` recomputes: `latestConfig` from full log, `committedConfig` from empty (conservative)

### Extension 5: Non-Atomic persistVote (Family 3)

**What the brief said**: `persistVote` (raft.go:1135-1141) writes term then votedFor. Crash between leaves term bumped but votedFor stale.

**Spec design**:

- `persistedTerm`, `persistedVotedFor` track on-disk state
- `pendingVote` holds the deferred vote response
- `HandleRequestVoteRequest` Case 3 (higher term + grant): persists term only, defers votedFor
- `CompletePersistVote`: persists votedFor and sends response
- `Crash`: recovers from `persistedTerm`/`persistedVotedFor`, NOT from `currentTerm`/`votedFor`
- Also included `HandleRequestVoteRequestAtomic` for trace validation (impl doesn't crash between persists during normal trace)

## Output Files

### base spec: `hashiraft.tla` (822 lines)

```
Variables (17):
  Standard:  currentTerm, votedFor, log, state, commitIndex,
             nextIndex, matchIndex, votesGranted, messages
  Ext 1+2:   leaseContact
  Ext 3:     diskBlocked
  Ext 4:     committedConfig, latestConfig
  Ext 5:     persistedTerm, persistedVotedFor, pendingVote

Actions (20):
  Election:  Timeout, HandleRequestVoteRequest, HandleRequestVoteRequestAtomic,
             HandleRequestVoteResponse, BecomeLeader, CompletePersistVote
  Replication: ClientRequest, ReplicateEntries, SendHeartbeat,
               HandleAppendEntriesRequest, HandleReplicateResponse,
               HandleHeartbeatResponse, AdvanceCommitIndex
  Config:    ProposeConfigChange
  Lease:     CheckLeaderLease
  Faults:    DiskBlock, DiskUnblock, Crash, LoseMessage, DropStaleMessage

Invariants (6):
  Standard:  ElectionSafety, LogMatching, LeaderCompleteness
  Bug detection: NoPhantomContact, LeaseImpliesLoyalty, ConfigSafety
```

### MC spec: `MChashiraft.tla` + `MChashiraft.cfg`

- 7 counter-bounded actions (timeout, request, crash, lose, heartbeat, diskBlock, configChange)
- 8 structural invariants
- 4 temporal properties
- Symmetry reduction over Server set
- Message buffer constraint

### Trace spec: `Tracehashiraft.tla` + `Tracehashiraft.cfg`

- 11 action wrappers
- 3 silent actions (SilentTimeout, SilentHandleReplicateResponse, FillLogGap)
- Bootstrap state: term=1, config log entry at index 1
- Uses HandleRequestVoteRequestAtomic (not the non-atomic variant)
- ValidatePostStateWeak for async events (heartbeat responses)

### Instrumentation: `instrumentation.patch`

- 14 trace event insertion points across `raft.go` and `replication.go`
- TraceLogger interface + TraceEvent/TraceState/TraceMsg structs in `trace_logger.go`
- `traceVotedFor` field for votedFor tracking

## Reference Files

- Base spec: `case-studies/hashicorp-raft/scenarios/base/spec/hashiraft.tla`
- MC spec: `case-studies/hashicorp-raft/scenarios/base/spec/MChashiraft.tla`
- Trace spec: `case-studies/hashicorp-raft/scenarios/base/spec/Tracehashiraft.tla`
- Instrumentation: `case-studies/hashicorp-raft/scenarios/base/patches/instrumentation.patch`
- Modeling Brief: `skills/code_analysis/examples/hashicorp-raft-modeling-brief.md`
