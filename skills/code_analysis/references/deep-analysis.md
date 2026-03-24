# Deep Analysis Methodology

Detailed guide for Phase 1 (Reconnaissance) and Phase 3 (Deep Analysis) of Code Analysis.

---

## 1. Codebase Reconnaissance (Phase 1)

### 1.1 Identify Core Modules

Locate the files that implement:

| Component | What to look for |
|-----------|-----------------|
| State machine | Main event loop, state transitions (follower/candidate/leader) |
| Message types | RPC definitions, request/response structs |
| RPC handlers | Functions that process incoming messages |
| Log management | Append, truncate, read log entries |
| Persistence | Stable store operations (term, vote, log) |
| Configuration changes | Membership add/remove, joint consensus |
| Snapshot | Snapshot creation, transfer, restore |
| Network/Transport | Message sending, connection management |

Use `Glob` and `Grep` to locate these systematically:
```
Grep: "func.*handleVote\|func.*appendEntries\|func.*requestVote"
Grep: "type.*Request\|type.*Response"
Grep: "StableStore\|LogStore\|SnapshotStore"
```

### 1.2 Map Concurrency Model

Critical for understanding what can interleave:

| Question | Why it matters |
|----------|---------------|
| What runs on the main thread / event loop? | Determines what is effectively atomic |
| What runs on separate goroutines/threads? | These can interleave with each other and main thread |
| What locks protect shared state? | Identifies synchronization boundaries |
| What channels/queues connect components? | Identifies message-passing boundaries |
| What runs independently (timers, heartbeats)? | Independent goroutines may miss state changes |

### 1.3 Map Atomicity Boundaries

For each major operation, determine:
- What reads and writes happen as a single atomic unit?
- What can be interleaved by concurrent operations?
- What persistence operations happen in what order?

This directly informs how to split (or not split) TLA+ actions.

---

## 2. Deep Code Analysis Patterns (Phase 3)

### 2.1 Code Path Inconsistency

**What**: Multiple code paths that handle the same concept but differ in important ways.

**How to find**:
1. Identify all places that handle the same RPC type (e.g., AppendEntries response)
2. For each, list what checks are performed
3. Find paths that are missing checks present in others

**Example** (hashicorp/raft):
```
AppendEntries response handling:
  replicateTo (line 239):  checks resp.Term > req.Term  ← YES
  pipelineDecode (line 548): checks resp.Term > req.Term ← YES
  heartbeat (line 412):    no term check                 ← MISSING
```

**Why it's valuable**: Path inconsistency bugs are the most common type found in the hashicorp/raft analysis. They directly map to TLA+ modeling — split the action into variants and check if the variant without the check violates safety.

### 2.2 Non-Atomic Operations

**What**: Operations that modify multiple pieces of state in separate steps, with a crash window between them.

**How to find**:
1. Search for persistence operations: `SetUint64`, `Set`, `StoreLogs`, `DeleteRange`
2. Find sequences of multiple persistence calls in the same function
3. Ask: "What if the process crashes between call N and call N+1?"

**Example** (hashicorp/raft):
```go
// raft.go:1135-1141 — persistVote
func (r *Raft) persistVote(term uint64, candidate []byte) error {
    if err := r.stable.SetUint64(keyCurrentTerm, term); err != nil {  // Step 1
        return fmt.Errorf("failed to save current term: %w", err)
    }
    if err := r.stable.Set(keyLastVoteCand, candidate); err != nil {   // Step 2
        return fmt.Errorf("failed to save last vote candidate: %w", err)
    }
    return nil
}
// Crash between Step 1 and Step 2: term is new, but votedFor is stale
```

**How to model**: Split the operation into two TLA+ actions. Add a `Crash` action that can fire between them. Check if the recovered state satisfies safety invariants.

### 2.3 Missing Guards / Checks

**What**: A handler that lacks a safety check present in similar handlers.

**How to find**:
1. For each RPC handler, list all precondition checks
2. Compare across similar handlers
3. Find missing checks

Common checks to look for:
- Term validation (`req.Term >= currentTerm`)
- State check (`state == Leader` / `state == Follower`)
- Membership check (`sender is in cluster`)
- Log consistency check (`prevLogIndex` / `prevLogTerm`)

### 2.4 Reference Deviation Analysis

**What**: Places where the implementation deliberately differs from the reference algorithm/paper.

**How to find**:
1. Read the reference algorithm (e.g., Raft paper Figure 2)
2. For each rule in the reference, find the corresponding code
3. Note every deviation, however small

**What to note for each deviation**:
- What the reference says
- What the implementation does instead
- Why (check code comments, PRs, issues)
- Risk: could this deviation have edge cases?

**Types of deviations**:

| Type | Example | Risk |
|------|---------|------|
| Additional feature | PreVote (not in original Raft paper) | New interactions with existing features |
| Optimization | Pipeline replication | May skip checks present in non-optimized path |
| Architectural split | Heartbeat on separate goroutine | May miss state changes visible to main thread |
| Different data structure | Two config versions (committed/latest) | Inconsistent usage across code paths |
| Different timing | Lease-based leader detection vs heartbeat-based | Timing assumptions may not hold |

### 2.5 Developer Signals

**What**: Explicit acknowledgments of known issues in the code.

```bash
grep -rn "TODO\|FIXME\|HACK\|XXX\|BUG\|WARN" <core_files>
```

These are high-value signals:
- A TODO about a known issue confirms the area is problematic
- A FIXME suggests the developer intended to fix something but didn't
- A HACK suggests a workaround that may have side effects

### 2.6 Error Handling Gaps

**What**: Code paths where errors are logged but not handled, or where partial operations leave state inconsistent.

**How to find**:
1. Search for error handling: `if err != nil`
2. Check what happens after the error: is state rolled back? Is the operation retried? Or just logged?
3. Look for partial operations: Step 1 succeeds, Step 2 fails — is Step 1 rolled back?

---

## 3. Verification Checklist

For EVERY finding from Phase 3, verify before including in the report:

### 3.1 Re-Read

Don't rely on memory. Re-read the exact lines. Context matters — the surrounding code may contain compensating logic.

### 3.2 Compensating Mechanisms

Check if there's another check elsewhere that handles this case:
- Is there a timeout that eventually triggers the right behavior?
- Is there a periodic check that catches inconsistencies?
- Is there a recovery path that fixes the state?

### 3.3 Full Execution Path

Trace the control flow from entry point to the suspicious code:
- What conditions must be true for this code to execute?
- Can those conditions actually occur?
- What happens after this code — does subsequent logic fix the issue?

### 3.4 Design Intent

Check if it's intentional:
- Read code comments around the suspicious area
- Search for related PRs/issues discussing this behavior
- Check if similar code in other implementations does the same thing

### 3.5 Real-World Impact

Assess whether the issue can be triggered in practice:
- Does it require a specific sequence of events?
- Does it require network partition, crash, or other failures?
- Has anyone reported this issue in production?

---

## 4. Analysis Method

### 4.1 File-by-File Reading

For each core file, read it **in full** using the `Read` tool. Do not skim. Pay special attention to:

- RPC handlers (requestVote, appendEntries, installSnapshot, etc.)
- State transition functions (becomeFollower, becomeCandidate, becomeLeader)
- Persistence operations (writing term, vote, log entries)
- Configuration change logic

### 4.2 Parallelization

Use multiple Task subagents — one per major source file:

```
Subagent A: Analyze raft.go (state machine, RPC handlers)
Subagent B: Analyze replication.go (log replication, heartbeat)
Subagent C: Analyze configuration.go (config changes)
```

Each subagent should:
1. Read the file completely
2. Apply all analysis patterns (2.1-2.6)
3. Return findings with file:line references

### 4.3 Cross-Referencing

After parallel analysis, cross-reference findings:
- Do findings from different files relate to the same mechanism?
- Do they form a Bug Family?
- Do they confirm or contradict each other?
