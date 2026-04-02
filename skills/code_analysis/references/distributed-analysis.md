# Distributed / Message-Passing Analysis

Use this reference after classifying the target as **Category A (Distributed / Message-Passing)**.

This file covers the analysis patterns that matter most for replicated state machines, consensus protocols, storage services, and other systems where the main risks are protocol logic, crash windows, and message-handling behavior.

---

## 1. Reconnaissance Priorities

Locate the files that implement:

| Component | What to look for |
|-----------|-----------------|
| State machine | Main event loop, role/state transitions |
| Message types | RPC / request / response structs |
| RPC handlers | Functions that process incoming messages |
| Log management | Append, truncate, replay, compaction |
| Persistence | Stable store operations (term, vote, log, metadata) |
| Configuration changes | Membership add/remove, joint consensus, reconfig |
| Snapshot | Snapshot create, transfer, install, recover |
| Network / transport | Message send/receive, connection management |

Useful search patterns:

```text
handleVote | appendEntries | installSnapshot | timeoutNow
Request | Response | Msg | RPC
StableStore | LogStore | SnapshotStore | persist | recover
```

### Concurrency Questions

Map what can interleave:

| Question | Why it matters |
|----------|---------------|
| What runs on the main thread / event loop? | Determines what is effectively atomic |
| What runs on separate goroutines / threads? | These can observe stale state or bypass checks |
| What timers / heartbeats / background loops run independently? | Split timing domains create protocol deviations |
| What locks protect shared state? | Reveals synchronization assumptions |
| What persistence writes happen in what order? | Crash windows often live here |

---

## 2. High-Value Analysis Patterns

### 2.1 Code Path Inconsistency

Find multiple code paths that should enforce the same protocol rule but do not.

Typical examples:

- one AppendEntries response path checks term, another skips it
- one read path checks leadership lease, another skips it
- one config-change path updates both old/new configs, another updates only one

These often become excellent bug families because they map cleanly to split TLA+ actions.

### 2.2 Non-Atomic Persistence

Look for multi-step durable updates:

- write term, then vote
- write metadata, then data
- persist snapshot metadata, then delete old log

Ask: what if the process crashes between the two writes?

### 2.3 Missing Guards / Validation

Enumerate handler preconditions and compare across related handlers.

Common checks:

- term validation
- leadership / follower state validation
- membership validation
- prev-log / match-index validation
- only-if-committed / only-if-durable validation

### 2.4 Reference Deviation

Compare the implementation against:

- the paper / reference algorithm
- previous in-repo specs
- sister implementations

Useful deviation classes:

- extra feature not in the paper
- optimization path that bypasses normal logic
- architectural split across goroutines / services
- alternate representation of config / log / snapshot state
- different timing model (e.g., lease-based leader detection vs heartbeat-based)

### 2.5 Independent Control Loops

Look for logic that was split across independently scheduled components:

- heartbeat loop vs replication loop
- election timeout vs apply loop
- async snapshot sender vs foreground state machine

Many bugs come from one loop observing state later than another.

### 2.6 Recovery / Snapshot / Membership Cross-Product

These interactions are disproportionately bug-dense:

- crash recovery during or after config change
- snapshot install racing with append / truncate
- recovering persisted metadata that lags in-memory membership

### 2.7 Error Handling Gaps

Search `if err != nil` and partial rollback paths.

Questions:

- is state rolled back?
- is a partially-completed operation retried?
- does the code continue with stale assumptions after logging an error?

---

## 3. What Strong Distributed Bug Families Look Like

Strong bug families usually group around mechanisms like:

- message acceptance guards
- non-atomic persistence
- config / quorum transitions
- recovery vs live-state divergence
- independent heartbeat / replication / timeout control loops
- snapshot lifecycle mismatches

Weak bug families are usually:

- flat “file X has many suspicious lines”
- broad “network bug” buckets with no shared mechanism
- implementation-only nits better handled by testing or code review

---

## 4. Modeling Implications

When a distributed-system finding is promising for TLA+, it usually implies one of:

- split one handler into multiple action variants
- introduce persistent vs in-memory state
- add explicit crash / recovery actions
- model dual config / dual log / snapshot metadata
- separate independent loops that the paper treats as one

If a finding is mostly about formatting, logging, allocation, or a tiny local coding mistake, it is usually **not** a good model-checking target.
