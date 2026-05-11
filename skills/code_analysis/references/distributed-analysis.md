# Distributed / Message-Passing Analysis

Use this reference after classifying the target as **Category A (Distributed / Message-Passing)**.

This file covers the analysis patterns that matter most for replicated state machines, consensus protocols, storage services, and other systems where the main risks are protocol logic, crash windows, and message-handling behavior.

If the target uses BFT consensus (Byzantine threat model — PBFT, HotStuff, Tendermint / CometBFT, DiemBFT / AptosBFT, IBFT / QBFT, HoneyBadgerBFT, Algorand, Narwhal+Bullshark), **additionally** consult `bft-analysis.md` for the Byzantine adversary categories that compose on top of the 6 distributed fault families described here. For purely crash-fault-tolerant systems (Raft, Multi-Paxos, primary-backup), use this file alone — `bft-analysis.md` does not apply.

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

---

## 5. Fault Model Reference

Distributed systems have well-established canonical fault models — `crash + lose message + timeout` appears in every consensus paper and every replication codebase. The six families below codify what is already canonical across the literature, plus a few system-specific patterns surfaced by the case-study set. They are a checklist for completeness, not a constraint on design.

If the target has a domain-specific failure mode that fits its semantics better — disk silent corruption, clock skew, geo-replication fan-out, leader lease drift, custom write-ahead-log truncation — model it directly. The list is non-exhaustive on purpose.

Unlike concurrent specs (where one family — thread interleaving — dominates), distributed bugs typically emerge from the **interaction between two or three families**. Crash alone rarely surfaces a Raft bug; crash + network + timeout in combination does. Spend modeling effort ensuring each family is faithful, then let TLC explore their cross-product.

> Byzantine / equivocation faults (BFT consensus) are not covered here — see `bft-analysis.md` for the 9 Byzantine adversary categories. When the target is BFT, model both layers: the 6 distributed families below + the Byzantine actions in `bft-analysis.md` that compose with them.

### 5.1 Crash and Recovery — *the canonical headline*

Server stops; in-memory state is lost; persisted state is retained. On restart, the node rejoins the quorum and may differ from the durable view of others.

- Applicable when: every distributed system. This is the canonical fault model — a distributed spec without it is missing its primary adversary.
- Spec hint: `Crash(s)` action that splits state into persistent vs in-memory; only persistent survives. `Recover(s)` re-enters the protocol with persistent state. See `case-studies/cometbft/spec/base.tla`.
- Skip when: never.
- Composition note: most non-trivial Raft / Paxos bugs need crash composed with at least one network family (5.2) or non-atomic persistence (5.4).

### 5.2 Message Loss / Partition / Reorder

Network drops messages, isolates servers, or reorders delivery.

- Applicable when: any system using asynchronous messaging.
- Spec hint: `LoseMessage(m)` removes from the message bag; `PartitionServer(s)` filters delivery for that server; reorder is implicit when the spec uses a bag (set) rather than an ordered queue. See `case-studies/etcd-raft/spec/MC.tla` (`MCLoseMessage`, `MCPartitionServer`).
- Skip when: rare — TCP delivery guarantees do not cover application-level reorder across retries / multiple connections.

### 5.3 Timeout / Timer Firing

Election / leader / heartbeat / lease timer fires non-deterministically. Models clock skew, scheduler delay, or simply the absence of a synchrony assumption.

- Applicable when: any system with timers.
- Spec hint: `Timeout(s)` action under counter bound. The action does not depend on real time — it fires at any spec-allowed point.
- Skip when: rare; even pure data planes usually have some timer.
- Composition note: timeout + partition is the classic split-brain trigger.

### 5.4 Non-Atomic Persistence

Crash between two or more durable writes within a single logical operation. Persistent state on restart contains a partial commit.

- Applicable when: implementation uses multiple disk writes (term then votedFor; index then data; metadata then checkpoint) without group fsync.
- Spec hint: split the "atomic" persist into N sub-actions; allow `Crash` between any pair. See `case-studies/aptosbft/spec/MC.tla` (`MCCrashBetweenSignAndPersist`).
- Skip when: implementation uses single-atomic-write or transactional fsync.
- Bug class: heavy in MongoDB / Raft variants where persistence is the main correctness boundary.

### 5.5 Configuration / Membership Change

Quorum membership changes during the protocol — joint consensus, leader-driven reconfig, or out-of-band cluster reshape.

- Applicable when: system supports add/remove server, role changes, epoch transitions.
- Spec hint: `ConfigChange(s, newCfg)` action; track active configs and decide how reads/writes intersect. Joint consensus (Raft §6) requires dual-config state.
- Skip when: cluster size is fixed at boot.

### 5.6 Snapshot / State Transfer / Catchup

Lagging server receives bulk state from a peer rather than replaying the log; the protocol must reconcile installed state with subsequent incremental updates.

- Applicable when: system has snapshot-and-install, log compaction, or peer-to-peer state sync.
- Spec hint: `InstallSnapshot(s, snap)` truncates local state to snapshot; subsequent log appends must match. See `case-studies/etcd-raft/scenarios/snapshot/`.
- Skip when: log is unbounded and never compacted.

---

### Sub-Category Prioritization

The six families apply with different weight by sub-category:

| Sub-category | Typical examples | Priority families | Often skip |
|---|---|---|---|
| Raft / Multi-Paxos consensus | etcd-raft, hashicorp-raft, braft, logcabin | 5.1 Crash, 5.2 Network, 5.3 Timeout, 5.4 NonAtomicPersist, 5.6 Snapshot, 5.5 ConfigChange | — |
| Replicated storage | mongodb-*, kudu, scylla, rethinkdb | 5.1 Crash, 5.4 NonAtomicPersist (heavy), 5.6 Catchup, 5.2 Network, 5.5 Reconfig | — |
| Network protocol FSM | sonic-iccpd, sonic-linkmgrd, sonic-warmreboot | 5.2 Loss / Reorder, 5.3 Timeout, 5.1 Crash, **event-ordering** (system-specific) | 5.6 Snapshot |
| Streaming / pub-sub | aeron, mongodb-changestreams | 5.1 Crash, 5.2 Network, 5.6 Catchup, 5.4 NonAtomicPersist | — |

5.1 Crash appears in every row — like 5.1 Thread Interleaving in concurrent specs, it is universal. The differences are in which other families are load-bearing for the system's specific guarantees. Match the modeled adversary to actual exposure.

If the target is hybrid, take the union of relevant rows.

### Composition

Distributed bugs typically need 2-3 families composed: `crash + non-atomic persistence` (split-brain after partial fsync), `partition + timeout` (split-brain election), `config change + crash during transition` (lost commits). Compose only after each family individually passes — composition explodes state space and clouds blame attribution.

### When None of These Fits

If the target's most realistic fault is not on this list — disk silent corruption, GPS clock drift, geo-replication fan-out, custom WAL truncation, leader-lease boundary issues — model it directly. The six families are starting points across the case-study set, not a definition of "fault model".
