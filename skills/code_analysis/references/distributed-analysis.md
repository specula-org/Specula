# Distributed / Message-Passing Analysis

Use this reference after classifying the target as **Category A (Distributed / Message-Passing)**.

This file covers the analysis patterns that matter most for replicated state machines, consensus protocols, storage services, and other systems where the main risks are protocol logic, crash windows, and message-handling behavior.

If the target uses BFT consensus (Byzantine threat model — PBFT, HotStuff, Tendermint / CometBFT, DiemBFT / AptosBFT, IBFT / QBFT, HoneyBadgerBFT, Algorand, Narwhal+Bullshark), **additionally** consult `bft-analysis.md` for the Byzantine adversary categories that compose on top of the 6 distributed fault categories described here. For purely crash-fault-tolerant systems (Raft, Multi-Paxos, primary-backup), use this file alone — `bft-analysis.md` does not apply.

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

These often become excellent scenarios because they map cleanly to split TLA+ actions.

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

## 3. What Strong Distributed Scenarios Look Like

Strong scenarios usually group around mechanisms like:

- message acceptance guards
- non-atomic persistence
- config / quorum transitions
- recovery vs live-state divergence
- independent heartbeat / replication / timeout control loops
- snapshot lifecycle mismatches

Weak scenarios are usually:

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

## 5. Fault Model — Vocabulary, Not Checklist

The labels below are a vocabulary for talking about distributed failure modes. They are **not** a checklist; do not assume your target needs all of them, and do not copy structural choices from other case studies. Each target deserves a case-specific analysis grounded in its own code, deployment context, and the open questions the brief is trying to answer.

> Byzantine / equivocation faults (BFT consensus) are not covered here — see `bft-analysis.md`. When the target is BFT, the Byzantine adversary composes with whichever non-Byzantine faults the target's deployment actually exposes.

### 5.1 Crash and Recovery — *the canonical headline*

Server stops; in-memory state is lost; persisted state is retained. On restart, the node rejoins the quorum and may differ from the durable view of others. This is the substrate of distributed bugs in the same way thread interleaving is the substrate of concurrent bugs — a Raft/Paxos-style spec that does not model crash is usually missing its primary adversary. How to split persistent vs in-memory state is target-specific; the right granularity comes from reading the actual persistence code.

### 5.2-5.6 — Other Common Failure Modes

These are situational. Use them only if your target's actual code, deployment, and the open question warrant them. Each entry is a label; the implementation should come from your case, not from imitating other case studies.

- **5.2 Message loss / partition / reorder** — asynchronous-messaging hazards: drops, isolation, out-of-order delivery across retries or multiple connections.
- **5.3 Timeout / timer firing** — election, lease, heartbeat, or scheduler-delay timers fire non-deterministically. Often the trigger for split-brain when composed with partition.
- **5.4 Non-atomic persistence** — multiple durable writes within one logical operation, with crash possible between any pair. Heavy in replicated-storage systems where fsync boundaries are the main correctness frontier.
- **5.5 Configuration / membership change** — joint consensus, leader-driven reconfig, role / epoch transitions while the protocol is running.
- **5.6 Snapshot / state transfer / catchup** — lagging server receives bulk state and must reconcile with subsequent incremental updates.

If your target's most realistic fault isn't named above — disk silent corruption, clock skew, geo-replication fan-out, leader lease drift, custom WAL truncation, GPS drift, application-level reorder across retries, etc. — describe it directly. The vocabulary is not a closed list.

### Composition

Most non-trivial distributed bugs need 2-3 of these mechanisms composed (crash + non-atomic persist; partition + timeout; config change during transition). Composition explodes state space and clouds blame attribution, so compose only when the open question requires it, and only after each individual mechanism is faithful in isolation.

### Caveat: no answer-key adversaries

The same anti-pattern that bites concurrent specs bites distributed specs too — adversaries whose only effect is to reproduce an already-fixed bug. If you can characterise a wrapper's effect as "equivalent to `git revert <commit>`" for some past commit, drop it. Closed PRs are evidence of mechanism bug-proneness (§ 2 of the modeling brief); they are not a target list for the spec to re-enumerate. See `modeling-brief-format.md` § 6.1 and `bug-archaeology.md` § 1.4.
