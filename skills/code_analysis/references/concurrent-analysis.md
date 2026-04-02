# Concurrent / Lock-Free Analysis

Use this reference after classifying the target as **Category B (Concurrent / Lock-Free / Runtime)**.

This file covers the analysis patterns that matter most for lock-free data structures, runtimes, schedulers, async cancellation code, and reclamation-heavy implementations.

---

## 1. Reconnaissance Priorities

Locate the files that implement:

| Component | What to look for |
|-----------|-----------------|
| Linearization points | CAS / fetch_add / swap / compare_exchange sites |
| Reclamation | epoch, hazard, debt, retire, reclaim, free, deferred drop |
| Resize / migration | grow, copy, transfer, promote, help, rehash |
| Fallback / slow path | help paths, parking, blocking mode, async completion |
| Ownership transfer | fulfill, cancel, drop, wake, unpark, handoff |
| Bookkeeping state | counters, flags, per-thread slots, rem/refcount fields |

These are often more important than the public API surface. A tiny lock-free helper file can be more bug-dense than a large outer module.

### Concurrency Questions

Map what can interleave:

| Question | Why it matters |
|----------|---------------|
| Which atomics participate in one logical operation? | Cross-variable ordering gaps often hide here |
| What snapshots are cached and later re-checked? | Missing re-check bugs are common |
| When is data retired vs actually reclaimed? | Lifetime bugs live in this gap |
| What ownership transfers across threads / callbacks? | Completion-order bugs often live here |
| What fast path differs from the fallback / help path? | Divergence is a major bug source |
| Which state is thread-local view vs current shared truth? | Good TLA+ models need both |

---

## 2. High-Value Analysis Patterns

### 2.1 Split Operation Windows

Look for API-level operations that appear atomic but are internally split into stages:

- read snapshot -> validate / confirm
- reserve -> write -> publish
- load pointer -> confirm -> access
- retire -> unlink -> reclaim
- enqueue wakeup -> decrement counter -> complete

Each stage boundary is a candidate bug family.

### 2.2 Missing Re-Check After Stale Snapshot

Pattern:

1. Thread reads shared state into a local snapshot
2. Another thread changes the structure
3. Original thread continues without re-checking the snapshot against current state

Common sites:

- resize helpers
- fallback readers
- batch operations
- iterators
- async futures after `await`

### 2.3 Memory-Ordering Bridges Across Variables

Look for guarantees that depend on visibility across **different** atomics or between atomics and plain memory.

Examples:

- seeing tail update implies data write is visible
- publishing hazard / debt before pointer swap
- epoch bump must be ordered before pointer read
- wakeup must be visible after status transition

If the safety argument depends on comments, folklore, or architecture assumptions rather than a local proof, treat it as high priority.

### 2.4 Reclamation / Grace-Period Windows

Map the lifecycle exactly:

1. object becomes unreachable
2. object is retired / queued
3. readers still holding references drain
4. reclamation actually frees memory

Then ask:

- what protects step 2 -> 4?
- can a thread still access a retired object?
- can the object be re-used at the same address / slot / generation?

### 2.5 Ownership Transfer and Completion Ordering

Look for one thread handing work or ownership to another:

- detachable task completion
- async future drop / cancel paths
- parker / unpark handoff
- helper thread finishing another thread’s work

Many real bugs come from signaling ownership transfer before all accesses to the old-owner state have finished.

### 2.6 Fast Path vs Slow Path Divergence

Compare:

- single-item vs batch path
- optimistic path vs fallback path
- blocking vs non-blocking mode
- initiator path vs helper path
- normal completion vs cancel / timeout / abort path

If the slow path skips a check present in the fast path, that is often model-checkable.

### 2.7 Bookkeeping Boundary Violations

Check whether semantic API guarantees are enforced by counters / flags:

- bounded capacity
- exactly-once dequeue / consume
- no duplicate publication
- no orphaned waiter / parked thread
- no stale rem / refcount / epoch bookkeeping

These often produce strong invariants even when the implementation is otherwise low-level.

---

## 3. What Strong Concurrent Bug Families Look Like

Strong bug families usually group around mechanisms like:

- stale snapshot + missing re-check
- memory ordering across variables
- retire / reclaim lifetime mismatch
- wrong wakeup / wrong owner handoff
- fast-path / fallback divergence
- partial completion / cancellation ordering

Weak bug families are usually:

- “this file uses atomics a lot”
- Rust / C++ type-system-only issues with no protocol-level state machine
- pure allocator / UB details with no tractable finite-state abstraction

---

## 4. Modeling Implications

When a concurrent-system finding is promising for TLA+, it usually implies one of:

- per-thread program counters
- shared state plus thread-local cached views
- split actions at confirm / publish / reclaim boundaries
- explicit retire / reclaim state
- bounded fault injection for stale snapshots, skipped re-checks, premature reclaim, wrong wakeup

If the issue depends entirely on language-level aliasing rules, provenance, or undefined behavior below the abstraction level you can model, it is usually better classified as test-verifiable or code-review-only.
