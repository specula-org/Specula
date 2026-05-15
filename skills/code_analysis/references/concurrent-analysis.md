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

---

## 5. Fault Model — Vocabulary, Not Checklist

The labels below are a vocabulary for talking about concurrent failure modes. They are **not** a checklist; do not assume your target needs all of them, or even any of them beyond what its actual code suggests. Each target deserves a case-specific analysis grounded in its own code evidence — when none of the labels fit, name the failure mode yourself and proceed.

### 5.1 Thread Interleaving / Action Granularity

The substrate of almost every concurrent bug — two correct-looking operations run in an order the author did not consider. TLA+ already gives you interleaving for free; the only question is action granularity. Split actions where the implementation can be preempted (between atomic ops, across lock release, at any observable boundary). Avoid collapsing multi-step protocols (`load → check → CAS`) into a single action just to control state space — that hides the bug rather than finding it.

This is base-spec design, not an MC wrapper. If you find yourself adding `MCPreempt`, ask first whether the underlying actions are at the right granularity.

### 5.2-5.8 — Other Common Failure Modes

These are situational. Use them only if your target's actual code exposes the mechanism, and only model what the open question demands. Each entry is a label; the implementation should come from your case, not from imitating other case studies.

- **5.2 Cancellation / future drop / close** — cancellation reaches the same cleanup path as normal completion (async runtimes, futures, channels, detachable tasks).
- **5.3 Allocator failure / OOM** — allocation sites return failure; the error path doesn't leak partially-published state, hold locks, or inflate counters.
- **5.4 CAS spurious failure** — `compare_exchange_weak`-style retry loops survive failures that aren't caused by an actual value change.
- **5.5 Memory ordering / visibility bridges** — cross-variable visibility assumptions that the implementation's actual `Ordering::*` labels may or may not justify.
- **5.6 ABA / pointer reuse** — slot or generation reuse while another thread holds a stale snapshot.
- **5.7 Caller misuse / adversarial client** — legal-but-stressful call sequences (double-init, concurrent iter+modify, drop-while-borrowed, lock-ordering across calls).
- **5.8 Spurious / lost wakeup** — `wait` returns without `notify`, or `notify` reaches no waiter, or wakeup goes to the wrong waiter.

If your target's most realistic failure mode isn't named above (JIT barrier reorder, kernel preemption in a critical section, NIC packet reorder, signal during RMW, etc.), describe it directly. The vocabulary is not a closed list.

### Caveat for 5.5 (memory ordering): no answer-key adversaries

There is one anti-pattern we've watched repeatedly produce zero-value findings: adversaries whose only effect is to reproduce an already-fixed bug. If you can characterise the adversary's effect on the spec as "equivalent to `git revert <commit>`" for some past commit — drop it. The MC run produces no information the closed PR didn't already record, no matter what the wrapper is named or which cfg houses it. Closed PRs are evidence of mechanism bug-proneness (§ 2 of the modeling brief); they are not a target list for the spec to re-enumerate. See `modeling-brief-format.md` § 6.1 (output-value litmus) and `bug-archaeology.md` § 1.4 (value-driven containment).

### Composition

Some families compose: cancellation + allocator failure exercises whether the cancel path leaks under OOM; ABA + memory ordering exercises detection under weakened visibility. Compose only when the open question requires it — composition explodes state space and clouds attribution.
