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

## 5. Fault Model Reference

Concurrent systems do not have a single canonical fault model the way `crash + lose message + timeout` is canonical for distributed systems. The eight families below are **starting points** for the adversary, derived from where bugs have actually been found across the case-study set. They are a checklist for completeness, not a constraint on design.

If the target has a domain-specific failure mode that fits its semantics better — NIC packet reorder, signal-during-RMW, eBPF map preemption, CPU offlining, page fault in critical section — model that instead. The list is non-exhaustive on purpose.

The first family below (Thread Interleaving) is the universal headline and applies to every concurrent system. The remaining seven are situational; their relevance shifts by sub-category — see the prioritization table at the end of this section.

### 5.1 Thread Interleaving / Action Granularity — *the headline family*

**This is the most important fault family by a wide margin.** Production concurrent bugs are overwhelmingly pure interleaving bugs — two correct-looking operations run in an order the author did not consider. Model checking is uniquely good at exposing these: TLC exhaustively explores all interleavings, which testing cannot. The other seven families are situational; this one is universal and is where the most modeling effort should go.

The adversary here is **already present** in TLA+'s default interleaving semantics. You do not add it — you express it through **action granularity**. The granularity decisions, made well, expose the interleaving bugs the spec is supposed to find. Made poorly, they hide them.

Modeling discipline:

- **Split actions at every observable boundary.** Every CAS, every atomic load whose result feeds a downstream decision, every store another thread may observe — each is a candidate action boundary.
- **Do not collapse multi-step protocols into one action.** If the implementation does `load → check → CAS`, the spec must have three actions, not one. The bug that lives in the gap between steps is invisible if the gap is not modeled.
- **Match the implementation's interruption points.** Holding a lock through three atomic ops = one action. Releasing the lock between ops = three actions. The spec's action structure should mirror where the real code can be preempted.
- **Resist over-collapsing for state-space reasons.** "Modeled as one action because BFS would explode otherwise" is a faithfulness regression — flag it, do not silently accept it. Use counter bounds, scenario configs, or symmetry to control state space, not coarsening of atomicity.

Spec hint: this is **not** modeled by adding an `MCPreempt` action. It is modeled by how you split actions in the first place. An explicit `MCPreempt` is only useful when you deliberately cut a coarse action into pre/post halves and the rest of the spec is already at the right granularity.

Verification heuristic: for every pair of consecutive actions in the spec, ask "could the implementation be preempted between these two operations?" If yes, are they separate actions, and is the intermediate state captured precisely? If no, can the implementation guarantee atomicity through hardware (single CAS, single atomic store) or through a held lock? Either of these is fine; "we collapsed it because we wanted simpler invariants" is not.

Why this matters more than the other families: the other seven require their specific mechanism to be present (an allocator, a CAS, a wait/notify pair, a futures runtime, etc.). Thread interleaving is **always** present in any concurrent system and is the substrate on which most real bugs are exposed. The case-study set confirms this — the bugs found are predominantly interleaving bugs that the right action granularity made visible, with memory-order or OOM bugs as the long tail.

### 5.2 Cancellation / Future Drop / Close

Adversary cancels an in-flight operation at any await / yield / external-completion point.

- Applicable when: async runtime, futures, channels, detachable tasks, or any API documenting "may be cancelled" or "may be dropped".
- Spec hint: per-await `MCDropFuture` action under counter bound; see `kanal!MCDropRecvFutureCancel`. The cancellation must reach the same cleanup path as a normal completion.
- Skip when: API explicitly forbids cancellation between begin/end (rare).
- Existing examples: kanal (2 bugs), papaya (1 bug), libgomp (omp_fulfill_event deadlock).

### 5.3 Allocator Failure / OOM

`malloc` / `Box::new` / table-grow returns failure non-deterministically at allocation sites inside the modeled scope.

- Applicable when: the modeled path allocates — especially resize, snapshot capture, retire-bag growth, table promotion, queue-node alloc.
- Spec hint: bounded `MCAllocFail(site)` driving the allocation site to its error branch. Check that the error propagates without leaking partially-published state, holding locks, or inflating bookkeeping counters.
- Skip when: the system is documented to abort on OOM and aborts are acceptable in its deployment.

### 5.4 CAS Spurious Failure (cas_weak)

`compare_exchange_weak` (or equivalent) fails even when the expected value matches.

- Applicable when: implementation uses `compare_exchange_weak`, common in performance-tuned Rust / C++ lock-free code.
- Spec hint: tag each modeled CAS as weak/strong. Weak CAS gets an extra `SpuriousFail` branch under counter bound. Verify the surrounding retry loop is correct under spurious failure.
- Skip when: implementation uses only `compare_exchange_strong`.

### 5.5 Memory Ordering / Visibility Bridges

Model the implementation's actual memory-ordering labels first, then look for cross-variable visibility assumptions that those labels may not justify.

- Applicable when: lock-free implementation uses mixed `Ordering::*` annotations and the safety argument depends on cross-variable visibility (see § 2.3).
- Spec hint: **do not** attempt full TSO / ARM modeling. Label each load/store in the spec with the C11/Rust ordering actually used in the implementation. Add bounded visibility-gap actions only for bridges that the implementation's real labels leave ambiguous.
- Discipline: any counterexample requires manual review against the real hardware model. Many violations are spurious because actual TSO / ARM rules out the interleaving that a simplified TLA+ visibility model allows.
- Skip when: implementation uses only `seq_cst` (rare in performance-sensitive lock-free code).

**Forbidden: adversaries whose only value is TLA+-reproduction of an already-fixed bug.** If your finding's contribution reduces to "we re-derived a result the upstream commit and its regression test already establish" — drop it. The information added is zero; only the medium (TLA+ vs `cargo test`) is different.

A practical litmus: if the adversary's effect on the spec can be obtained by `git revert <commit>` for some past commit, you are almost always in this case — answer-key-guided regression demonstration.

The "sensitivity" / "robustness check" framing does not rescue this. If the only conclusion you can write about a violation is "already fixed by PR #N — no action needed," the work added nothing. Treat the closed-PR list as evidence of mechanism bug-proneness in modeling-brief § 2, not as a target set for the spec to re-enumerate.

Concrete patterns this rule retires:
- `MCRelaxOrdering(site)` / `MCPickRelaxSite(site)` whose `RelaxSites` set is 1-to-1 with closed upstream commits that introduced the current SC labels (e.g., arc-swap rounds 2/3/4 enumerating sites at `(#76, #198, #204, #195, #164)`).
- `MCRevert<X>` actions that disable a guard / check added by a known fix commit.
- Counter-bounded actions inserted specifically to recreate the pre-fix interleaving documented in some past issue's comments.

### 5.6 ABA / Pointer Reuse

Same address (or slot, or generation tag) is reused while another thread holds a stale snapshot.

- Applicable when: pointer-based lock-free with reclamation (Treiber stack, Michael-Scott queue, lock-free maps), counter-tagged versions, or slot-recycling structures.
- Spec hint: explicit slot or generation token; reclamation returns the slot to a free pool; CAS uses `(pointer, tag)` tuple when the implementation does.
- Skip when: implementation guarantees no reuse within any reader's lifetime (e.g., epoch GC with proven quiescent period — but the property still needs an invariant).

### 5.7 Caller Misuse / Adversarial Client

Client makes call sequences that are documented as legal but unfriendly: double-init, concurrent iter + modify, drop-while-borrowed via raw API, lock-ordering across multiple library calls.

- Applicable when: library exposes an API surface with non-trivial documented contract.
- Spec hint: a small `ClientHarness` action set drives the library through stress sequences (legal but adversarial). This is harness-level, not internal-state-level — the harness sits outside the library spec and chooses call sequences non-deterministically.
- Skip when: API is single-call-per-thread with no inter-call state.

### 5.8 Spurious / Lost Wakeup

`condvar.wait` returns without a matching `notify`, or `notify` arrives but no thread is parked, or wakeup is delivered to the wrong waiter.

- Applicable when: futex-based, condvar-based, parker-based, or atomic-flag-with-park synchronization.
- Spec hint: `MCSpuriousWake(t)` under bound; `notify` retried in a loop in spec, mirroring the implementation's `while (!cond) wait()`.
- Skip when: synchronization is purely atomic-counter-based with no wait/notify.
- Existing examples: libgomp omp_fulfill_event deadlock (lost-wakeup variant, found via TLC).

---

### Sub-Category Prioritization

5.1 (Thread Interleaving) is universal — model it for every concurrent spec. The remaining families' priority shifts by sub-category. Use this table to decide where to invest beyond 5.1, and what is safe to skip.

| Sub-category | Typical examples | Priority families (after 5.1) | Often skip |
|---|---|---|---|
| Lock-free data structures | Treiber stack, Michael-Scott queue, dpdk-ring | 5.5 MemOrder, 5.6 ABA, 5.7 Caller | 5.2 Cancel, 5.8 Wakeup |
| Synchronization primitives | mutex, condvar, futex, parker | 5.8 Wakeup, 5.7 Caller (lock order) | 5.5 MemOrder, 5.6 ABA |
| Concurrent runtimes | OpenMP, tokio executor, fiber pools | 5.2 Cancel, 5.3 OOM | 5.5 MemOrder, 5.6 ABA |
| Channels / message passing | kanal, tokio-broadcast, MPSC | 5.2 Cancel/Drop/Close | 5.5 MemOrder, 5.6 ABA |
| Concurrent collections | flurry, scc, papaya, crossbeam-skiplist | 5.7 Caller (iter+modify), 5.6 ABA, 5.3 OOM (resize) | 5.8 Wakeup |
| Reader-writer separation | arc-swap, crossbeam-epoch, left-right | 5.5 MemOrder, 5.6 Reuse | 5.2 Cancel, 5.8 Wakeup |

The differences matter: lock-free data structures and synchronization primitives have almost disjoint primary failure modes. A spec for a futex-based parker that invests heavily in memory-ordering adversaries is misallocated effort; a spec for a Michael-Scott queue that invests in lost-wakeup is similarly misallocated.

If the target is a hybrid (e.g., a concurrent collection that internally uses a parker), take the union of the relevant rows.

### Composition

Several families compose meaningfully: `cancellation + allocator failure` exercises whether the cancel path itself can leak under OOM; `memory ordering + ABA` exercises ABA detection under weakened visibility. Compose only after each family passes individually — composition explodes state space and clouds blame attribution.

### When None of These Fits

If the target's most realistic fault is not on this list — a JIT compiler reordering a barrier, a kernel preempting in a critical section that holds a spinlock, a NIC delivering packets out of order — model that directly. The eight families above are the most common starting points across the case-study set, not a definition of "fault model".
