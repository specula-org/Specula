# Modeling Brief: DPDK rte_ring

## 1. System Overview

- **System**: DPDK rte_ring — lock-free multi-producer/multi-consumer ring buffer used in 10-100 Gbps networking (AWS, Azure, telecom)
- **Language**: C, ~1500 LOC core logic across `lib/ring/`
- **Protocol**: Two-phase lock-free enqueue/dequeue — CAS to reserve head slots, spin-wait to publish tail
- **Key architectural choices**:
  - Four sync modes: MP/MC (32-bit CAS), HTS (64-bit CAS, serialized), RTS (64-bit CAS with counters), SP/SC (no atomics)
  - Tail must advance **in-order** in MP/MC — this creates the "convoy problem" when a thread stalls
  - RTS solves this with a counter mechanism: only the last thread (matching counter) advances tail position
  - 32-bit head/tail counters with modular arithmetic, capacity bounded by 2^31
- **Concurrency model**: Lock-free, pinned-core polling (no preemption assumed). Designed for DPDK's run-to-completion threading model.

## 2. Bug Families

### Family 1: Two-Phase Commit Stall / Liveness (HIGH)

**Mechanism**: The two-phase protocol (CAS head → write data → update tail with in-order spin-wait) creates a window where a stalled/crashed thread blocks all subsequent tail updates, preventing consumers from seeing any new data.

**Evidence**:
- Historical: Producer stall causes 10+ second hangs with oversubscribed threads (mailing list report, users@dpdk.org/msg08325.html)
- Historical: Producer crash permanently deadlocks ring (confirmed by Konstantin Ananyev, dev@dpdk.org/msg289265.html)
- Historical: CAS-retry livelock under oversubscription (shines77/RingQueue#1, confirmed for DPDK)
- Code analysis: MP/MC tail-wait at `rte_ring_c11_pvt.h:36-37` — `rte_wait_until_equal_32` blocks indefinitely until predecessor updates tail
- Code analysis: HTS blocks ALL threads at `rte_ring_hts_elem_pvt.h:63` — `head != tail` means one thread is in-flight, all others spin
- Code analysis: RTS mitigates via counter mechanism at `rte_ring_rts_elem_pvt.h:24-62` — tail.cnt tracks completions, only last thread moves tail.pos
- Code analysis: RTS htd_max bounds head-tail divergence at `rte_ring_rts_elem_pvt.h:77`

**Affected code paths**:
- `__rte_ring_update_tail` (MP/MC spin-wait): `rte_ring_c11_pvt.h:35-37`
- `__rte_ring_hts_head_wait` (HTS serialization): `rte_ring_hts_elem_pvt.h:56-69`
- `__rte_ring_rts_update_tail` (RTS counter mechanism): `rte_ring_rts_elem_pvt.h:24-62`
- `__rte_ring_rts_head_wait` (RTS HTD throttle): `rte_ring_rts_elem_pvt.h:68-83`

**Suggested modeling approach**:
- Variables: `head[Side]`, `tail[Side]`, `phase[Thread]` ∈ {Idle, Reserved, Writing, Done}, `cnt[Side]` (for RTS)
- Actions: `Reserve` (CAS head), `WriteData` (copy elements), `PublishTail` (update tail with mode-specific logic)
- Add `Stall(t)` / `Crash(t)` action that freezes a thread between Reserve and PublishTail
- Model all three MT modes: MP/MC (in-order tail wait), HTS (head==tail gate), RTS (counter-based tail)
- Granularity: Reserve and PublishTail are separate actions (the stall window between them is the core issue)

**Priority**: High
**Rationale**: Fundamental design-level issue affecting production deployments. RTS mode's counter mechanism is the primary correctness target — it's complex enough to harbor subtle bugs. Three distinct algorithms (MP/MC, HTS, RTS) solving the same problem with different trade-offs makes this ideal for comparative model checking.

---

### Family 2: Memory Ordering / Stale Read Vulnerabilities (HIGH)

**Mechanism**: Incorrect or insufficient memory ordering in the head-move CAS / tail-update pattern allows threads to observe stale values of the opposing side's tail, causing underflow in free-space computation → data corruption.

**Evidence**:
- Historical: `a4ad0eba9d` (2025) — CRITICAL fix for default MP/MC mode, latent ~7 years
- Historical: `66d5f96278` (2025) — CRITICAL fix for HTS mode, latent ~5.5 years
- Historical: `36b69b5f95` (2025) — CRITICAL fix for RTS mode, latent ~5.5 years
- Historical: Gavin Hu 2018 fix — stale tail reads on ARM/POWER, up to 27.6% latency impact
- Code analysis: HTS `update_tail` stores 32-bit `pos.tail` while `head_wait` reads 64-bit `raw` — mixed-width atomic access (`rte_ring_hts_elem_pvt.h:42` vs `:61`)
- Code analysis: RTS producer releases 64-bit `tail.raw`, consumer acquires 32-bit sub-field — cross-width pairing

**Affected code paths**: `__rte_ring_headtail_move_head` (C11 path), `__rte_ring_hts_move_head`, `__rte_ring_rts_move_head`, all `update_tail` variants

**Suggested modeling approach**:
- Model "stale read" as nondeterministic: when a thread reads the opposing tail, it may see the current value OR any older value
- Variables: `visibleTail[Thread][Side]` — each thread's view of the opposing tail (can lag behind actual)
- Action: `StaleRead(t)` — thread t's view of opposing tail is set to any value between its last observation and the actual value
- Check: `RingSafety` — no thread reserves beyond actual capacity (free-space computation must not underflow)

**Priority**: High
**Rationale**: 4+ critical bugs over 7 years, all sharing the same mechanism. The Nov 2025 fixes demonstrate this family is still active. Memory ordering bugs are notoriously hard to find by testing (hidden on x86, manifests only on specific ARM variants). A stale-read model can catch the *consequence* (capacity underflow) even though TLA+ doesn't model memory ordering directly.

---

### Family 3: Peek Mode Atomicity Gaps (MEDIUM)

**Mechanism**: The START/FINISH split-operation API extends the two-phase window to user-controlled duration. Missing abort handling and double-START create deadlock or corruption.

**Evidence**:
- Code analysis: HTS double-START self-deadlocks — second `head_wait` spins forever (`rte_ring_peek_elem_pvt.h:119-135`)
- Code analysis: ST double-START creates overlapping reservations → data corruption on FINISH
- Code analysis: Crash between START/FINISH permanently deadlocks HTS ring, stalls ST ring
- Code analysis: Passing `n=0` to FINISH aborts (documented by example at `rte_ring_peek.h:36-41`)

**Affected code paths**: `__rte_ring_do_enqueue_start`, `rte_ring_enqueue_elem_finish`, `__rte_ring_hts_set_head_tail`, `__rte_ring_st_set_head_tail`

**Suggested modeling approach**:
- Extend the phase model: `phase[Thread]` ∈ {Idle, PeekStarted, PeekFinished}
- Action: `PeekStart(t)` — reserve slots, enter PeekStarted
- Action: `PeekFinish(t, n)` — commit n slots (n=0 for abort)
- Add `Crash(t)` between PeekStart and PeekFinish
- Check: no permanent deadlock after crash (liveness)

**Priority**: Medium
**Rationale**: Peek mode is less widely used than the core enqueue/dequeue, but it exercises the same two-phase protocol with an extended window. The double-START deadlock and crash-recovery gaps are concrete issues worth verifying.

---

### Family 4: RTS Counter Overflow / ABA (LOW)

**Mechanism**: The RTS 64-bit CAS packs (cnt, pos) into a single word. The 32-bit counter wraps at 2^32 operations, creating a theoretical ABA window.

**Evidence**:
- Code analysis: `rte_ring_rts_elem_pvt.h:169` — 64-bit CAS on `(cnt, pos)` pair
- Code analysis: At 100M ops/sec, counter wraps in ~43 seconds
- Code analysis: DPDK's pinned-core model mitigates this (no long preemptions), but VMs with live migration could trigger it

**Affected code paths**: `__rte_ring_rts_move_head`, `__rte_ring_rts_update_tail`

**Suggested modeling approach**:
- Model counter as a small finite domain (e.g., 0..3) to force wraparound
- Check if ABA causes duplicate slot reservation or double tail advance
- This is secondary to Family 1/2 but worth checking if counter domain is small enough

**Priority**: Low
**Rationale**: Theoretical vulnerability. DPDK's operational model (pinned cores) makes it practically safe, but the algorithm provides no formal guarantee. Model checking with small counter domains can verify robustness.

## 3. Modeling Recommendations

### 3.1 Model (with rationale)

| What | Why | How |
|------|-----|-----|
| Two-phase commit protocol | Family 1: core mechanism, 3 production-impact reports | Reserve (CAS head) and PublishTail as separate actions with thread scheduling between them |
| All 3 MT modes (MP/MC, HTS, RTS) | Family 1: comparative analysis of stall behavior | Mode parameter on ring; same invariants, different tail-update logic |
| RTS counter mechanism | Family 1: most complex protocol, primary correctness target | Model (cnt, pos) pair, counter-based tail advancement |
| Thread stall/crash | Family 1: the trigger for convoy/deadlock | Nondeterministic Stall(t) action that freezes a thread in Reserved phase |
| Stale reads of opposing tail | Family 2: root cause of 4+ critical bugs | Nondeterministic StaleRead — thread may see any older tail value |
| Peek START/FINISH | Family 3: extends two-phase window | Additional PeekStarted phase with crash between start/finish |
| Bounded counter (RTS) | Family 4: ABA verification | Small finite counter domain forces wraparound during model checking |

### 3.2 Do Not Model (with rationale)

| What | Why |
|------|-----|
| Element copy mechanics | Pure memory copying — no protocol logic. Integer overflow in scaling (Family 5) is a C-level arithmetic issue, not model-checkable |
| Ring creation / lifecycle | API safety issues (Family 4) are type-system/runtime-guard problems, not protocol logic |
| SP/SC mode | Single-threaded — no concurrency to model check |
| Zero-copy peek internals | Same protocol as regular peek, just returns pointers instead of copying. No additional concurrency concern |
| Generic vs C11 implementation | They implement the same algorithm with different barrier strategies. The stale-read model captures the consequence of ordering bugs without modeling barriers directly |
| `rte_ring_count` / `rte_ring_empty` accuracy | Known-documented best-effort behavior. Not a safety concern |
| Cache-line alignment / performance | Performance optimization, not correctness |

## 4. Proposed Extensions

| Extension | Variables | Purpose | Bug Family |
|-----------|-----------|---------|------------|
| Thread phases | `phase[Thread]` ∈ {Idle, Reserved, Writing, Done} | Model the two-phase commit window | Family 1 |
| Per-mode tail update | `mode` ∈ {MPMC, HTS, RTS} | Comparative analysis of three algorithms | Family 1 |
| RTS counters | `headCnt`, `tailCnt` | Model counter-based tail deferral | Family 1, 4 |
| HTD throttle | `htdMax` | Bound head-tail divergence in RTS | Family 1 |
| Thread stall | `stalled[Thread]` ∈ BOOLEAN | Model preemption / crash between phases | Family 1 |
| Stale tail view | `visibleTail[Thread]` | Model weak memory ordering effects | Family 2 |
| Peek phases | Extended phase ∈ {PeekStarted, PeekFinished} | Model START/FINISH split operations | Family 3 |

## 5. Proposed Invariants

| Invariant | Type | Description | Targets |
|-----------|------|-------------|---------|
| RingSafety | Safety | No data loss, no duplicate reads: every enqueued element is dequeued exactly once | Standard, all families |
| NoOverwrite | Safety | A producer never writes to a slot that a consumer hasn't finished reading | Family 1, 2 |
| NoStaleRead | Safety | A consumer never reads a slot that a producer hasn't finished writing | Family 1, 2 |
| CapacityBound | Safety | Number of in-flight elements never exceeds ring capacity | Family 2 (stale read → underflow) |
| TailMonotonicity | Safety | tail.pos is monotonically non-decreasing (modulo 2^32) | Family 1 |
| CounterConsistency | Safety | RTS: tail.cnt <= head.cnt always | Family 1, 4 |
| NoABA | Safety | No thread's CAS succeeds on a value that has wrapped around to a previous state | Family 4 |
| TailProgress | Liveness | If no thread is stalled and the ring is non-empty, tail eventually advances | Family 1 |
| RTSBoundedStall | Liveness | In RTS mode, if one thread stalls, other threads can still make progress (up to htd_max) | Family 1 |
| MPMCStall | Liveness (negative) | In MP/MC mode, one stalled thread blocks ALL tail progress — verify this is the case | Family 1 |
| HTSStall | Liveness (negative) | In HTS mode, one in-flight thread blocks ALL other threads — verify this is the case | Family 1 |
| PeekRecovery | Liveness | After a peek-START thread crashes, ring can be recovered via reset | Family 3 |

## 6. Findings Pending Verification

### 6.1 Model-Checkable

| ID | Description | Expected invariant violation | Bug Family |
|----|-------------|----------------------------|------------|
| MC-1 | RTS counter mechanism correctness under out-of-order thread completion | CounterConsistency, RingSafety | 1 |
| MC-2 | RTS with stalled thread: other threads can still enqueue/dequeue up to htd_max | RTSBoundedStall (should pass) vs MPMCStall (should fail for MP/MC) | 1 |
| MC-3 | Stale read of opposing tail causes capacity underflow | CapacityBound violation with StaleRead enabled | 2 |
| MC-4 | RTS counter ABA with small counter domain (e.g., 0..3) | NoABA, RingSafety | 4 |
| MC-5 | Peek double-START causes ring invariant violation | RingSafety (ST mode), TailProgress (HTS deadlock) | 3 |
| MC-6 | Peek crash-recovery: ring stuck after crash between START/FINISH | PeekRecovery (expected fail without reset) | 3 |
| MC-7 | MP/MC: producer crash → ring permanently stuck | TailProgress (expected fail) | 1 |

### 6.2 Test-Verifiable

| ID | Description | Suggested test approach |
|----|-------------|----------------------|
| TV-1 | Integer overflow in `nr_num = num * scale` (`rte_ring_elem_pvt.h:148`) | Unit test with esize=4096, large batch, verify element copy correctness |
| TV-2 | `count=1` creates zero-capacity ring | Create ring with count=1, verify enqueue returns 0 |
| TV-3 | `count=0` with EXACT_SZ creates zero-capacity ring | Create ring with count=0 + EXACT_SZ, check behavior |
| TV-4 | Peek FINISH on unsupported mode (release build) | Call peek APIs on MT_RTS ring in release build, check for UB |
| TV-5 | `htd_max` setter is not thread-safe | Concurrent `set_htd_max` + enqueue, use ThreadSanitizer |

### 6.3 Code-Review-Only

| ID | Description | Suggested action |
|----|-------------|-----------------|
| CR-1 | Mixed-width atomic access in HTS (32-bit store / 64-bit load) — formally UB in C11 | Align with peek-mode path that uses 64-bit store |
| CR-2 | Cross-width release/acquire in RTS (64-bit release / 32-bit acquire) | Document or align to same width |
| CR-3 | No esize stored in ring struct | Add esize field + runtime check in debug builds |
| CR-4 | HTD stale tail read in `__rte_ring_rts_head_wait` uses plain volatile | Use explicit atomic load with acquire |
| CR-5 | `rte_ring_reset` non-atomic across prod/cons | Document specific failure mode or use single atomic reset |

## 7. Reference Pointers

- **Full analysis report**: see the [Specula case-studies repository](https://github.com/specula-org/specula-case-studies) for the complete dpdk-ring analysis
- **Key source files**:
  - `lib/ring/rte_ring_elem_pvt.h` — core enqueue/dequeue (474 lines)
  - `lib/ring/rte_ring_c11_pvt.h` — C11 atomics CAS + tail update (143 lines)
  - `lib/ring/rte_ring_rts_elem_pvt.h` — RTS counter mechanism (282 lines)
  - `lib/ring/rte_ring_hts_elem_pvt.h` — HTS serialized mode (267 lines)
  - `lib/ring/rte_ring_peek_elem_pvt.h` — Peek START/FINISH (169 lines)
  - `lib/ring/rte_ring_core.h` — Data structures (164 lines)
- **Critical commits**: `a4ad0eba9d`, `66d5f96278`, `36b69b5f95` (memory ordering fixes, Nov 2025)
- **Mailing list threads**: LWP stall (users@dpdk.org/msg08325.html), producer crash (dev@dpdk.org/msg289265.html), count/empty RFC (dev@dpdk.org/msg165654.html)
- **ARM blog**: "When a barrier does not block: The pitfalls of partial order" (Herd7 litmus tests for the memory ordering bugs)
- **Test suite**: `app/test/test_ring.c` (functional), `app/test/test_ring_stress.c` + mode-specific stress tests (MP/MC, RTS, HTS, peek)
