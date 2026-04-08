# Concurrent System Trace Collection: Timebox Approach

This guide describes the trace collection methodology for **Category B systems** — concurrent and lock-free data structures where operations are ns-level and mutex-based tracing causes unacceptable probe effects.

**When to use**: DPDK rte_ring, arc-swap, libomp, libgomp, crossbeam-epoch, and similar systems where core operations are CAS/atomic/spin-loop based.

**Reference**: OmniLink (Hackett et al., arXiv 2601.11836, 2026) — timebox-based linearization for concurrent systems. CONVEROS (Tang et al., ATC'25) — missing event approach for OS concurrency modules.

---

## Background: Why Standard Tracing Fails for Concurrent Systems

In standard (Category A) tracing, all threads write to a single file via mutex:

```
Thread A:  ──op──[LOCK─emit─fflush─UNLOCK]──────────
Thread B:  ────op──────[WAIT]──[LOCK─emit─fflush─UNLOCK]
```

For ns-level operations, this causes:
1. **Probe effect**: mutex hold time (μs) >> operation time (ns), changing thread scheduling
2. **Artificial serialization**: mutex forces a total order that doesn't exist in reality
3. **Heisenbug suppression**: race conditions disappear because mutex delays mask timing windows

The timebox approach eliminates all three problems.

---

## Architecture Overview

```
Instrumentation              Post-processing              Validation (Trace.tla)

Thread 0 → trace-0.ndjson ─┐
Thread 1 → trace-1.ndjson ─┼→ merge + timestamp compress → TLC searches partial order
Thread 2 → trace-2.ndjson ─┘

Per-thread file, no mutex       Combine into per-thread      ViablePIDs constrains
rdtsc [start, end] interval     arrays, compress timestamps   which threads can step
State captured outside interval                               State validation retained
```

---

## Step 1: Per-Thread Trace Writer

Each thread writes to its own file. No mutex, no contention.

### C Example

```c
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct {
    FILE *fp;
    int tid;
} tl_trace_t;

static __thread tl_trace_t __tl_trace = {NULL, -1};

// rdtsc with memory fence — prevents CPU reordering, ~25 cycles
static inline uint64_t trace_rdtsc(void) {
    unsigned lo, hi;
    __asm__ volatile (
        "mfence\n\t"
        "rdtsc"
        : "=a"(lo), "=d"(hi)
    );
    return ((uint64_t)hi << 32) | lo;
}

// Initialize: each thread opens its own file
void trace_thread_init(int tid, const char *prefix) {
    char path[256];
    snprintf(path, sizeof(path), "%s-thread-%d.ndjson", prefix, tid);
    __tl_trace.fp = fopen(path, "w");
    __tl_trace.tid = tid;
}

// Emit: no mutex, direct write to thread-local file
void trace_emit(const char *json_line) {
    if (__tl_trace.fp) {
        fputs(json_line, __tl_trace.fp);
        fputc('\n', __tl_trace.fp);
    }
}

// Shutdown: flush and close
void trace_thread_shutdown(void) {
    if (__tl_trace.fp) {
        fflush(__tl_trace.fp);
        fclose(__tl_trace.fp);
        __tl_trace.fp = NULL;
    }
}
```

### Rust Example

```rust
use std::cell::RefCell;
use std::fs::File;
use std::io::{BufWriter, Write};

thread_local! {
    static TRACE_WRITER: RefCell<Option<BufWriter<File>>> = RefCell::new(None);
    static TRACE_TID: RefCell<i32> = RefCell::new(-1);
}

fn trace_rdtsc() -> u64 {
    let lo: u32;
    let hi: u32;
    unsafe {
        core::arch::x86_64::_mm_mfence();
        core::arch::asm!("rdtsc", out("eax") lo, out("edx") hi);
        core::arch::x86_64::_mm_mfence();
    }
    ((hi as u64) << 32) | lo as u64
}

pub fn trace_thread_init(tid: i32, prefix: &str) {
    let path = format!("{}-thread-{}.ndjson", prefix, tid);
    let file = File::create(&path).expect("Failed to open trace file");
    TRACE_WRITER.with(|w| *w.borrow_mut() = Some(BufWriter::new(file)));
    TRACE_TID.with(|t| *t.borrow_mut() = tid);
}

pub fn trace_emit(json_line: &str) {
    TRACE_WRITER.with(|w| {
        if let Some(ref mut writer) = *w.borrow_mut() {
            writeln!(writer, "{}", json_line).ok();
        }
    });
}
```

### Platform Note (non-x86)

`rdtsc` is x86-only. For other architectures:
- **ARM (aarch64)**: use `cntvct_el0` via `mrs` instruction (~similar overhead)
- **Portable fallback**: `clock_gettime(CLOCK_MONOTONIC)` — higher overhead (~50-100ns) but works everywhere
- Choose based on whether the target system runs on x86 in practice

---

## Step 2: Timebox Instrumentation Pattern

Each trace event wraps the actual operation with `[start, end]` timestamps. State is captured **outside** the interval to keep it tight.

### Basic Pattern

```c
// 1. Record start time
uint64_t t_start = trace_rdtsc();

// 2. Execute the actual operation (this is what we're tracing)
result = do_operation(args);

// 3. Record end time
uint64_t t_end = trace_rdtsc();

// 4. Capture state AFTER the interval (does not widen [start, end])
int field1 = read_shared_field1();
int field2 = read_shared_field2();

// 5. Emit to thread-local file (no mutex)
snprintf(buf, sizeof(buf),
    "{\"tag\":\"trace\",\"event\":\"%s\",\"tid\":%d,"
    "\"start\":%lu,\"end\":%lu,"
    "\"state\":{\"field1\":%d,\"field2\":%d},"
    "\"args\":{...}}",
    event_name, tid, t_start, t_end, field1, field2);
trace_emit(buf);
```

### Why State Capture is Outside the Interval

The interval `[start, end]` should be as tight as possible — it determines how much concurrency TLC must explore. If state capture (reading multiple shared fields, formatting JSON) is inside the interval:

```
Tight interval (state outside):   [start ── operation ── end] capture state → emit
  → interval = operation time only (~10-100ns)

Wide interval (state inside):     [start ── operation ── capture state ── end]
  → interval = operation + capture time (~200-500ns)
  → 2-5x more overlap with other threads → more TLC branching
```

State captured after `end` may include changes from other threads that happened between operation and capture. This is fine — TLC explores all orderings and will find the one consistent with the captured state.

### Tightening Intervals with Refinement

For operations with significant setup/teardown around the critical section:

```c
uint64_t t_start = trace_rdtsc();   // broad start

// Setup: lock acquisition, argument validation, etc.
acquire_lock();
validate_args();

uint64_t t_refined_start = trace_rdtsc();   // tight start: just before critical op

// Critical operation
result = cas(&shared_var, expected, desired);

uint64_t t_refined_end = trace_rdtsc();     // tight end: just after critical op

// Teardown: cleanup, unlock, etc.
release_lock();

uint64_t t_end = trace_rdtsc();     // broad end

// Use refined interval for tighter ordering
snprintf(buf, ..., t_refined_start, t_refined_end, ...);
```

Use refinement when the critical section is a small part of a larger function. OmniLink calls these `refine_op_start()` / `refine_op_end()`.

### Entire Hot Path Must Be Lock-Free

Making `emit()` lock-free is necessary but not sufficient. The **entire code path from instrumentation site to file write** must be free of shared locks. Common violations:

| Pattern | Problem | Fix |
|---------|---------|-----|
| ID registry (`table_id()`, `buffer_id()`) | Mutex on every event to map pointer → sequential ID | Thread-local cache; Mutex only on first encounter |
| Thread name allocation | Mutex or atomic counter on every event | Cache in thread-local after first call |
| Global counter (event sequence number) | Atomic fetch_add serializes all threads | Remove — timebox ordering replaces sequence numbers |
| Shared lookup table | Mutex to read mapping on every emit | Clone into thread-local at init or cache on first access |

**Rule**: grep your trace module for `lock()`, `Mutex`, and `fetch_add` calls. If any of them execute on every trace event (not just during initialization), they reintroduce the probe effect that timebox is designed to eliminate.

**Fix pattern** (Rust): thread-local cache with lazy global fallback:

```rust
thread_local! {
    static LOCAL_ID_CACHE: RefCell<HashMap<usize, u64>> = RefCell::new(HashMap::new());
}

pub fn resource_id(raw_addr: usize) -> u64 {
    // Fast path: thread-local, no lock
    LOCAL_ID_CACHE.with(|cache| {
        if let Some(&id) = cache.borrow().get(&raw_addr) {
            return id;
        }
        // Slow path: register once in global map
        let id = GLOBAL_REGISTRY.lock().unwrap()
            .entry(raw_addr).or_insert_with(|| COUNTER.fetch_add(1, Ordering::Relaxed))
            .clone();
        cache.borrow_mut().insert(raw_addr, id);
        id
    })
}
```

**Fix pattern** (C): thread-local cache array:

```c
// Fast path: thread-local cache (no lock)
static __thread struct { uintptr_t addr; uint64_t id; } __id_cache[16];
static __thread int __id_cache_len = 0;

uint64_t resource_id(uintptr_t addr) {
    for (int i = 0; i < __id_cache_len; i++)
        if (__id_cache[i].addr == addr) return __id_cache[i].id;
    // Slow path: global registry (locked, runs once per resource per thread)
    uint64_t id = register_global(addr);
    if (__id_cache_len < 16)
        __id_cache[__id_cache_len++] = (typeof(__id_cache[0])){addr, id};
    return id;
}
```

---

## Step 3: Trace Format

### Per-Thread NDJSON

Each thread's file contains its events in execution order:

```json
{"tag":"trace","event":"ReserveProd","tid":0,"start":1000,"end":1050,"state":{"prodHead":4,"prodTail":2},"args":{"n":2}}
{"tag":"trace","event":"WriteProd","tid":0,"start":1100,"end":1200,"state":{"prodHead":6,"prodTail":2},"args":{"values":[10,20]}}
{"tag":"trace","event":"PublishProd","tid":0,"start":1250,"end":1300,"state":{"prodHead":6,"prodTail":6}}
```

### Required Fields

| Field | Type | Description |
|-------|------|-------------|
| `tag` | `"trace"` | **Mandatory**. Trace.tla filters on this. |
| `event` | string | Action name matching Trace.tla |
| `tid` | int | Thread ID (0-indexed) |
| `start` | uint64 | rdtsc timestamp at operation start |
| `end` | uint64 | rdtsc timestamp at operation end |
| `state` | object | State snapshot (captured outside interval) |
| `args` | object | Operation arguments (optional, for constraining TLC) |
| `msg` | object | Message fields (optional, for message-passing actions) |

---

## Step 4: Post-Processing

Merge per-thread files, compress timestamps, output per-thread arrays.

### Preprocessor Script

```python
#!/usr/bin/env python3
"""Merge per-thread timebox traces into a single JSON file for TLC."""

import json
import glob
import sys

def merge_and_compress(trace_dir, output_path):
    # 1. Read all per-thread files
    per_thread = {}
    all_timestamps = set()

    for path in sorted(glob.glob(f"{trace_dir}/trace-thread-*.ndjson")):
        tid = int(path.split("-thread-")[1].split(".")[0])
        events = []
        for line in open(path):
            line = line.strip()
            if not line:
                continue
            event = json.loads(line)
            if event.get("tag") != "trace":
                continue
            events.append(event)
            all_timestamps.add(event["start"])
            all_timestamps.add(event["end"])
        per_thread[tid] = events

    # 2. Timestamp compression: raw rdtsc → dense integers
    #    Preserves ordering relationships, reduces TLC state space
    sorted_ts = sorted(all_timestamps)
    ts_map = {ts: idx + 1 for idx, ts in enumerate(sorted_ts)}  # 1-indexed for TLA+

    for tid in per_thread:
        for event in per_thread[tid]:
            event["start"] = ts_map[event["start"]]
            event["end"] = ts_map[event["end"]]

    # 3. Output: structure for TLC ingestion
    output = {
        "num_threads": len(per_thread),
        "max_timestamp": len(sorted_ts),
        "traces": {str(tid): events for tid, events in sorted(per_thread.items())}
    }

    with open(output_path, "w") as f:
        json.dump(output, f, indent=2)

    print(f"Merged {sum(len(v) for v in per_thread.values())} events "
          f"from {len(per_thread)} threads, "
          f"{len(sorted_ts)} unique timestamps")

if __name__ == "__main__":
    merge_and_compress(sys.argv[1], sys.argv[2])
```

### Timestamp Compression

Raw rdtsc values are large (e.g., `48372719384027`). Compressing to dense integers:
- Preserves all ordering relationships (`a < b` before compression ↔ `a' < b'` after)
- Preserves interval overlap (`[a,b] ∩ [c,d] ≠ ∅` ↔ `[a',b'] ∩ [c',d'] ≠ ∅`)
- Reduces TLC state space (smaller integer domain)

---

## Step 5: Trace.tla for Timebox Validation

The trace validation module differs from Category A. Instead of a single global trace sequence, it maintains per-thread sequences with a partial-order constraint.

### Template

```tla
---- MODULE Trace ----
EXTENDS base, Json, Naturals, Sequences, TLC

\* Load per-thread traces from preprocessed JSON
CONSTANT TraceFile
traceData == JsonDeserialize(TraceFile)
traces == traceData.traces

\* Per-thread program counter: index into each thread's trace
VARIABLE pc

traceVars == <<pc>>
allVars == <<vars, traceVars>>  \* vars from base spec + trace bookkeeping

\* Threads that still have unconsumed events
ThreadsWithEvents == { tid \in DOMAIN traces : pc[tid] <= Len(traces[tid]) }

\* --- Core: Partial Order via Timebox Intervals ---
\*
\* Thread `tid` is viable (can take its next step) iff no other thread
\* has a pending event that COMPLETED BEFORE `tid`'s next event STARTED.
\* If such a thread exists, it must go first (real-time ordering).
\* Overlapping intervals → both viable → TLC explores both orderings.
ViablePIDs ==
    { tid \in ThreadsWithEvents :
        ~ \E tid2 \in ThreadsWithEvents :
            /\ tid2 /= tid
            /\ traces[tid2][pc[tid2]].end < traces[tid][pc[tid]].start }

\* --- Initialization ---
TraceInit ==
    /\ Init                              \* base spec Init
    /\ pc = [tid \in DOMAIN traces |-> 1]

\* --- Next State: pick a viable thread, match its event ---
TraceNext ==
    \* Normal step: consume an event from a viable thread
    \/ /\ ThreadsWithEvents /= {}
       /\ \E tid \in ViablePIDs :
            LET logline == traces[tid][pc[tid]] IN
            /\ MatchEvent(tid, logline)         \* defined below: dispatch + state check
            /\ pc' = [pc EXCEPT ![tid] = pc[tid] + 1]
    \* Silent actions (for unobserved internal transitions)
    \/ /\ ThreadsWithEvents /= {}
       /\ SilentActions                         \* from base spec, with constraints
       /\ UNCHANGED pc
    \* Stuttering after trace is fully consumed
    \/ /\ ThreadsWithEvents = {}
       /\ UNCHANGED allVars

\* --- Event Matching (customize per system) ---
MatchEvent(tid, logline) ==
    CASE logline.event = "ActionA" ->
            \* State validation: check fields that are reliably captured
            /\ stateVar1 = logline.state.field1
            /\ stateVar2 = logline.state.field2
            /\ ActionA(tid, logline.args.param1)
      [] logline.event = "ActionB" ->
            /\ ActionB(tid, logline.args.param1, logline.args.param2)
      \* ... add cases for each traced action

\* --- Spec ---
TraceSpec == TraceInit /\ [][TraceNext]_allVars

\* --- Validation Property ---
\* Trace is valid iff all events are eventually consumed
TraceFullyConsumed == <>(ThreadsWithEvents = {})
====
```

### How TLC Searches

At each step, `\E tid \in ViablePIDs` is an existential quantifier. TLC tries every viable thread:

1. If only one thread is viable → deterministic step (no branching)
2. If multiple threads are viable (overlapping intervals) → TLC forks, exploring each choice
3. Branches where preconditions fail or states don't match → pruned (dead ends)
4. If any path fully consumes all events → trace is valid

State validation **helps** by pruning incorrect orderings early, reducing the search space.

### Silent Actions

Silent actions are still needed for unobserved transitions (same as Category A). Constrain them to prevent state explosion:
- Guard on next trace event type
- Limit to specific threads/rounds
- Use ordering constraints for non-observed participants

---

## Step 6: Trace.cfg

```
SPECIFICATION TraceSpec

CONSTANT TraceFile = "traces/merged.json"

\* Check that trace is fully consumed (all events matched)
PROPERTY TraceFullyConsumed

\* Or use deadlock detection: if trace isn't fully consumed, TLC deadlocks
\* INVARIANT TraceNotStuck

\* Optional: model constants from base spec
\* CONSTANT Thread = {"t0", "t1", "t2", "t3"}
```

---

## Search Space Control

The timebox approach trades trace correctness for TLC search time. Key controls:

| Technique | Effect | How |
|-----------|--------|-----|
| **Tight intervals** | Fewer overlaps → fewer branches | Use `refine_op_start/end` around critical section |
| **Short traces** | Fewer total events → smaller state graph | Design focused test scenarios, 50-200 events per trace |
| **More traces** | Compensate for shorter length | Run many test executions, validate each separately |
| **State validation** | Prune impossible orderings early | Keep state capture, validate known-accurate fields |
| **Timestamp compression** | Smaller integer domain | Preprocessor maps raw timestamps to dense integers |

### Recommended trace lengths

| System complexity | Events per trace | Expected TLC time |
|-------------------|------------------|--------------------|
| Simple (2 threads, 1 operation type) | 50-100 | seconds |
| Medium (4 threads, 3-5 operation types) | 100-300 | minutes |
| Complex (8+ threads, many operation types) | 200-500 | minutes to hours |

Run many short traces rather than few long ones.

---

## Trace Quality Criteria

A Category B trace is only useful if it actually exercises the timebox mechanism. Traces where all events are sequential (no interval overlap) degrade to Category A behavior — the ViablePIDs search adds overhead without benefit.

### Minimum Quality Requirements

1. **Concurrent overlap**: At least 20% of event pairs across different threads should have overlapping `[start, end]` intervals. If 0 pairs overlap, the trace is effectively sequential and the timebox mechanism is not being tested.

2. **Cross-thread interleaving**: Operations from different threads must be **interleaved in time**, not sequential (all of thread A, then all of thread B). Design test scenarios where threads operate simultaneously on shared data.

3. **Event type coverage**: Every instrumented event type should appear in at least one trace. An event type that is instrumented but never tested is a coverage gap — the trace validation can't verify that the spec handles it correctly.

### How to Check

After preprocessing, inspect the compressed timestamps:

```
Good (overlap):                    Bad (sequential):
  worker: Push [1,2] [3,4]          worker: Push [1,2] [3,4] [5,6] [7,8]
  s1: StealBegin [2,5]              s1: StealBegin [9,10]
  s2: StealBegin [3,6]              s2: StealBegin [11,12]
  ↑ overlapping intervals            ↑ no overlap — timebox not tested
```

### Test Scenario Design Principles

| Principle | What to do | Why |
|-----------|-----------|-----|
| **Simultaneous start** | Use barriers to start all threads at the same time | Ensures operations overlap rather than serialize |
| **Interleaved workload** | Threads do work in small batches, not all-at-once | Creates overlap between producer and consumer operations |
| **Contention-heavy scenarios** | Multiple stealers + active worker simultaneously | Exercises the exact races that timebox ordering must handle |
| **Mix of outcomes** | Include both successful and failed operations (CAS fail, empty deque) | Tests spec's handling of contention outcomes |

### Example: Good vs Bad Test Design

```
BAD: Worker pushes all, then stealers start
  worker: push push push push push  →  pop pop pop
  s1:                                    steal steal steal
  s2:                                    steal steal steal
  (push phase has zero concurrency)

GOOD: Worker pushes while stealers are active
  worker: push push → pop → push push → pop pop
  s1:       steal → steal → steal
  s2:            steal → steal → steal
  (pushes and steals overlap — real concurrency)
```

### Coverage Checklist

Before declaring trace generation complete, verify:

- [ ] Each instrumented event type appears in at least one trace
- [ ] At least one trace has genuine cross-thread interval overlap
- [ ] At least one trace includes contention (CAS failures, empty results)
- [ ] At least one trace exercises the system's resize/growth/reclaim paths (if modeled)

---

## Comparison: Category A vs Category B

| Aspect | Category A (Distributed) | Category B (Concurrent) |
|--------|--------------------------|-------------------------|
| Trace file | Single file, mutex-protected | Per-thread files, no mutex |
| Timestamp | Monotonic clock (ms/μs) | rdtsc (ns) |
| Event ordering | Fixed by mutex write order | Partial order from intervals |
| TLC matching | Linear: `TraceLog[l]`, `l' = l+1` | Branching: `ViablePIDs`, `pc[tid]' = pc[tid]+1` |
| State validation | Always (full or weak) | Always (captured outside interval) |
| Probe effect | Negligible | Eliminated |
| TLC search space | O(N) | O(N × 2^K), K = concurrent pairs |
| Silent actions | Needed | Needed (same) |

---

## Related Work

- **OmniLink** (Hackett et al., 2026): Timebox + linearizability for black-box concurrent systems. Records operations only (no state). We extend this by retaining state validation for stronger bug detection.
- **CONVEROS** (Tang et al., ATC'25): Missing event markers for OS kernel concurrency. Uses explicit developer annotations for uncertain regions. Alternative to timebox when rdtsc is unavailable.
- **PGo/TraceLink** (Hackett et al., ASPLOS'23): Vector clocks for distributed systems. Appropriate for Category A but too invasive for Category B.
