# Trace Module Patterns

Language-specific patterns for the trace emission library. Adapt to your target system.

**Important**: The pattern you use depends on the system category. See `guide.md` Step 0 for classification.

---

## Category A: Distributed / Message-Passing Systems (Standard Pattern)

### Common Pattern

Every trace module needs:
1. **Global writer** — initialized once, thread-safe (mutex-protected)
2. **Server mapping** — implementation node IDs → TLA+ names (s1, s2, s3)
3. **Emit function** — writes one NDJSON line per call, **must include `"tag": "trace"`** in the outer envelope
4. **NDJSON output** — one JSON object per line, flushed immediately

Every emitted line must follow this envelope:

```json
{"tag": "trace", "ts": "<real_timestamp>", "event": {"name": "ActionName", "nid": "s1", "state": {...}, "msg": {...}}}
```

`tag` is mandatory — Trace.tla filters on it. Lines without `"tag": "trace"` are silently ignored.

### Examples by Language

| Language | Case Study | Trace Module | Key Files |
|----------|-----------|--------------|-----------|
| Rust | aptosbft | `case-studies/aptosbft/harness/src/tla_trace.rs` | trace module + test scenario + apply.sh + run.sh |
| Go | cometbft | `case-studies/cometbft/artifact/cometbft/` (instrumented in-place) | harness/run.sh + harness/preprocess_trace.py |
| C++ | braft | `case-studies/braft/artifact/braft/` (trace_logger.cpp) | instrumented in artifact source |

**Start by reading the example closest to your target language**, then adapt the pattern to your system.

---

## Category B: Concurrent / Lock-Free Systems (Timebox Pattern)

### Common Pattern

Every trace module needs:
1. **Per-thread writer** — thread-local file handle, zero contention
2. **rdtsc timestamps** — record `[start, end]` interval around each operation
3. **Emit function** — writes one NDJSON line to the thread-local file, **must include `"tag": "trace"`**
4. **State capture outside interval** — read state after `end` timestamp to keep interval tight

Every emitted line must follow this envelope:

```json
{"tag": "trace", "event": "ActionName", "tid": 0, "start": 1000, "end": 1050, "state": {...}, "args": {...}}
```

### Instrumentation Pattern

```
t_start = rdtsc()
result = do_operation(args)       // the actual operation
t_end = rdtsc()
state = capture_state()           // AFTER end — does not widen interval
emit(event_name, tid, t_start, t_end, state, args)
```

### Examples by Language

| Language | Case Study | Trace Module | Key Files |
|----------|-----------|--------------|-----------|
| C | DPDK rte_ring | `case-studies/dpdk-ring/harness/src/rte_ring_tla_trace.h` | header-only, `#ifdef` guarded |
| C | libomp | `case-studies/libomp/harness/src/omp_trace.h` | header with preprocessor script |
| Rust | arc-swap | `case-studies/arc-swap/harness/src/tla_trace.rs` | thread-local suppress flag pattern |

### Post-Processing Required

Category B traces require a merge step before validation:
1. Merge per-thread files into one JSON with per-thread arrays
2. Compress timestamps to dense integers
3. See `concurrent-timebox-guide.md` Step 4 for the preprocessor script

### Key Differences from Category A

| Aspect | Category A | Category B |
|--------|-----------|-----------|
| Writer | `Mutex<File>` or `pthread_mutex_t` + `FILE*` | `thread_local FILE*` (no mutex) |
| Timestamp | `clock_gettime` / `monotonic_time_ms` | `rdtsc` with `mfence` |
| Format | Single timestamp `ts` | Interval `start` + `end` |
| Trace.tla | `TraceLog[l]`, linear matching | `traces[tid][pc[tid]]`, `ViablePIDs` partial order |
| Post-processing | Optional (ID remapping) | Required (merge + compress) |

**See `concurrent-timebox-guide.md` for the full methodology, Trace.tla template, and search space control techniques.**
