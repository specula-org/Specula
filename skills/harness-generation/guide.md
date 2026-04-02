# Trace Harness Generation (Phase 2.5)

Instrument the real system's source code to emit NDJSON traces, write test scenarios that exercise the protocol, and collect the first batch of traces for Phase 3 (Spec Validation).

---

## Step 0: Determine System Category

Before starting instrumentation, determine which category the target system belongs to. The two categories have fundamentally different trace collection strategies due to the difference in operation timescales.

### Category A: Distributed / Message-Passing Systems

**Examples**: CometBFT, braft, Substrate GRANDPA, Autobahn BFT, hashicorp-raft, etcd-raft

**Characteristics**:
- Operations are ms-level (network I/O, disk I/O, RPC)
- Mutex overhead (μs) is negligible compared to operation time
- Probe effect from trace instrumentation does not alter system behavior
- Event ordering issues are rare and minor

**Trace strategy**: Use the **standard single-file approach** described in Steps 1-7 below.
- Single NDJSON file per scenario, all threads write via mutex
- Timestamps via monotonic clock (ms or μs precision is fine)
- State captured at emit time under existing locks
- Minor ordering issues handled case-by-case (preprocessor or weak validation)

### Category B: Concurrent / Lock-Free Data Structures

**Examples**: DPDK rte_ring, arc-swap, libomp barrier+tasking, libgomp barrier, crossbeam-epoch

**Characteristics**:
- Operations are ns-level (CAS, atomic ops, spin loops)
- Mutex overhead (μs) is 100-1000x the operation time — **severe probe effect**
- Mutex serializes thread scheduling, suppressing the exact race conditions we want to observe
- Event ordering issues are frequent due to tight timing windows

**Trace strategy**: Use the **timebox approach** described in `references/concurrent-timebox-guide.md`.
- Per-thread trace files (zero mutex contention)
- Timestamps via `rdtsc` (ns precision, ~25 CPU cycles overhead)
- Each event records an interval `[start, end]` around the operation
- TLC searches all valid interleavings of overlapping intervals (partial order)
- State still captured and validated (placed outside the interval to keep it tight)

**Read `references/concurrent-timebox-guide.md` for the full concurrent trace methodology before proceeding.**

### How to Decide

| Question | If yes → | If no → |
|----------|----------|---------|
| Does the system communicate via network/RPC? | Category A | Keep checking |
| Are core operations < 1μs (CAS, atomic, spin)? | Category B | Category A |
| Does adding a mutex to the hot path change observable behavior? | Category B | Category A |
| Is the system a lock-free or wait-free data structure? | Category B | Category A |

When in doubt, default to Category A. Only use the timebox approach when probe effect is a real concern.

---

## Input

| Item | Description |
|------|-------------|
| Instrumentation spec | `spec/instrumentation-spec.md` — action-to-code mapping from Phase 2 |
| Trace spec | `spec/Trace.tla` + `spec/Trace.cfg` — defines expected trace format |
| Source code | `artifact/<system>/` — the real system codebase |

## Output

| Item | Path | Description |
|------|------|-------------|
| Trace module | `harness/src/` | Trace emission library (language-specific) |
| Apply script | `harness/apply.sh` | Applies instrumentation patches to artifact |
| Test scenarios | `harness/src/` | Test code that exercises protocol paths |
| Run script | `harness/run.sh` | One-command: apply instrumentation, build, run tests, collect traces |
| Traces | `traces/*.ndjson` | NDJSON trace files from test runs |
| Instrumentation guide | `harness/INSTRUMENTATION.md` | Brief doc for Phase 3 agent to adjust instrumentation if needed |

---

## Step 1: Read Inputs

1. **Read `instrumentation-spec.md`** — understand every action-to-code mapping, trigger points, fields to capture
2. **Skim `Trace.tla`** — understand the expected event schema (event names, field names, state fields)
3. **Read the relevant source code** — the files referenced in the instrumentation spec

---

## Step 2: Write Trace Module

Write a language-specific trace emission library in `harness/src/`. This module provides:

1. **Initialization** — open trace file, set up server name mapping
2. **Emit function** — write one NDJSON line per call with: tag, event name, node ID, state snapshot, message fields (if applicable), real timestamp
3. **Shutdown** — flush and close

### NDJSON Envelope

Every trace line **must** include `"tag": "trace"`. Trace.tla filters on this field — lines without it are silently ignored, causing validation to see an empty trace.

```json
{"tag": "trace", "ts": "<real_timestamp>", "event": {"name": "<ActionName>", "nid": "<server_id>", "state": {...}, "msg": {...}}}
```

Optionally, emit a **config line** as the first line to declare cluster topology and tuning parameters. Use `"tag": "config"`:

```json
{"tag": "config", "ts": "...", "config": {"servers": ["s1", "s2", "s3"], "electionTimeout": "150ms", ...}}
```

Trace.tla can use this to override constants (e.g., `Server`, timeout values) instead of hardcoding them.

### Server ID Mapping

Implementation node IDs (hex addresses, ip:port, UUIDs) must be mapped to TLA+ names (`s1`, `s2`, `s3`). Choose the strategy that fits the system:

| Strategy | When to use | Example |
|----------|-------------|---------|
| **Static mapping at emit time** | Test setup knows all node IDs upfront | braft, aptosbft — build a map in test init, call `nid(implID)` at each emit |
| **Dynamic mapping at runtime** | Node IDs only known at startup | hashicorp-raft — register peers as they appear, assign `s1`, `s2`, ... in discovery order |
| **Post-processing script** | IDs are too complex to map in-code (long hex, block hashes) | cometbft — emit raw IDs, then run `preprocess_trace.py` to remap all IDs before validation |

If using post-processing, include the script in `harness/` and call it from `run.sh`.

### Requirements

- **`"tag": "trace"` is mandatory** on every event line
- Timestamps must be real (epoch nanos, monotonic clock, ISO 8601, etc.), never synthetic
- Output format must be NDJSON (one JSON object per line)
- Event names must match `Trace.tla` exactly (1:1 correspondence with spec actions)
- State fields must match the mapping in `instrumentation-spec.md`
- Thread-safe: **Category A** → mutex-protected global writer (standard pattern); **Category B** → per-thread files with rdtsc intervals (see `references/concurrent-timebox-guide.md`)

**Read `references/trace-module-patterns.md`** for language-specific templates.

---

## Step 3: Instrument Source Code

Insert trace emit calls into the system's source code at the locations specified in `instrumentation-spec.md`.

### Patch Management

Two approaches (choose based on system):

1. **Copy-and-patch**: Copy harness source files (trace module, test scenarios) into the artifact, then patch `mod`/`import` declarations to wire them in. Best for compiled languages with module systems (Rust, Go).
   - `apply.sh` steps: `cp harness/src/*.rs artifact/.../src/` → `sed` or `patch` to add `mod tla_trace;` to `lib.rs`
   - Include a `clean.sh` to revert: `git -C artifact checkout -- .`

2. **Git patch**: Generate a patch file from a working instrumented tree, then apply it reproducibly. Best for C/C++/Java or when modifying many source files.
   - Create patch: `cd artifact && git diff > ../harness/patches/instrumentation.patch`
   - `apply.sh` steps: `cd artifact && git checkout -- . && git apply ../harness/patches/instrumentation.patch`
   - Patch files live in `harness/patches/` and are version-controlled

### State Capture Levels

Not all instrumentation points can capture full state. The instrumentation spec may define different capture levels:

| Level | Fields | When to use |
|-------|--------|-------------|
| **Full** | All spec variables (term, role, votedFor, commitIndex, lastLogIndex, lastLogTerm, ...) | Action runs under the node's main lock and has access to all state |
| **Weak** | Only term + role (or similarly minimal) | Async threads (e.g., replicator bthreads, background goroutines) that cannot safely read full state |
| **Specialized** | A specific subset (e.g., term + role + commitIndex) | Actions that update a single field (e.g., AdvanceCommitIndex) where only that field plus core state is available |

When using a non-full capture level, **document it** in `harness/INSTRUMENTATION.md` with the reason (e.g., "Replicator runs in a separate bthread, only term and role are passed via closure"). This tells the Phase 3 agent which Trace.tla validator variant (`ValidatePostStateWeak`, `ValidatePostStateCommit`, etc.) to use.

### Trace Coverage

Instrument **as many spec actions as possible**. The more actions are traced, the stronger the consistency check between implementation and spec. Only skip tracing an action if observing it provides no value for bug finding (e.g., pure heartbeat probes with no state change, read-only queries). Actions that are not traced will require Silent Action wrappers in Trace.tla, which weaken validation — minimize them.

### Rules

- Every instrumentation point inserts into **real system code** — the emit call runs inside the actual code path
- Do NOT write a standalone simulator that reimplements protocol logic
- Do NOT hand-write trace data
- Capture state at the trigger point specified in the instrumentation spec (before/after matters)

---

## Step 4: Write Test Scenarios

Write test code that exercises the protocol code paths to generate trace events.

**Reuse existing tests first.** Most systems already have integration or end-to-end tests that exercise the protocol paths you need. Prefer adding trace emit calls to existing test infrastructure rather than writing new tests from scratch. Only write new scenarios when existing tests do not cover the target code paths (e.g., specific fault injection, bug-family edge cases).

**Requirements**:
- Tests must use the system's real test framework (Go `testing`, Rust `#[test]`, Java JUnit, etc.)
- Tests must run the actual protocol code (not mocked or simulated)
- Aim for 2-4 scenarios covering: normal operation, fault injection (crash, network partition), edge cases from bug families
- Each scenario writes to a separate trace file: `traces/<scenario>.ndjson`

---

## Step 5: Write run.sh

Write `harness/run.sh` — a single script that:

1. Applies instrumentation (`apply.sh`)
2. Builds the project
3. Runs test scenarios
4. Collects traces to `traces/`
5. Reports trace line counts

Must be executable from `.specula-output/`: `cd .specula-output && bash harness/run.sh`

---

## Step 6: Run and Verify

1. Execute `harness/run.sh`
2. Verify traces were generated in `traces/`
3. Spot-check trace content:
   - Each line is valid JSON
   - Event names match spec actions
   - Timestamps are real (not sequential integers)
   - State fields are present and reasonable
4. **Check event type coverage**:
   - List all instrumented event types (from Step 3)
   - For each type, verify it appears in at least one trace
   - If an event type is missing from all traces, either:
     - Add a test scenario that triggers it, or
     - Document why it cannot be triggered in tests (e.g., "requires hardware fault injection")
   - Uncovered event types mean the spec's handling of that action is untested by trace validation
5. **(Category B only) Check trace concurrency quality**:
   - At least one trace must have genuine cross-thread interval overlap
   - If all traces are sequential (no overlap), the timebox mechanism is not being tested
   - See `references/concurrent-timebox-guide.md` "Trace Quality Criteria" for details
6. **Check state validation coverage (L2)**:
   - Open `Trace.tla` and verify `ValidatePostState` is NOT a stub (`TRUE`)
   - For each action wrapper, verify it checks the key fields that the action modifies
   - Captured state fields in the trace must have corresponding checks in `ValidatePostState`
   - If a field is captured but not validated, either add the check or remove the capture (don't leave dead data)
7. Run a quick trace validation to catch obvious format issues:
   ```
   run_trace_validation(spec_file="Trace.tla", config_file="Trace.cfg", trace_file="../traces/<name>.ndjson", work_dir="spec/")
   ```
8. If validation fails, fix instrumentation and re-run. Minor fixes are expected at this stage.

---

## Step 7: Write Instrumentation Guide

Write `harness/INSTRUMENTATION.md` — a brief guide for the Phase 3 (validation) agent to adjust instrumentation when trace validation reveals issues.

Contents:
- Where each instrumentation point is (file:line after apply)
- How to add a new field to an event (which struct/function to modify)
- How to add a new event type (copy pattern from existing)
- How to move a capture point (before → after or vice versa)
- How to rebuild and re-run after changes

Keep it short and practical — the Phase 3 agent needs to make small adjustments, not understand the entire harness architecture.

---

## Critical Rules

1. **Instrument real code, not a simulator.** The trace must capture what the real system does. A standalone simulator that reimplements protocol logic defeats the purpose of trace validation.
2. **Never hand-write traces.** Every trace line must come from running instrumented code. Synthetic traces (sequential timestamps, perfectly symmetric patterns) are worthless for validation.
3. **Match the instrumentation spec exactly.** Event names, field names, trigger points — the spec generation agent designed these for a reason. Deviating causes trace validation failures.
4. **Real timestamps only.** Use the system's clock (epoch nanos, monotonic, etc.). Sequential integers (1000, 1001, 1002) indicate hand-written traces.
5. **One trace file per scenario.** Don't mix scenarios into a single file.
6. **run.sh must work end-to-end.** Anyone should be able to reproduce traces with a single command.

---

## Reference Files

- **`references/trace-module-patterns.md`** — Language-specific trace emission templates (Go, Rust, Java)

## Examples

- **Rust (aptosbft)**: copy-and-patch approach, Rust trace module + test scenario
- **Go (cometbft)**: Go test scenarios with preprocessing

See the [Specula case-studies repository](https://github.com/specula-org/specula-case-studies) for full harness examples.

## Related Skills

- **spec-generation** — Previous phase: produces `instrumentation-spec.md` that drives this workflow
- **validation-workflow** — Next phase: uses the traces to validate the spec

## Additional References

For additional examples beyond the built-in ones, see the [Specula case-studies repository](https://github.com/specula-org/specula-case-studies) which contains 60+ completed case studies across distributed systems, consensus protocols, and concurrent data structures.
