# Trace Harness Generation (Phase 2.5)

Instrument the real system's source code to emit NDJSON traces, write test scenarios that exercise the protocol, and collect the first batch of traces for Phase 3 (Spec Validation).

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
2. **Emit function** — write one NDJSON line per call with: event name, node ID, state snapshot, message fields (if applicable), real timestamp
3. **Shutdown** — flush and close

**Requirements**:
- Timestamps must be real (epoch nanos or monotonic clock), never synthetic
- Output format must be NDJSON (one JSON object per line)
- Event names must match `Trace.tla` exactly (1:1 correspondence with spec actions)
- State fields must match the mapping in `instrumentation-spec.md`
- Thread-safe if the system is concurrent

**Read `references/trace-module-patterns.md`** for language-specific templates.

---

## Step 3: Instrument Source Code

Insert trace emit calls into the system's source code at the locations specified in `instrumentation-spec.md`.

**Two approaches** (choose based on system):

1. **Copy-and-patch**: Copy harness source files into the artifact, add `mod`/`import` declarations. Use `apply.sh` to automate. Best for compiled languages with module systems (Rust, Go).
2. **Direct patch**: Modify artifact source files in-place. Use `apply.sh` with `git apply` or `sed`. Best for systems where adding modules is harder.

**Rules**:
- Every instrumentation point inserts into **real system code** — the emit call runs inside the actual code path
- Do NOT write a standalone simulator that reimplements protocol logic
- Do NOT hand-write trace data
- Capture state at the trigger point specified in the instrumentation spec (before/after matters)

---

## Step 4: Write Test Scenarios

Write test code that exercises the protocol code paths to generate trace events.

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

Must be executable from the case study root: `cd case-studies/<name> && bash harness/run.sh`

---

## Step 6: Run and Verify

1. Execute `harness/run.sh`
2. Verify traces were generated in `traces/`
3. Spot-check trace content:
   - Each line is valid JSON
   - Event names match spec actions
   - Timestamps are real (not sequential integers)
   - State fields are present and reasonable
4. Run a quick trace validation to catch obvious format issues:
   ```
   run_trace_validation(spec_file="Trace.tla", config_file="Trace.cfg", trace_file="../traces/<name>.ndjson", work_dir="spec/")
   ```
5. If validation fails, fix instrumentation and re-run. Minor fixes are expected at this stage.

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

- **Rust (aptosbft)**: `case-studies/aptosbft/harness/` — copy-and-patch approach, Rust trace module + test scenario
- **Go (cometbft)**: `case-studies/cometbft/harness/` — Go test scenarios with preprocessing

## Related Skills

- **spec-generation** — Previous phase: produces `instrumentation-spec.md` that drives this workflow
- **validation-workflow** — Next phase: uses the traces to validate the spec
