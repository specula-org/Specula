---
name: harness-generation
description: >
  Generate trace harnesses that instrument real system code to emit NDJSON traces
  for TLA+ validation. Use when the user says "trace harness", "instrument code",
  "emit traces", "NDJSON tracing", "test scenarios for TLA+", or needs to produce
  traces from instrumented tests for spec validation.
---

# Trace Harness Generation (Phase 2.5)

Instrument real system source code to emit NDJSON traces, write test scenarios, and collect traces for Phase 3 (Spec Validation).

## Workflow

1. **Read inputs** — `spec/instrumentation-spec.md` (action-to-code mapping), `spec/Trace.tla` + `Trace.cfg` (expected trace format), `artifact/<system>/` (source code)
2. **Write trace module** — language-specific emission library in `harness/src/` with init, emit, and shutdown functions. Read `references/trace-module-patterns.md` for templates
3. **Instrument source code** — insert emit calls at locations from `instrumentation-spec.md`. Use copy-and-patch (Rust, Go) or git patch (C/C++/Java) approach
4. **Write test scenarios** — reuse existing integration tests first; only write new ones for uncovered paths. Each scenario writes to `traces/<scenario>.ndjson`
5. **Write `harness/run.sh`** — single script: apply patches, build, run tests, collect traces
6. **Run and verify** — check traces are valid JSON, event names match spec, timestamps are real, then run `run_trace_validation()`
7. **Write `harness/INSTRUMENTATION.md`** — brief guide for Phase 3 agent to adjust instrumentation

## NDJSON Envelope

Every trace line **must** include `"tag": "trace"` — Trace.tla filters on this field; lines without it are silently ignored.

```json
{"tag": "trace", "ts": "1718234567890123456", "event": {"name": "RequestVote", "nid": "s1", "state": {"term": 3, "role": "candidate", "votedFor": "s1"}, "msg": {"term": 3, "lastLogIndex": 12, "lastLogTerm": 2}}}
```

## Minimal run.sh Structure

```bash
#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")/.."
bash harness/apply.sh           # apply instrumentation patches
cd artifact/<system> && make     # build instrumented system
cd ../.. && bash harness/test.sh # run test scenarios
echo "Traces collected:" && wc -l traces/*.ndjson
```

## Critical Rules

1. **Instrument real code, not a simulator** — traces must capture what the real system does
2. **Never hand-write traces** — every line must come from running instrumented code
3. **Match instrumentation spec exactly** — event names, field names, trigger points
4. **Real timestamps only** — use system clock (epoch nanos, monotonic, ISO 8601)
5. **One trace file per scenario** — don't mix scenarios into a single file
6. **`run.sh` must work end-to-end** — anyone should reproduce traces with one command

Read `guide.md` for detailed methodology, patch management strategies, state capture levels, and server ID mapping approaches.
