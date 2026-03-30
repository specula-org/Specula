# Phase 2.5: Harness Generation

You are instrumenting a system's source code to collect execution traces
for TLA+ trace validation.

## Target System

- **Name**: ${TARGET_NAME}
- **Language**: ${TARGET_LANG}
- **Source Code**: ${REPO_DIR}

## Input from Previous Phases

- Instrumentation spec: ${SPEC_DIR}/instrumentation-spec.md
- Trace spec: ${SPEC_DIR}/Trace.tla
- Base spec: ${SPEC_DIR}/base.tla

Read the instrumentation spec to understand which code locations to instrument
and what trace events to emit.

## Instructions

Follow the **harness-generation** skill methodology. Read the skill guide at:
  ${SKILL_DIR_HARNESS}/guide.md

## Tasks

1. **Instrument the source code** — Add NDJSON trace event emissions at the
   code locations specified in instrumentation-spec.md. Patch the real source
   code, do NOT write a standalone simulation.
2. **Write test scenarios** — Create tests that exercise the protocol code paths
   relevant to each bug family.
3. **Collect traces** — Run the instrumented tests and save NDJSON traces to:
   ${WORKSPACE_DIR}/traces/

## Output

- `${WORKSPACE_DIR}/harness/` — Instrumented code, patches, test scenarios
- `${WORKSPACE_DIR}/traces/*.ndjson` — Collected execution traces

Ensure traces contain enough events (aim for 20+ events per trace) to
meaningfully exercise the spec's state transitions.
