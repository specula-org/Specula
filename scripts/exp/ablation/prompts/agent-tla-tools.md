# Task: Analyze System and Write TLA+ Specification

You are an agent tasked with analyzing a system implementation and writing
a TLA+ formal specification for it.

## Target System

- **Name**: ${TARGET_NAME}
- **Language**: ${TARGET_LANG}
- **Algorithm**: ${TARGET_REFERENCE}
- **Source Code**: ${REPO_DIR}

## What to Do

1. **Analyze the source code**: Read the implementation to understand the system's
   architecture, state variables, and state transitions. Focus on the core protocol
   logic, concurrency mechanisms, and correctness-critical code paths.

2. **Write a TLA+ specification**: Model the system's core behavior as a TLA+ spec.
   Include state variables, initial state, and next-state actions for each
   significant operation.

3. **Define invariants**: Write safety and liveness properties that the system
   should satisfy.

4. **Write model checking configuration**: Create configuration files with
   appropriate constants for bounded model checking.

5. **Validate with traces** (if feasible): If you can instrument the code to
   produce execution traces, use trace validation to check spec conformance.

6. **Run model checking**: Execute TLC to verify the specification. Analyze any
   violations found.

## Output

Write all files to: `${SPEC_DIR}/`

- `base.tla` — Main specification
- `base.cfg` — Base configuration
- `MC.tla` — Model checking wrapper (bounded constants)
- `MC.cfg` — Model checking configuration

## Tools and Skills Available

You have access to standard file/shell tools plus the **TLA+ AI Tools** plugin:

### TLA+ MCP Tools

- **validate_spec_syntax** — Check TLA+ syntax via SANY
- **run_trace_validation** — Validate a trace against a spec
- **run_trace_validation_parallel** — Validate multiple traces
- **run_trace_debugging** — Debug trace validation failures
- **get_tlc_summary** — Get summary of a TLC run
- **get_tlc_state** — Inspect specific states in a TLC counterexample
- **compare_tlc_states** — Compare two TLC states

### TLA+ Community Skills (read these for guidance)

- Getting started: `${TLAPLUS_AI_TOOLS_DIR}/skills/tla-getting-started/SKILL.md`
- Model checking: `${TLAPLUS_AI_TOOLS_DIR}/skills/tla-model-checking/SKILL.md`
- Spec review: `${TLAPLUS_AI_TOOLS_DIR}/skills/tla-spec-review/SKILL.md`
- Debug violations: `${TLAPLUS_AI_TOOLS_DIR}/skills/tla-debug-violations/SKILL.md`

### TLC via bash

- `java -cp ${TLA2TOOLS_JAR}:${COMMUNITY_JAR} tlc2.TLC <spec.tla> -config <cfg> -workers auto -deadlock`

## Bug Report

If model checking reveals invariant violations, write a brief report:
`${SPEC_DIR}/bug-report.md`
