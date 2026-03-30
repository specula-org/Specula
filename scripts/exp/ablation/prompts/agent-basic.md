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

5. **Run model checking**: Execute TLC to verify the specification. Analyze any
   violations found.

## Output

Write all files to: `${SPEC_DIR}/`

- `base.tla` — Main specification
- `base.cfg` — Base configuration
- `MC.tla` — Model checking wrapper (bounded constants)
- `MC.cfg` — Model checking configuration

## Tools Available

You have access to standard file and shell tools:
- Read/write files
- Run bash commands (including TLC via java -cp)
- Search code with grep/glob

You do NOT have TLA+-specific analysis tools. Use TLC directly via bash:
- Syntax check: `java -cp ${TLA2TOOLS_JAR} tla2sany.SANY <spec.tla>`
- Model check: `java -cp ${TLA2TOOLS_JAR}:${COMMUNITY_JAR} tlc2.TLC <spec.tla> -config <cfg> -workers auto -deadlock`

## Bug Report

If model checking reveals invariant violations, write a brief report:
`${SPEC_DIR}/bug-report.md`
