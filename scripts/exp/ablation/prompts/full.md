# Specula: Full Pipeline

You are performing formal verification of a system implementation using TLA+.

## Target System

- **Name**: ${TARGET_NAME}
- **GitHub**: ${TARGET_GITHUB}
- **Language**: ${TARGET_LANG}
- **Reference Algorithm**: ${TARGET_REFERENCE}
- **Source Code**: ${REPO_DIR}

## Working Directory

Write all outputs to: ${WORKSPACE_DIR}

- Specs: `${SPEC_DIR}/`
- Modeling brief: `${WORKSPACE_DIR}/modeling-brief.md`

## Phase 1: Code Analysis

Follow the code-analysis methodology. Read the guide and references:

- ${SKILL_DIR_ANALYSIS}/guide.md
- ${SKILL_DIR_ANALYSIS}/references/bug-archaeology.md
- ${SKILL_DIR_ANALYSIS}/references/deep-analysis.md
- ${SKILL_DIR_ANALYSIS}/references/modeling-brief-format.md

Example: ${SKILL_DIR_ANALYSIS}/examples/hashicorp-raft-modeling-brief.md

Execute all 4 sub-phases:

1. **Reconnaissance** — Map codebase structure, core modules, concurrency model
2. **Bug Archaeology** — Mine git history and GitHub issues for historical bugs
3. **Deep Analysis** — Systematic code reading for inconsistencies
4. **Modeling Brief** — Synthesize findings into bug families

Output: `${WORKSPACE_DIR}/modeling-brief.md`

## Phase 2: Spec Generation

Read the spec-generation guide and references:

- ${SKILL_DIR_SPECGEN}/guide.md
- ${SKILL_DIR_SPECGEN}/references/base-spec-methodology.md
- ${SKILL_DIR_SPECGEN}/references/mc-spec-pattern.md
- ${SKILL_DIR_SPECGEN}/references/trace-spec-pattern.md
- ${SKILL_DIR_SPECGEN}/references/instrumentation-spec-format.md

Generate:

1. `${SPEC_DIR}/base.tla` + `base.cfg` — Core spec with bug-family driven extensions
2. `${SPEC_DIR}/MC.tla` + `MC.cfg` — Model checking wrapper with counter-bounded fault injection
3. `${SPEC_DIR}/Trace.tla` + `Trace.cfg` — Trace validation wrapper
4. `${SPEC_DIR}/instrumentation-spec.md` — Action-to-code mapping

## Phase 2.5: Harness Generation

Read the harness-generation guide:

- ${SKILL_DIR_HARNESS}/guide.md

Instrument the source code to emit NDJSON trace events. Write:

1. `${WORKSPACE_DIR}/harness/` — Instrumented code + test scenarios
2. Run tests to collect traces at `${WORKSPACE_DIR}/traces/`

## Phase 3A: Trace Validation

Read the trace validation guide:

- ${SKILL_DIR_TRACE}/guide.md
- ${SKILL_DIR_TRACE}/references/validation.md
- ${SKILL_DIR_TRACE}/references/debugging.md
- ${SKILL_DIR_TRACE}/references/fix.md

Validate the spec against collected traces. Fix mismatches iteratively.

## Phase 3B: Model Checking

Read the model checking guide:

- ${SKILL_DIR_CHECKING}/guide.md

Run TLC with MC spec. Analyze invariant violations. Determine if each violation is:
- A real implementation bug
- A spec bug (fix and re-validate)
- A known issue

Output: `${SPEC_DIR}/bug-report.md`
