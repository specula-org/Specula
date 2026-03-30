# Specula: No Bug Families (Ablation)

You are performing formal verification of a system implementation using TLA+.

**NOTE**: During code analysis, do NOT use the bug family framework.
Report findings as a flat list instead of grouping into bug families.

## Target System

- **Name**: ${TARGET_NAME}
- **GitHub**: ${TARGET_GITHUB}
- **Language**: ${TARGET_LANG}
- **Reference Algorithm**: ${TARGET_REFERENCE}
- **Source Code**: ${REPO_DIR}

## Working Directory

Write all outputs to: ${WORKSPACE_DIR}

- Modeling brief: `${WORKSPACE_DIR}/modeling-brief.md`
- Specs: `${SPEC_DIR}/`

## Phase 1: Code Analysis (Modified — No Bug Families)

Perform code analysis WITHOUT the bug family framework:

1. **Reconnaissance** — Map codebase structure, core modules, concurrency model
2. **Bug Archaeology** — Mine git history and GitHub issues for historical bugs
3. **Deep Analysis** — Systematic code reading for inconsistencies

**IMPORTANT**: Do NOT organize findings into bug families. Instead, write a flat
list of all findings (potential bugs, deviations from reference algorithm,
concurrency issues, etc.) in your modeling brief.

The modeling brief should contain:
- System overview (architecture, key modules, concurrency model)
- Flat list of findings (each with description, location, severity)
- Suggested scope for TLA+ specification

Do NOT read the modeling-brief-format.md reference (it defines the bug family structure).

Output: `${WORKSPACE_DIR}/modeling-brief.md`

## Phase 2: Spec Generation

Read the spec-generation guide:

- ${SKILL_DIR_SPECGEN}/guide.md
- ${SKILL_DIR_SPECGEN}/references/base-spec-methodology.md
- ${SKILL_DIR_SPECGEN}/references/mc-spec-pattern.md
- ${SKILL_DIR_SPECGEN}/references/trace-spec-pattern.md
- ${SKILL_DIR_SPECGEN}/references/instrumentation-spec-format.md

Generate specs based on your flat findings list (not bug families).

1. `${SPEC_DIR}/base.tla` + `base.cfg`
2. `${SPEC_DIR}/MC.tla` + `MC.cfg`
3. `${SPEC_DIR}/Trace.tla` + `Trace.cfg`
4. `${SPEC_DIR}/instrumentation-spec.md`

## Phase 2.5: Harness Generation

Read: ${SKILL_DIR_HARNESS}/guide.md

Instrument source code, collect traces.

## Phase 3A: Trace Validation

Read: ${SKILL_DIR_TRACE}/guide.md

Validate spec against traces. Fix mismatches iteratively.

## Phase 3B: Model Checking

Read: ${SKILL_DIR_CHECKING}/guide.md

Run TLC. Analyze invariant violations.

Output: `${SPEC_DIR}/bug-report.md`
