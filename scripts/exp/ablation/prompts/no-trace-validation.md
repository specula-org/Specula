# Specula: No Trace Validation (Ablation)

You are performing formal verification of a system implementation using TLA+.

**NOTE**: Skip harness generation and trace validation. After spec generation,
go directly to model checking.

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

## Phase 1: Code Analysis

Follow the code-analysis methodology. Read the guide and references:

- ${SKILL_DIR_ANALYSIS}/guide.md
- ${SKILL_DIR_ANALYSIS}/references/bug-archaeology.md
- ${SKILL_DIR_ANALYSIS}/references/deep-analysis.md
- ${SKILL_DIR_ANALYSIS}/references/modeling-brief-format.md

Example: ${SKILL_DIR_ANALYSIS}/examples/hashicorp-raft-modeling-brief.md

Execute all 4 sub-phases. Output: `${WORKSPACE_DIR}/modeling-brief.md`

## Phase 2: Spec Generation

Read the spec-generation guide and references:

- ${SKILL_DIR_SPECGEN}/guide.md
- ${SKILL_DIR_SPECGEN}/references/base-spec-methodology.md
- ${SKILL_DIR_SPECGEN}/references/mc-spec-pattern.md

Generate:

1. `${SPEC_DIR}/base.tla` + `base.cfg` — Core spec with bug-family driven extensions
2. `${SPEC_DIR}/MC.tla` + `MC.cfg` — Model checking wrapper with counter-bounded fault injection

Do NOT generate Trace.tla or instrumentation-spec.md (not needed without trace validation).

## Phase 2.5: SKIPPED

Do NOT instrument code. Do NOT collect traces.

## Phase 3A: SKIPPED

Do NOT perform trace validation.

## Phase 3B: Model Checking

Read the model checking guide:

- ${SKILL_DIR_CHECKING}/guide.md

Run TLC with MC spec. Analyze invariant violations. Determine if each violation is:
- A real implementation bug
- A spec bug
- A known issue

Note: without trace validation, the spec may not faithfully model the implementation.
Use your best judgment when interpreting violations.

Output: `${SPEC_DIR}/bug-report.md`
