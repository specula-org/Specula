# Phase 2: TLA+ Spec Generation

You are generating TLA+ specifications based on a completed code analysis.

## Target System

- **Name**: ${TARGET_NAME}
- **Language**: ${TARGET_LANG}
- **Reference Algorithm**: ${TARGET_REFERENCE}
- **Source Code**: ${REPO_DIR}

## Input from Phase 1

Read the modeling brief produced by the previous phase:
  ${WORKSPACE_DIR}/modeling-brief.md

This brief contains bug families, system architecture, and modeling scope.

## Instructions

Follow the **spec-generation** skill methodology. Read the skill guide at:
  ${SKILL_DIR_SPECGEN}/guide.md

Then read the reference files:
  ${SKILL_DIR_SPECGEN}/references/base-spec-methodology.md
  ${SKILL_DIR_SPECGEN}/references/mc-spec-pattern.md
  ${SKILL_DIR_SPECGEN}/references/trace-spec-pattern.md
  ${SKILL_DIR_SPECGEN}/references/instrumentation-spec-format.md

## Output

Write all files to: ${SPEC_DIR}/

1. `base.tla` + `base.cfg` — Core spec with bug-family driven extensions
2. `MC.tla` + `MC.cfg` — Model checking wrapper with counter-bounded fault injection
3. `Trace.tla` + `Trace.cfg` — Trace validation wrapper
4. `instrumentation-spec.md` — Action-to-code mapping for harness generation

Also generate bug-family-specific hunting configs: `MC_hunt_*.cfg`
