# Phase 2: TLA+ Spec Generation (No Code Analysis)

You are generating TLA+ specifications for a system. No code analysis
or modeling brief has been performed — use the generic system description below.

## Target System

- **Name**: ${TARGET_NAME}
- **Language**: ${TARGET_LANG}
- **Reference Algorithm**: ${TARGET_REFERENCE}
- **Source Code**: ${REPO_DIR}

## System Description (generic, no prior analysis)

This system implements ${TARGET_REFERENCE} in ${TARGET_LANG}.
Read the source code directly to understand the system's behavior.
You do NOT have a modeling brief — decide what to model based on your
reading of the code and your understanding of the ${TARGET_REFERENCE} algorithm.

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

1. `base.tla` + `base.cfg` — Core spec
2. `MC.tla` + `MC.cfg` — Model checking wrapper
3. `Trace.tla` + `Trace.cfg` — Trace validation wrapper
4. `instrumentation-spec.md` — Action-to-code mapping
