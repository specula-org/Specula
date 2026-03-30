# Specula: No Code Analysis (Ablation)

You are performing formal verification of a system implementation using TLA+.

**NOTE**: Skip code analysis entirely. Use only the generic system description below.

## Target System

- **Name**: ${TARGET_NAME}
- **GitHub**: ${TARGET_GITHUB}
- **Language**: ${TARGET_LANG}
- **Reference Algorithm**: ${TARGET_REFERENCE}
- **Source Code**: ${REPO_DIR}

## Working Directory

Write all outputs to: ${WORKSPACE_DIR}

- Specs: `${SPEC_DIR}/`

## Phase 1: SKIPPED

Do NOT perform code analysis. Do NOT produce a modeling brief.
Instead, use this minimal system description to guide spec generation:

> This system implements ${TARGET_REFERENCE} in ${TARGET_LANG}.
> Repository: ${REPO_DIR}
> Read the source code as needed during spec generation.

## Phase 2: Spec Generation

Read the spec-generation guide and references:

- ${SKILL_DIR_SPECGEN}/guide.md
- ${SKILL_DIR_SPECGEN}/references/base-spec-methodology.md
- ${SKILL_DIR_SPECGEN}/references/mc-spec-pattern.md
- ${SKILL_DIR_SPECGEN}/references/trace-spec-pattern.md
- ${SKILL_DIR_SPECGEN}/references/instrumentation-spec-format.md

Generate:

1. `${SPEC_DIR}/base.tla` + `base.cfg` — Core spec
2. `${SPEC_DIR}/MC.tla` + `MC.cfg` — Model checking wrapper
3. `${SPEC_DIR}/Trace.tla` + `Trace.cfg` — Trace validation wrapper
4. `${SPEC_DIR}/instrumentation-spec.md` — Action-to-code mapping

Without a modeling brief, base your spec on your reading of the source code
and your understanding of the ${TARGET_REFERENCE} algorithm.

## Phase 2.5: Harness Generation

Read the harness-generation guide:

- ${SKILL_DIR_HARNESS}/guide.md

Instrument the source code to emit NDJSON trace events. Collect traces.

## Phase 3A: Trace Validation

Read the trace validation guide:

- ${SKILL_DIR_TRACE}/guide.md

Validate the spec against collected traces. Fix mismatches iteratively.

## Phase 3B: Model Checking

Read the model checking guide:

- ${SKILL_DIR_CHECKING}/guide.md

Run TLC with MC spec. Analyze invariant violations.

Output: `${SPEC_DIR}/bug-report.md`
