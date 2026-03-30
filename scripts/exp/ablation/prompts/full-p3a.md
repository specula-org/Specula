# Phase 3A: Trace Validation

You are validating a TLA+ specification against execution traces collected
from the real system implementation.

## Target System

- **Name**: ${TARGET_NAME}

## Input from Previous Phases

- Spec files: ${SPEC_DIR}/ (base.tla, Trace.tla, Trace.cfg)
- Traces: ${WORKSPACE_DIR}/traces/*.ndjson
- Source code: ${REPO_DIR}

## Instructions

Follow the **tla-trace-workflow** skill methodology. Read the skill guide at:
  ${SKILL_DIR_TRACE}/guide.md

Then read the reference files:
  ${SKILL_DIR_TRACE}/references/validation.md
  ${SKILL_DIR_TRACE}/references/debugging.md
  ${SKILL_DIR_TRACE}/references/fix.md

## Tasks

1. **Validate each trace** — Run `run_trace_validation` on EVERY collected trace
   in ${WORKSPACE_DIR}/traces/. Do not skip any trace.
2. **Debug mismatches** — When validation fails, use `run_trace_debugging` to
   identify the root cause (spec bug, trace format issue, or missing action).
3. **Fix the spec** — Edit base.tla and/or Trace.tla to fix mismatches.
   Never weaken validation by removing checks — fix the underlying issue.
4. **Re-validate** — After each fix, re-run validation on ALL traces to ensure
   no regressions. Use `run_trace_validation_parallel` for efficiency.
5. **Iterate** — Repeat steps 2-4 until all traces pass validation.

## Completion Criteria

This phase is complete ONLY when ALL traces in ${WORKSPACE_DIR}/traces/
pass validation without errors. Do not proceed until this is achieved.

## Output

- Updated spec files (base.tla, Trace.tla) with fixes applied
- All traces validated successfully
