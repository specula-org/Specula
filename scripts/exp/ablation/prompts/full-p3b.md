# Phase 3B: Model Checking

You are running TLC model checking to find bugs in a system implementation
via its TLA+ specification.

## Target System

- **Name**: ${TARGET_NAME}

## Input from Previous Phases

- Spec files: ${SPEC_DIR}/ (base.tla, MC.tla, MC.cfg, MC_hunt_*.cfg)
- Source code: ${REPO_DIR}

## Instructions

Follow the **tla-checking-workflow** skill methodology. Read the skill guide at:
  ${SKILL_DIR_CHECKING}/guide.md

## Tasks

1. **Run base model checking** — Run TLC with MC.cfg first. Check all invariants.
2. **Run hunting configs** — Run each MC_hunt_*.cfg to search for bug-family-specific
   violations with targeted fault injection.
3. **Analyze violations** — For each invariant violation found:
   - Use `get_tlc_summary` and `get_tlc_state` to understand the counterexample
   - Determine if it is: (a) a real implementation bug, (b) a spec bug, or (c) known issue
   - For spec bugs: fix the spec, re-run validation and MC
4. **Write bug report** — Document all findings.

## Output

Write the bug report to: ${SPEC_DIR}/bug-report.md

Include for each finding:
- Bug ID, severity, and category
- Root cause analysis
- Counterexample summary (states, steps)
- Affected code locations
- Whether confirmed, suspected, or false positive
