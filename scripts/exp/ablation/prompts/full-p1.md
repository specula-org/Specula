# Phase 1: Code Analysis

You are performing code analysis for formal verification of a system implementation.

## Target System

- **Name**: ${TARGET_NAME}
- **GitHub**: ${TARGET_GITHUB}
- **Language**: ${TARGET_LANG}
- **Reference Algorithm**: ${TARGET_REFERENCE}
- **Source Code**: ${REPO_DIR}

## Instructions

Follow the **code-analysis** skill methodology. Read the skill guide at:
  ${SKILL_DIR_ANALYSIS}/guide.md

Then read the reference files as needed:
  ${SKILL_DIR_ANALYSIS}/references/bug-archaeology.md
  ${SKILL_DIR_ANALYSIS}/references/deep-analysis.md
  ${SKILL_DIR_ANALYSIS}/references/modeling-brief-format.md

Example: ${SKILL_DIR_ANALYSIS}/examples/hashicorp-raft-modeling-brief.md

## Phases

Execute all 4 sub-phases in order:

1. **Reconnaissance** — Map codebase structure, core modules, concurrency model
2. **Bug Archaeology** — Mine git history and GitHub issues/PRs for historical bugs
3. **Deep Analysis** — Systematic code reading for inconsistencies and deviations
4. **Modeling Brief** — Synthesize findings into bug families

## Output

Write your modeling brief to: `${WORKSPACE_DIR}/modeling-brief.md`

This file will be used by the next phase (spec generation) as the primary input.
Focus on identifying **bug families** — groups of potential bugs that share
a common mechanism and can be targeted by the same TLA+ invariants.
