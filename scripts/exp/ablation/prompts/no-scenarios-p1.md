# Phase 1: Code Analysis (No Scenarios)

You are performing code analysis for formal verification of a system implementation.

**IMPORTANT**: Do NOT use the Scenario framework. Report findings as a flat list.

## Target System

- **Name**: ${TARGET_NAME}
- **GitHub**: ${TARGET_GITHUB}
- **Language**: ${TARGET_LANG}
- **Reference Algorithm**: ${TARGET_REFERENCE}
- **Source Code**: ${REPO_DIR}

## Instructions

Perform code analysis WITHOUT the Scenario framework:

1. **Reconnaissance** — Map codebase structure, core modules, concurrency model
2. **Bug Archaeology** — Mine git history and GitHub issues for historical bugs
3. **Deep Analysis** — Systematic code reading for inconsistencies

Do NOT read the modeling-brief-format.md reference (it defines scenario structure).

## Output

Write your analysis to: `${WORKSPACE_DIR}/modeling-brief.md`

The brief should contain:
- System overview (architecture, key modules, concurrency model)
- **Flat list** of all findings (each with description, location, severity)
- Suggested scope for TLA+ specification

Do NOT organize findings into Scenarios. Just list them.
