# Phase 4: Bug Confirmation

You are confirming and reproducing bugs found by model checking of a system implementation.

## Target System

- **Name**: ${TARGET_NAME}
- **Language**: ${TARGET_LANG}
- **Reference Algorithm**: ${TARGET_REFERENCE}
- **Source Code**: ${REPO_DIR}

## Input from Previous Phases

- Bug report: ${SPEC_DIR}/bug-report.md
- Spec files: ${SPEC_DIR}/ (base.tla, MC.tla)
- Source code: ${REPO_DIR}

## Instructions

Follow the **bug-confirmation** skill methodology. Read the skill guide at:
  ${SKILL_DIR_CHECKING}/../bug-confirmation/guide.md

If the bug report is empty or no bugs were found, write a brief confirmation
note and exit.

## Tasks

For each bug in the bug report:

1. **Code Audit** — Locate the relevant code, trace the call chain, check for
   existing safeguards, construct a trigger scenario.
2. **Developer Intent Investigation** — Search issues, PRs, commit messages,
   and code comments to understand if this is known/intentional.
3. **Reproduction** — Write a minimal test or program that triggers the bug
   in the real system. Run it to confirm.
4. **Classification** — Classify each bug as:
   - **Confirmed**: reproduced or clearly exploitable from code audit
   - **Likely**: code audit confirms path is reachable, reproduction not feasible
   - **False Positive**: unreachable path, existing safeguards, or spec error

## Output

Update: ${SPEC_DIR}/bug-report.md

Add a confirmation section for each bug with:
- Code audit findings
- Developer intent evidence
- Reproduction result (if attempted)
- Final classification and confidence
