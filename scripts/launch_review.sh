#!/usr/bin/env bash
#
# Run a Claude Code review agent on phase outputs.
# Used by launch_pipeline.sh between phases. Can also be used standalone.
#
# Usage:
#   bash scripts/launch_review.sh <phase> <name> [name ...]
#
# Phases:
#   analysis    — Review code analysis output (modeling-brief.md, analysis-report.md)
#   specgen     — Review spec generation output (base.tla, MC.tla, Trace.tla)
#   validation  — Review validation results (validation-report.md)
#
# Output:
#   case-studies/<name>/review-<phase>.md

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SPECULA_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
CASE_STUDIES_DIR="$SPECULA_ROOT/case-studies"
AGENT="claude-code"
TARGETS=()

# ──────────────────────────────────────────────────────────
# Parse arguments
# ──────────────────────────────────────────────────────────
PHASE="${1:-}"
shift 2>/dev/null || true

for arg in "$@"; do
  case "$arg" in
    --agent=*) AGENT="${arg#*=}" ;;
    --help|-h)
      sed -n '2,/^$/{ s/^# //; s/^#//; p }' "$0"
      exit 0
      ;;
    *) TARGETS+=("$arg") ;;
  esac
done

if [[ -z "$PHASE" || ${#TARGETS[@]} -eq 0 ]]; then
  echo "Usage: $0 <analysis|specgen|validation> name [name ...]"
  exit 1
fi

ADAPTER="$SCRIPT_DIR/adapters/${AGENT}.sh"
if [[ ! -f "$ADAPTER" ]]; then
  echo "ERROR: Unknown agent '${AGENT}' — adapter not found at ${ADAPTER}"
  exit 1
fi

# ──────────────────────────────────────────────────────────
# Generate review prompt per phase
# ──────────────────────────────────────────────────────────
generate_analysis_review_prompt() {
  local name="$1"
  local work_dir="${CASE_STUDIES_DIR}/${name}"
  cat <<PROMPT
# Code Analysis Review: ${name}

Review the code analysis outputs for quality and completeness.

## Files to Review

- Modeling Brief: ${work_dir}/modeling-brief.md
- Analysis Report: ${work_dir}/analysis-report.md

## Review Checklist

Score each item 1-5 (1=missing, 3=adequate, 5=excellent):

1. **Coverage Statistics**: Are they reported? How many issues were deeply read (target: 30+)?
2. **Bug Families**: Are they well-defined with mechanisms, not just lists? (target: 4-7 families)
3. **Evidence Quality**: Does each bug cite file:line, issue numbers, and commit references?
4. **Model-Checkable Findings**: Are findings classified? How many are model-checkable?
5. **Modeling Brief Completeness**: Variables, actions, invariants, extensions all specified?
6. **False Positive Control**: Were excluded issues documented with reasons?
7. **Source Code Annotations**: Are file:line references present throughout?

## Output

Write your review to: ${work_dir}/review-analysis.md

Format:
\`\`\`markdown
# Code Analysis Review: ${name}

## Scores
| Criterion | Score | Notes |
|-----------|-------|-------|
| Coverage Statistics | X/5 | ... |
| Bug Families | X/5 | ... |
| Evidence Quality | X/5 | ... |
| Model-Checkable Findings | X/5 | ... |
| Modeling Brief Completeness | X/5 | ... |
| False Positive Control | X/5 | ... |
| Source Code Annotations | X/5 | ... |

## Overall: X/35

## Issues Found
- ...

## Verdict: PASS / NEEDS_IMPROVEMENT
\`\`\`
PROMPT
}

generate_specgen_review_prompt() {
  local name="$1"
  local work_dir="${CASE_STUDIES_DIR}/${name}"
  local spec_dir="${work_dir}/spec"
  cat <<PROMPT
# Spec Generation Review: ${name}

Review the generated TLA+ specs for correctness and completeness.

## Files to Review

- Base Spec: ${spec_dir}/base.tla
- Base Config: ${spec_dir}/base.cfg
- MC Spec: ${spec_dir}/MC.tla
- MC Config: ${spec_dir}/MC.cfg
- Trace Spec: ${spec_dir}/Trace.tla
- Trace Config: ${spec_dir}/Trace.cfg
- Instrumentation: ${spec_dir}/instrumentation-spec.md
- Modeling Brief (reference): ${work_dir}/modeling-brief.md

## Review Checklist

Score each item 1-5:

1. **Bug Family Coverage**: Does each Bug Family in the brief have corresponding spec extensions?
2. **Action Design**: Are actions named after impl functions? Are code paths split where they diverge?
3. **Source Annotations**: Does every logic block cite file:line?
4. **Invariant Coverage**: Are standard + extension invariants present for each Bug Family?
5. **MC Spec Structure**: Are only fault-injection actions bounded? Symmetry/view/constraints present?
6. **Trace Spec Design**: Are silent actions tightly constrained? Post-state validation present?
7. **Instrumentation Mapping**: Is there a 1:1 mapping between spec actions and code locations?
8. **Logical Correctness**: Check for tautologies, impossible guards, typos in temporal properties.

## Output

Write your review to: ${spec_dir}/review-specgen.md

Format:
\`\`\`markdown
# Spec Generation Review: ${name}

## Scores
| Criterion | Score | Notes |
|-----------|-------|-------|
| Bug Family Coverage | X/5 | ... |
| Action Design | X/5 | ... |
| Source Annotations | X/5 | ... |
| Invariant Coverage | X/5 | ... |
| MC Spec Structure | X/5 | ... |
| Trace Spec Design | X/5 | ... |
| Instrumentation Mapping | X/5 | ... |
| Logical Correctness | X/5 | ... |

## Overall: X/40

## Issues Found
- ...

## Verdict: PASS / NEEDS_IMPROVEMENT
\`\`\`
PROMPT
}

generate_validation_review_prompt() {
  local name="$1"
  local work_dir="${CASE_STUDIES_DIR}/${name}"
  local spec_dir="${work_dir}/spec"
  cat <<PROMPT
# Validation Review: ${name}

Review the spec validation results and summarize readiness for trace validation.

## Files to Review

- Validation Report: ${spec_dir}/validation-report.md
- Quick MC Log (if exists): ${spec_dir}/quick-mc.log

## Review Checklist

1. **Syntax**: Did all specs pass SANY?
2. **MC Results**: Any violations found? Expected or unexpected?
3. **Readiness**: Is the spec ready for trace validation? What needs instrumentation first?

## Output

Write your review to: ${spec_dir}/review-validation.md

Format:
\`\`\`markdown
# Validation Review: ${name}

## Status
- Syntax: PASS/FAIL
- MC: PASS/FAIL/TIMEOUT/SKIPPED
- Ready for trace validation: YES/NO

## Next Steps
- ...

## Verdict: PASS / NEEDS_IMPROVEMENT
\`\`\`
PROMPT
}

# ──────────────────────────────────────────────────────────
# Launch review agent
# ──────────────────────────────────────────────────────────
launch_review() {
  local name="$1" phase="$2"
  local work_dir="${CASE_STUDIES_DIR}/${name}"
  local spec_dir="${work_dir}/spec"

  # specgen/validation logs go under spec/ to match pipeline summary expectations
  local log_dir="${work_dir}"
  case "$phase" in
    specgen|validation) log_dir="${spec_dir}" ;;
  esac
  local log_file="${log_dir}/review-${phase}.log"

  local prompt
  case "$phase" in
    analysis)  prompt="$(generate_analysis_review_prompt "$name")" ;;
    specgen)   prompt="$(generate_specgen_review_prompt "$name")" ;;
    validation) prompt="$(generate_validation_review_prompt "$name")" ;;
    *) echo "Unknown phase: $phase"; exit 1 ;;
  esac

  echo "[$(date '+%H:%M:%S')] Reviewing ${name} (${phase})..."

  mkdir -p "$log_dir"

  local pid
  pid=$("$ADAPTER" --prompt="$prompt" --max-turns=30 --log="$log_file" --background)
  echo "$pid" > "${log_dir}/review-${phase}.pid"
  echo "  PID=$pid  Log: $log_file"
}

# ──────────────────────────────────────────────────────────
# Main
# ──────────────────────────────────────────────────────────
main() {
  echo "========================================"
  echo " Specula — Review Agent (${PHASE})"
  echo "========================================"

  local pids=()

  for name in "${TARGETS[@]}"; do
    name="$(echo "$name" | xargs)"
    launch_review "$name" "$PHASE"
    local pid_dir="${CASE_STUDIES_DIR}/${name}"
    case "$PHASE" in
      specgen|validation) pid_dir="${pid_dir}/spec" ;;
    esac
    pids+=("$(cat "${pid_dir}/review-${PHASE}.pid")")
  done

  echo ""
  echo "Waiting for review agents to complete..."
  for pid in "${pids[@]}"; do
    wait "$pid" 2>/dev/null || true
  done

  echo ""
  echo "========================================"
  echo " Review Results"
  echo "========================================"
  for name in "${TARGETS[@]}"; do
    name="$(echo "$name" | xargs)"
    local review_file
    case "$PHASE" in
      analysis)   review_file="${CASE_STUDIES_DIR}/${name}/review-analysis.md" ;;
      specgen)    review_file="${CASE_STUDIES_DIR}/${name}/spec/review-specgen.md" ;;
      validation) review_file="${CASE_STUDIES_DIR}/${name}/spec/review-validation.md" ;;
    esac

    if [[ -f "$review_file" ]]; then
      local verdict
      verdict=$(grep -i "verdict:" "$review_file" | tail -1)
      verdict="${verdict:-UNKNOWN}"
      echo "  ${name}: ${verdict}"
    else
      echo "  ${name}: (no review file generated — check log)"
    fi
  done
}

main
