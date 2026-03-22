#!/usr/bin/env bash
#
# Batch launcher: spawn one Claude Code agent per target system for bug confirmation.
# Each agent consolidates MC bugs + code review findings, then attempts to reproduce
# each bug following the bug-confirmation skill methodology.
#
# Usage:
#   bash scripts/launch/launch_bug_confirmation.sh [options] "name" [...]
#
# Example:
#   bash scripts/launch/launch_bug_confirmation.sh hashicorp-raft nuraft
#
# Options:
#   --dry-run           Print commands without executing
#   --check             Only verify prerequisites exist
#   --max-parallel=N    Max concurrent agents (default: 1)
#   --max-turns=N       Max agent turns (default: 0 = unlimited)
#   --agent=NAME        Agent adapter to use (default: claude-code)
#
# Prerequisites:
#   - Bug report at case-studies/<name>/spec/bug-report.md (from Phase 3)
#   - Modeling brief at case-studies/<name>/modeling-brief.md (from Phase 1)
#   - Source repo at case-studies/<name>/artifact/<repo>/

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SPECULA_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
CASE_STUDIES_DIR="$SPECULA_ROOT/case-studies"
MAX_PARALLEL=1
MAX_TURNS=0
DRY_RUN=false
CHECK_ONLY=false
AGENT="claude-code"
TARGETS=()

# ──────────────────────────────────────────────────────────
# Parse arguments
# ──────────────────────────────────────────────────────────
for arg in "$@"; do
  case "$arg" in
    --dry-run) DRY_RUN=true ;;
    --check) CHECK_ONLY=true ;;
    --max-parallel=*) MAX_PARALLEL="${arg#*=}" ;;
    --max-turns=*) MAX_TURNS="${arg#*=}" ;;
    --agent=*) AGENT="${arg#*=}" ;;
    --help|-h)
      sed -n '2,/^$/{ s/^# //; s/^#//; p }' "$0"
      exit 0
      ;;
    -*) echo "Unknown option: $arg"; exit 1 ;;
    *) TARGETS+=("$arg") ;;
  esac
done

if [[ ${#TARGETS[@]} -eq 0 ]]; then
  echo "Usage: $0 [options] name [name ...]"
  echo "Run $0 --help for details."
  exit 1
fi

ADAPTER="$SCRIPT_DIR/adapters/${AGENT}.sh"
if [[ ! -f "$ADAPTER" ]]; then
  echo "ERROR: Unknown agent '${AGENT}' — adapter not found at ${ADAPTER}"
  exit 1
fi

# ──────────────────────────────────────────────────────────
# Find artifact repo directory
# ──────────────────────────────────────────────────────────
find_repo_dir() {
  local name="$1"
  local artifact_dir="${CASE_STUDIES_DIR}/${name}/artifact"
  [[ ! -d "$artifact_dir" ]] && return
  for d in "$artifact_dir"/*/; do
    if [[ -d "${d}.git" || -f "${d}.git" ]]; then
      echo "$d"
      return
    fi
  done
}

# ──────────────────────────────────────────────────────────
# Check prerequisites
# ──────────────────────────────────────────────────────────
check_prereqs() {
  local ok=true
  for name in "${TARGETS[@]}"; do
    name="$(echo "$name" | xargs)"
    local work_dir="${CASE_STUDIES_DIR}/${name}"
    local repo_dir
    repo_dir="$(find_repo_dir "$name")"

    printf "  %-20s" "$name"

    if [[ -f "${work_dir}/spec/bug-report.md" ]]; then
      printf "bug-report OK"
    else
      printf "bug-report MISSING"
      ok=false
    fi

    if [[ -f "${work_dir}/modeling-brief.md" ]]; then
      printf "  brief OK"
    else
      printf "  brief MISSING"
      ok=false
    fi

    if [[ -n "$repo_dir" ]]; then
      printf "  repo OK"
    else
      printf "  repo MISSING"
      ok=false
    fi

    echo ""
  done
  $ok
}

# ──────────────────────────────────────────────────────────
# Generate agent prompt
# ──────────────────────────────────────────────────────────
generate_prompt() {
  local name="$1" repo_dir="$2"
  local work_dir="${CASE_STUDIES_DIR}/${name}"
  local spec_dir="${work_dir}/spec"

  cat <<PROMPT_EOF
# Bug Confirmation Task: ${name}

You are confirming and reproducing bugs found in **${name}** by both model checking and code review.

## Inputs

- **Bug report (MC findings)**: ${spec_dir}/bug-report.md
- **Modeling brief (code review findings)**: ${work_dir}/modeling-brief.md
- **Source code**: ${repo_dir}
- **Spec directory**: ${spec_dir}

## Methodology

Read and follow the **bug-confirmation** skill:
  ${SPECULA_ROOT}/.claude/skills/bug-confirmation/guide.md

## Task

### Step 1: Consolidate all findings

Read both \`bug-report.md\` (MC-confirmed bugs) and \`modeling-brief.md\` (code review findings).
Create a unified list of all bugs/findings, noting for each:
- Source: MC (with counterexample) or code review
- Severity assessment
- Affected code location

Filter out defensive coding suggestions, style issues, and theoretical-only concerns.
Keep only findings that represent real logic bugs with concrete impact.

### Step 2: Confirm each bug via code audit

For each finding, follow the bug-confirmation skill Phase 1:
1. Locate and read the relevant code in the source repo
2. Trace the call chain — is the buggy path reachable?
3. Check for existing safeguards that prevent the bug
4. Construct a concrete trigger scenario

Classify each finding as:
- **CONFIRMED**: Code audit confirms the bug is real and reachable
- **FALSE POSITIVE**: Safeguards exist that prevent the bug in practice
- **NEEDS REPRODUCTION**: Bug is plausible but needs a test to verify

### Step 3: Attempt reproduction (for CONFIRMED / NEEDS REPRODUCTION bugs)

For each confirmed bug, follow the bug-confirmation skill Phase 2:
- Write a minimal reproduction test/program
- Use the system's public interfaces — no illegal state injection
- For concurrency bugs: real multi-thread scenarios, small delays to widen race windows are OK
- Success criterion: observable anomalous behavior (crash, deadlock, data inconsistency)

### Step 4: Write final report

Write the final consolidated report to: ${spec_dir}/confirmed-bugs.md

Format:
\`\`\`markdown
# Confirmed Bug Report — ${name}

## Summary
- Total findings reviewed: N
- Confirmed: N (M reproduced, K code-audit only)
- False positives: N
- Inconclusive: N

## Bug 1: <title>
- **Source**: MC / Code Review
- **Status**: REPRODUCED / CONFIRMED (code audit) / FALSE POSITIVE
- **Severity**: Critical / High / Medium
- **Location**: file:line
- **Description**: ...
- **Trigger scenario**: ...
- **Reproduction**: (if reproduced, describe the test and result)
- **Recommendation**: ...
\`\`\`

## Critical Rules

1. Follow the bug-confirmation skill strictly — especially the prohibited approaches.
2. MC-confirmed bugs with counterexamples are high-confidence; focus reproduction effort there first.
3. Do NOT lower reproduction standards to claim success. If you cannot reproduce, say so honestly.
4. For each false positive, explain clearly what safeguard prevents the bug.
PROMPT_EOF

  # Inject per-target extra prompt if present
  local extra="${work_dir}/.prompt-extra.md"
  if [[ -f "$extra" ]]; then
    echo ""
    echo "## Target-Specific Instructions"
    echo ""
    cat "$extra"
  fi
}

# ──────────────────────────────────────────────────────────
# Launch a single Claude Code agent
# ──────────────────────────────────────────────────────────
launch_agent() {
  local name="$1" prompt="$2"
  local work_dir="${CASE_STUDIES_DIR}/${name}"
  local log_file="${work_dir}/bug-confirmation.log"
  local prompt_file="${work_dir}/.bug-confirmation-prompt.md"

  echo "$prompt" > "$prompt_file"

  echo "[$(date '+%H:%M:%S')] Launching agent: ${name}"

  if $DRY_RUN; then
    echo "  [DRY RUN] $ADAPTER --prompt=<prompt> --max-turns=${MAX_TURNS} --log=${log_file} --background"
    echo "  Prompt saved: ${prompt_file}"
    return 0
  fi

  "$ADAPTER" --prompt-file="$prompt_file" --max-turns="$MAX_TURNS" --log="$log_file" --background &
  local pid=$!
  echo "$pid" > "${work_dir}/bug-confirmation.pid"
  echo "  PID=$pid  Log: $log_file"
}

# ──────────────────────────────────────────────────────────
# Main
# ──────────────────────────────────────────────────────────
main() {
  echo "========================================"
  echo " Specula — Bug Confirmation Batch Runner"
  echo "========================================"
  echo "Targets:      ${#TARGETS[@]}"
  echo "Max parallel: $MAX_PARALLEL"
  echo "Max turns:    $MAX_TURNS"
  echo ""

  echo "Checking prerequisites..."
  if ! check_prereqs; then
    echo ""
    echo "ERROR: Missing prerequisites. Run full pipeline first."
    exit 1
  fi
  echo ""

  if $CHECK_ONLY; then
    echo "All prerequisites OK."
    exit 0
  fi

  local running_pids=()

  for name in "${TARGETS[@]}"; do
    name="$(echo "$name" | xargs)"

    local repo_dir
    repo_dir="$(find_repo_dir "$name")"

    local prompt
    prompt="$(generate_prompt "$name" "$repo_dir")"

    # Throttle
    while (( ${#running_pids[@]} >= MAX_PARALLEL )); do
      local new_pids=()
      for pid in "${running_pids[@]}"; do
        if kill -0 "$pid" 2>/dev/null; then
          new_pids+=("$pid")
        fi
      done
      running_pids=("${new_pids[@]}")
      if (( ${#running_pids[@]} >= MAX_PARALLEL )); then
        sleep 5
      fi
    done

    launch_agent "$name" "$prompt"
    if ! $DRY_RUN; then
      running_pids+=("$(cat "${CASE_STUDIES_DIR}/${name}/bug-confirmation.pid")")
    fi
    echo ""
  done

  if ! $DRY_RUN; then
    echo "[$(date '+%H:%M:%S')] All agents launched. Waiting..."
    echo "  Monitor: tail -f ${CASE_STUDIES_DIR}/*/bug-confirmation.log"
    echo ""
    wait
    echo "[$(date '+%H:%M:%S')] All agents completed."
  fi

  # Summary
  echo ""
  echo "========================================"
  echo " Results"
  echo "========================================"
  for name in "${TARGETS[@]}"; do
    name="$(echo "$name" | xargs)"
    local report="${CASE_STUDIES_DIR}/${name}/spec/confirmed-bugs.md"

    if [[ -f "$report" ]]; then
      local summary
      summary=$(grep -A5 "^## Summary" "$report" 2>/dev/null | tail -4)
      echo "  ${name}: ${summary:-report exists}"
    else
      echo "  ${name}: (no report)"
    fi
  done
}

main
