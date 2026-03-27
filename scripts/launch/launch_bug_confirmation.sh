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

### Step 3: MANDATORY — Reproduce every confirmed bug

**This step is NOT optional.** Every bug classified as CONFIRMED or NEEDS REPRODUCTION MUST have a reproduction test. A bug without reproduction is NOT confirmed — it is unverified.

For each confirmed bug:
1. Write a self-contained reproduction test to \`${work_dir}/repro/\`
2. The test MUST use the system's public interfaces — no illegal state injection
3. The test MUST actually be executed, and the output recorded
4. For concurrency bugs: real multi-thread/multi-process scenarios. Small delays (sleep, failpoints) to widen race windows are OK, but the logic must not be altered.
5. For distributed systems: use Docker or the system's test framework to set up a real cluster
6. Success criterion: observable anomalous behavior (crash, deadlock, data inconsistency, invariant violation)
7. If reproduction fails after genuine effort: explain what was tried, why it failed, and whether the bug is still believed to be real. Do NOT silently skip reproduction.

**Output requirement**: At least one executable file in \`${work_dir}/repro/\` for each confirmed bug. Name them \`test_bug1_*.py\`, \`test_bug2_*.py\`, etc.

### Step 4: Write final report

Write the final consolidated report to: ${spec_dir}/confirmed-bugs.md

Format:
\`\`\`markdown
# Confirmed Bug Report — ${name}

## Summary
- Total findings reviewed: N
- Reproduced: N
- Confirmed (code audit, reproduction failed): N
- False positives: N
- Inconclusive: N

## Bug 1: <title>
- **Source**: MC / Code Review
- **Status**: REPRODUCED / REPRODUCTION FAILED / FALSE POSITIVE
- **Severity**: Critical / High / Medium
- **Location**: file:line
- **Description**: ...
- **Trigger scenario**: ...
- **Reproduction test**: repro/test_bug1_xxx.py — describe what it does
- **Reproduction result**: PASS (bug triggered) / FAIL (bug not triggered, explain why)
- **Recommendation**: ...
\`\`\`

## Critical Rules

1. Follow the bug-confirmation skill strictly — especially the prohibited approaches.
2. **Every confirmed bug MUST have a reproduction test in repro/.** No exceptions. "Code audit only" is NOT an acceptable final status for new bugs.
3. MC-confirmed bugs with counterexamples are high-confidence; focus reproduction effort there first.
4. Do NOT lower reproduction standards to claim success. If you cannot reproduce, say so honestly — but you MUST try.
5. For each false positive, explain clearly what safeguard prevents the bug.
6. Actually RUN the reproduction tests and record the output. Do not just write tests without executing them.
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

      # Hard check: if confirmed bugs > 0, repro/ must have test files
      local confirmed
      confirmed=$(grep -oP 'Reproduced:\s*\K\d+' "$report" 2>/dev/null || echo "0")
      local repro_dir="${CASE_STUDIES_DIR}/${name}/repro"
      local repro_count
      repro_count=$(find "$repro_dir" -name "test_bug*" -type f 2>/dev/null | wc -l)

      local bug_count
      bug_count=$(grep -cP '^\s*##\s+Bug\s+\d+' "$report" 2>/dev/null || echo "0")

      if (( bug_count > 0 )) && (( repro_count == 0 )); then
        echo "  ⚠ WARNING: ${name} has ${bug_count} bug(s) but NO reproduction tests in repro/"
        echo "    Reproduction is MANDATORY. Re-run bug confirmation for this target."
      elif (( repro_count > 0 )); then
        echo "  ✓ ${name}: ${repro_count} reproduction test(s) in repro/"
      fi
    else
      echo "  ${name}: (no report)"
    fi
  done
}

main
