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
#   --recheck           Re-check mode: settle RECHECK repair requests (confirmation back-edge)
#   --max-repair-rounds=N  Per-request repair cap honored in --recheck (default: 0 = unlimited)
#   --max-parallel=N    Max concurrent agents (default: 1)
#   --max-turns=N       Max agent turns (default: 0 = unlimited)
#   --agent=NAME        Agent adapter to use (default: claude-code)
#   --claude-alias=NAME Claude CLI profile (default: claude)
#   --artifact=PATH     Explicit path to the artifact repo (overrides auto-detection)
#
# Prerequisites:
#   - Bug report at <name>/spec/bug-report.md (from Phase 3)
#   - Modeling brief at <name>/modeling-brief.md (from Phase 1)
#   - Source repo at <name>/artifact/<repo>/ (or supplied via --artifact)

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SPECULA_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
MAX_PARALLEL=1
MAX_TURNS=0
DRY_RUN=false
CHECK_ONLY=false
RECHECK_MODE=false
MAX_REPAIR_ROUNDS=0
AGENT="claude-code"
CLAUDE_ALIAS="${CLAUDE_ALIAS:-claude}"
ARTIFACT=""
TARGETS=()

# ──────────────────────────────────────────────────────────
# Parse arguments
# ──────────────────────────────────────────────────────────
for arg in "$@"; do
  case "$arg" in
    --dry-run) DRY_RUN=true ;;
    --check) CHECK_ONLY=true ;;
    --recheck) RECHECK_MODE=true ;;
    --max-repair-rounds=*) MAX_REPAIR_ROUNDS="${arg#*=}" ;;
    --max-parallel=*) MAX_PARALLEL="${arg#*=}" ;;
    --max-turns=*) MAX_TURNS="${arg#*=}" ;;
    --agent=*) AGENT="${arg#*=}" ;;
    --claude-alias=*) CLAUDE_ALIAS="${arg#*=}" ;;
    --artifact=*) ARTIFACT="${arg#*=}" ;;
    --help|-h)
      sed -n '2,/^$/{ s/^# //; s/^#//; p }' "$0"
      exit 0
      ;;
    -*) echo "Unknown option: $arg"; exit 1 ;;
    *) TARGETS+=("$arg") ;;
  esac
done

if [[ ${#TARGETS[@]} -eq 0 ]]; then
  TARGETS+=("$(basename "$PWD")")
fi

ADAPTER="$SCRIPT_DIR/adapters/${AGENT}.sh"
if [[ ! -f "$ADAPTER" ]]; then
  echo "ERROR: Unknown agent '${AGENT}' — adapter not found at ${ADAPTER}"
  exit 1
fi

# ──────────────────────────────────────────────────────────
# Resolve working directory for a target
# ──────────────────────────────────────────────────────────
get_work_dir() {
  local name="$1"
  if (( ${#TARGETS[@]} == 1 )); then
    echo "$PWD/.specula-output"
  else
    echo "$PWD/${name}/.specula-output"
  fi
}

# ──────────────────────────────────────────────────────────
# Find artifact repo directory
# ──────────────────────────────────────────────────────────
find_repo_dir() {
  local name="$1"
  if [[ -n "$ARTIFACT" ]]; then
    echo "$ARTIFACT"
    return
  fi
  local artifact_dir="$PWD/${name}/artifact"
  if [[ -d "$artifact_dir" ]]; then
    for d in "$artifact_dir"/*/; do
      if [[ -d "${d}.git" || -f "${d}.git" ]]; then
        echo "$d"
        return
      fi
    done
  fi
  if (( ${#TARGETS[@]} == 1 )); then
    echo "$PWD"
    return
  fi
}

# ──────────────────────────────────────────────────────────
# Check prerequisites
# ──────────────────────────────────────────────────────────
check_prereqs() {
  local ok=true
  for name in "${TARGETS[@]}"; do
    name="$(echo "$name" | xargs)"
    local work_dir
    work_dir="$(get_work_dir "$name")"
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
# Generate re-check-mode prompt (confirmation back-edge)
# ──────────────────────────────────────────────────────────
generate_recheck_prompt() {
  local name="$1" repo_dir="$2"
  local work_dir
  work_dir="$(get_work_dir "$name")"
  local spec_dir="${work_dir}/spec"

  cat <<PROMPT_EOF
# Bug Re-check Task (confirmation back-edge): ${name}

You are running the bug-confirmation **RE-CHECK** pass. Phase 3 (repair mode) has repaired
the spec for the open repair requests and moved them to \`status: RECHECK\`. Settle each
finding and transition its request out of RECHECK.

## Inputs
- **Repair requests**: ${spec_dir}/repair-requests/   (process ONLY status RECHECK)
- **Updated bug report + TLC output**: ${spec_dir}/bug-report.md , ${spec_dir}/output/
- **Confirmed bugs (you update this)**: ${spec_dir}/confirmed-bugs.md
- **Source code**: ${repo_dir}
- **Per-request cap**: --max-repair-rounds=${MAX_REPAIR_ROUNDS}   (0 = unlimited)

## Methodology — read and follow
- ${SPECULA_ROOT}/.claude/skills/bug-confirmation/phases/03-recheck.md
- ${SPECULA_ROOT}/.claude/skills/bug-confirmation/references/repair-request-format.md

## Task
For each repair request with \`status: RECHECK\` (ignore every other status):
- Compare the re-run result against the request's original counterexample.
- Transition the request to **exactly one** of RESOLVED / REOPENED / DEFERRED —
  **never leave it RECHECK**.
- Update the linked finding's entry in \`confirmed-bugs.md\` accordingly. You — not the
  orchestrator — own every confirmed-bugs.md status write.
- **Per-request cap**: if \`--max-repair-rounds\` is > 0 and the request's own \`round\`
  >= that cap, DEFER it instead of reopening.
- **Anti-oscillation**: never REOPEN with a repair already tried in the request's History.

## Critical rules
- Process ONLY \`status: RECHECK\` requests.
- Every processed request MUST leave RECHECK (RESOLVED / REOPENED / DEFERRED).
- Budget / quota is NOT a reason to defer.
- A DEFERRED finding is preserved for a developer with its full repair history — never dropped.
PROMPT_EOF
}

# ──────────────────────────────────────────────────────────
# Generate agent prompt
# ──────────────────────────────────────────────────────────
generate_prompt() {
  local name="$1" repo_dir="$2"
  local work_dir
  work_dir="$(get_work_dir "$name")"
  local spec_dir="${work_dir}/spec"

  if $RECHECK_MODE; then
    generate_recheck_prompt "$name" "$repo_dir"
  else
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

Consolidate the two finding sources into one candidate list:
- **MC findings** (with counterexamples): \`${spec_dir}/bug-report.md\`
- **Code-review findings**: \`${work_dir}/modeling-brief.md\`

Then process every candidate **strictly per the bug-confirmation skill's Flow** — do not restate, relax, or override it here. In particular:
- Apply **only** the skill's single pre-filter (code-review-sourced **and** already-known → drop before Phase 2, exactly as the skill defines it). Invent no other pre-filter — never skip a candidate as "defensive coding", "style", or "theoretical-only".
- Follow the skill's Phase 1 (investigation) and Phase 2 (strict Level 0→3 escalation ladder), and use its per-bug output schema and statuses.

Write the consolidated report to \`${spec_dir}/confirmed-bugs.md\`, with one \`repro/\` test per non-dropped finding under \`${work_dir}/repro/\`, exactly as the skill specifies.
PROMPT_EOF
  fi

  # Inject per-target extra prompt if present (prefer the target work dir)
  local extra="${work_dir}/.prompt-extra.md"
  if [[ ! -f "$extra" ]]; then
    extra="$PWD/.prompt-extra.md"
  fi
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
  local work_dir
  work_dir="$(get_work_dir "$name")"
  local tag="bug-confirmation"
  $RECHECK_MODE && tag="bug-recheck"
  local log_file="${work_dir}/${tag}.log"
  local prompt_file="${work_dir}/.${tag}-prompt.md"

  echo "$prompt" > "$prompt_file"

  echo "[$(date '+%H:%M:%S')] Launching agent: ${name}"

  if $DRY_RUN; then
    echo "  [DRY RUN] $ADAPTER --prompt=<prompt> --max-turns=${MAX_TURNS} --log=${log_file} --background"
    echo "  Prompt saved: ${prompt_file}"
    return 0
  fi

  "$ADAPTER" --prompt-file="$prompt_file" --max-turns="$MAX_TURNS" --claude-alias="$CLAUDE_ALIAS" --effort=max --log="$log_file" --background &
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
      running_pids+=("$(cat "$(get_work_dir "$name")/bug-confirmation.pid")")
    fi
    echo ""
  done

  if ! $DRY_RUN; then
    echo "[$(date '+%H:%M:%S')] All agents launched. Waiting..."
    echo "  Monitor: tail -f */bug-confirmation.log"
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
    local work_dir
    work_dir="$(get_work_dir "$name")"
    local report="${work_dir}/spec/confirmed-bugs.md"

    local repro_dir="${work_dir}/repro"
    local repro_count=0
    [[ -d "$repro_dir" ]] && repro_count=$(find "$repro_dir" -name "test_bug*" -type f 2>/dev/null | wc -l)

    if [[ -s "$report" ]]; then
      echo "  ${name}: confirmed-bugs.md written ($(wc -l < "$report") lines, repro/ tests: ${repro_count})"
    elif [[ -f "$report" ]]; then
      echo "  ${name}: confirmed-bugs.md empty (check log; repro/ tests: ${repro_count})"
    else
      echo "  ${name}: (no report — check log; repro/ tests: ${repro_count})"
    fi
  done
}

main
