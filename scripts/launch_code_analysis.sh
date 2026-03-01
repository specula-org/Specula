#!/usr/bin/env bash
#
# Batch launcher: spawn one Claude Code agent per target system for code analysis.
# Each agent follows the code-analysis skill methodology and produces a modeling brief.
#
# Usage:
#   bash scripts/launch_code_analysis.sh [options] "name|github|lang|reference" [...]
#
# Example:
#   bash scripts/launch_code_analysis.sh \
#     "braft|brpc/braft|C++|Raft (Ongaro 2014)" \
#     "sofa-jraft|sofastack/sofa-jraft|Java|Raft (Ongaro 2014)" \
#     "dragonboat|lni/dragonboat|Go|Raft (Ongaro 2014)"
#
# Options:
#   --dry-run           Print commands without executing
#   --check             Only verify repos exist
#   --max-parallel=N    Max concurrent agents (default: 1)
#   --max-turns=N       Max agent turns (default: 0 = unlimited)
#
# Prerequisites:
#   - claude CLI installed and authenticated
#   - gh CLI installed and authenticated
#   - Repos cloned at case-studies/<name>/artifact/<repo>/

set -euo pipefail
unset CLAUDECODE 2>/dev/null || true

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SPECULA_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
CASE_STUDIES_DIR="$SPECULA_ROOT/case-studies"
MAX_PARALLEL=1
MAX_TURNS=0
DRY_RUN=false
CHECK_ONLY=false
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
    --help|-h)
      sed -n '2,/^$/{ s/^# //; s/^#//; p }' "$0"
      exit 0
      ;;
    -*) echo "Unknown option: $arg"; exit 1 ;;
    *) TARGETS+=("$arg") ;;
  esac
done

if [[ ${#TARGETS[@]} -eq 0 ]]; then
  echo "Usage: $0 [options] \"name|github|lang|reference\" [...]"
  echo "Run $0 --help for details."
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
    if [[ -d "${d}.git" ]]; then
      echo "$d"
      return
    fi
  done
}

# ──────────────────────────────────────────────────────────
# Check all repos are present
# ──────────────────────────────────────────────────────────
check_repos() {
  local ok=true
  for target in "${TARGETS[@]}"; do
    IFS='|' read -r name _ _ _ <<< "$target"
    name="$(echo "$name" | xargs)"
    local repo_dir
    repo_dir="$(find_repo_dir "$name")"
    if [[ -n "$repo_dir" ]]; then
      local commits
      commits=$(cd "$repo_dir" && git rev-list --count HEAD 2>/dev/null || echo "?")
      echo "  OK  ${name} (${commits} commits)"
    else
      echo "  MISSING  ${name} — expected at ${CASE_STUDIES_DIR}/${name}/artifact/<repo>/"
      ok=false
    fi
  done
  $ok
}

# ──────────────────────────────────────────────────────────
# Generate agent prompt
# ──────────────────────────────────────────────────────────
generate_prompt() {
  local name="$1" github_short="$2" language="$3" reference="$4" repo_dir="$5"
  local work_dir="${CASE_STUDIES_DIR}/${name}"

  cat <<PROMPT_EOF
# Code Analysis Task

You are analyzing the following system:

- **Name**: ${name}
- **GitHub**: ${github_short}
- **Language**: ${language}
- **Reference Algorithm**: ${reference}
- **Repository**: ${repo_dir}
- **Working Directory**: ${work_dir}

## Instructions

Follow the **code-analysis** skill methodology. Read the skill guide at:
  ${SPECULA_ROOT}/.claude/skills/code_analysis/guide.md

Then read the reference files as needed:
  ${SPECULA_ROOT}/.claude/skills/code_analysis/references/bug-archaeology.md
  ${SPECULA_ROOT}/.claude/skills/code_analysis/references/deep-analysis.md
  ${SPECULA_ROOT}/.claude/skills/code_analysis/references/modeling-brief-format.md

And see the example:
  ${SPECULA_ROOT}/.claude/skills/code_analysis/examples/hashicorp-raft-modeling-brief.md

## Phases

Execute all 4 phases in order:

1. **Reconnaissance** — Build structural map of codebase
2. **Bug Archaeology** — Mine git history and GitHub issues/PRs for bugs
3. **Deep Analysis** — Systematic code reading to find new issues
4. **Modeling Brief** — Synthesize findings into modeling-brief.md

## Output

Write your outputs to:
- \`${work_dir}/modeling-brief.md\` — The primary deliverable (handoff to Spec Generation)
- \`${work_dir}/analysis-report.md\` — Detailed audit trail of all findings

## Critical Rules

1. VERIFY before reporting. Re-read code. Check for compensating mechanisms. No unverified claims.
2. Read issue DISCUSSIONS, not just titles. For any issue you plan to reference, read the full comment thread via \`gh issue view --comments\` to confirm it hasn't been debunked.
3. Do NOT hallucinate code logic. If unsure, READ IT. Cite file:line for every claim.
4. Use parallel Task subagents aggressively. Launch multiple subagents concurrently for: issue batch verification (5-10 issues per subagent), file-by-file deep analysis (one subagent per core file), and commit review. This is essential for both depth AND coverage.
5. Evidence-based claims only. Show code, git commits, issue discussions, or code path inconsistencies.
6. Bug Families over flat lists. Group by mechanism. 5 actionable families > 17 flat findings.
7. Every finding must be classified: model-checkable, test-verifiable, or code-review-only.
8. Thoroughness is non-negotiable. Analyze ALL bug-fix commits touching core files. Deeply read 30+ GitHub issues (full discussion threads). Report coverage statistics in the analysis report.
PROMPT_EOF
}

# ──────────────────────────────────────────────────────────
# Launch a single Claude Code agent
# ──────────────────────────────────────────────────────────
launch_agent() {
  local name="$1" prompt="$2"
  local work_dir="${CASE_STUDIES_DIR}/${name}"
  local log_file="${work_dir}/agent.log"
  local prompt_file="${work_dir}/.prompt.md"

  echo "$prompt" > "$prompt_file"

  echo "[$(date '+%H:%M:%S')] Launching agent: ${name}"

  if $DRY_RUN; then
    echo "  [DRY RUN] claude --print --dangerously-skip-permissions --max-turns ${MAX_TURNS} -p <prompt>"
    echo "  Prompt saved: ${prompt_file}"
    return 0
  fi

  nohup claude \
    --print \
    --dangerously-skip-permissions \
    --max-turns "$MAX_TURNS" \
    -p "$prompt" \
    > "$log_file" 2>&1 &

  local pid=$!
  echo "$pid" > "${work_dir}/agent.pid"
  echo "  PID=$pid  Log: $log_file"
}

# ──────────────────────────────────────────────────────────
# Main
# ──────────────────────────────────────────────────────────
main() {
  echo "========================================"
  echo " Specula — Code Analysis Batch Runner"
  echo "========================================"
  echo "Targets:      ${#TARGETS[@]}"
  echo "Max parallel: $MAX_PARALLEL"
  echo "Max turns:    $MAX_TURNS"
  echo ""

  echo "Checking repositories..."
  if ! check_repos; then
    echo ""
    echo "ERROR: Some repositories are missing. Clone them first."
    exit 1
  fi
  echo ""

  if $CHECK_ONLY; then
    echo "All repos OK."
    exit 0
  fi

  local running_pids=()

  for target in "${TARGETS[@]}"; do
    IFS='|' read -r name github_short language reference <<< "$target"
    name="$(echo "$name" | xargs)"
    github_short="$(echo "$github_short" | xargs)"
    language="$(echo "$language" | xargs)"
    reference="$(echo "$reference" | xargs)"

    local repo_dir
    repo_dir="$(find_repo_dir "$name")"

    local prompt
    prompt="$(generate_prompt "$name" "$github_short" "$language" "$reference" "$repo_dir")"

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
      running_pids+=("$(cat "${CASE_STUDIES_DIR}/${name}/agent.pid")")
    fi
    echo ""
  done

  if ! $DRY_RUN; then
    echo "[$(date '+%H:%M:%S')] All agents launched. Waiting..."
    echo "  Monitor: tail -f ${CASE_STUDIES_DIR}/*/agent.log"
    echo ""
    wait
    echo "[$(date '+%H:%M:%S')] All agents completed."
  fi

  # Summary
  echo ""
  echo "========================================"
  echo " Results"
  echo "========================================"
  for target in "${TARGETS[@]}"; do
    IFS='|' read -r name _ _ _ <<< "$target"
    name="$(echo "$name" | xargs)"
    local brief="${CASE_STUDIES_DIR}/${name}/modeling-brief.md"
    local report="${CASE_STUDIES_DIR}/${name}/analysis-report.md"
    if [[ -f "$brief" ]]; then
      local lines
      lines=$(wc -l < "$brief")
      echo "  OK  ${name} -> modeling-brief.md (${lines} lines)"
    elif [[ -f "$report" ]]; then
      local lines
      lines=$(wc -l < "$report")
      echo "  ~~  ${name} -> analysis-report.md only (${lines} lines, no modeling brief)"
    else
      echo "  --  ${name} (no output)"
    fi
  done
}

main
