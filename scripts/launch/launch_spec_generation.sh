#!/usr/bin/env bash
#
# Batch launcher: spawn one Claude Code agent per target system for TLA+ spec generation.
# Each agent follows the spec-generation skill methodology and produces base/MC/Trace specs.
#
# Usage:
#   bash scripts/launch/launch_spec_generation.sh [options] "name" [...]
#
# Example:
#   bash scripts/launch/launch_spec_generation.sh cometbft
#   bash scripts/launch/launch_spec_generation.sh braft sofa-jraft dragonboat
#
# Options:
#   --dry-run           Print commands without executing
#   --check             Only verify prerequisites exist
#   --max-parallel=N    Max concurrent agents (default: 1)
#   --max-turns=N       Max agent turns (default: 0 = unlimited)
#   --agent=NAME        Agent adapter to use (default: claude-code)
#
# Prerequisites:
#   - claude CLI installed and authenticated
#   - modeling-brief.md exists at case-studies/<name>/modeling-brief.md
#   - Source repo cloned at case-studies/<name>/artifact/<repo>/

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SPECULA_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
CASE_STUDIES_DIR="$SPECULA_ROOT/case-studies"
SKILL_DIR="$SPECULA_ROOT/.claude/skills/spec_generation"
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
    if [[ -d "${d}.git" ]]; then
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
    local brief="${CASE_STUDIES_DIR}/${name}/modeling-brief.md"
    local repo_dir
    repo_dir="$(find_repo_dir "$name")"

    if [[ -f "$brief" ]]; then
      local lines
      lines=$(wc -l < "$brief")
      printf "  %-20s modeling-brief.md (%d lines)" "$name" "$lines"
    else
      printf "  %-20s MISSING modeling-brief.md" "$name"
      ok=false
    fi

    if [[ -n "$repo_dir" ]]; then
      echo "  repo OK"
    else
      echo "  repo MISSING"
      ok=false
    fi
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
  local brief="${work_dir}/modeling-brief.md"

  cat <<PROMPT_EOF
# TLA+ Spec Generation Task

You are generating a TLA+ specification for: **${name}**

## Inputs

- **Modeling Brief**: ${brief}
- **Source Code**: ${repo_dir}
- **Output Directory**: ${spec_dir}

## Instructions

Follow the **spec-generation** skill methodology. Read the skill guide at:
  ${SKILL_DIR}/guide.md

Then read the reference files:
  ${SKILL_DIR}/references/base-spec-methodology.md
  ${SKILL_DIR}/references/mc-spec-pattern.md
  ${SKILL_DIR}/references/trace-spec-pattern.md
  ${SKILL_DIR}/references/instrumentation-spec-format.md

## Phases

Execute all 4 phases in order:

1. **Base Spec** — Write \`base.tla\` + \`base.cfg\` with bug-family driven extensions
2. **MC Spec** — Write \`MC.tla\` + \`MC.cfg\` with counter-bounded actions
3. **Trace Spec** — Write \`Trace.tla\` + \`Trace.cfg\` for trace validation
4. **Instrumentation Spec** — Write \`instrumentation-spec.md\` with action-to-code mapping

## Output

Create the output directory and write all files to:
  ${spec_dir}/

Expected files:
- \`${spec_dir}/base.tla\` — Base specification
- \`${spec_dir}/base.cfg\` — Base config
- \`${spec_dir}/MC.tla\` — Model checking specification
- \`${spec_dir}/MC.cfg\` — Model checking config
- \`${spec_dir}/Trace.tla\` — Trace validation specification
- \`${spec_dir}/Trace.cfg\` — Trace validation config
- \`${spec_dir}/instrumentation-spec.md\` — Instrumentation mapping

## Critical Rules

1. Every extension traces to a Bug Family. No Bug Family reference = don't add the extension.
2. Model the implementation, not the paper. Deviations from the reference algorithm are where bugs live.
3. Follow the code's control flow faithfully. Do not simplify, reorder, or merge logic that the code keeps separate.
4. Annotate every logic block with source lines (file:line). Not optional.
5. Write to files early and often. Insurance against context loss.
6. Split actions where code paths diverge. Merging hides bugs.
7. Name actions after implementation functions. Enables cross-referencing with code.
8. Silent actions must be tightly constrained. Unconstrained silent actions cause state space explosion.
9. MC spec bounds fault-injection, not normal operations.
PROMPT_EOF
}

# ──────────────────────────────────────────────────────────
# Launch a single Claude Code agent
# ──────────────────────────────────────────────────────────
launch_agent() {
  local name="$1" prompt="$2"
  local work_dir="${CASE_STUDIES_DIR}/${name}"
  local spec_dir="${work_dir}/spec"
  local log_file="${work_dir}/spec-gen.log"
  local prompt_file="${work_dir}/.spec-gen-prompt.md"

  mkdir -p "$spec_dir"
  echo "$prompt" > "$prompt_file"

  echo "[$(date '+%H:%M:%S')] Launching agent: ${name}"

  if $DRY_RUN; then
    echo "  [DRY RUN] $ADAPTER --prompt=<prompt> --max-turns=${MAX_TURNS} --log=${log_file} --background"
    echo "  Prompt saved: ${prompt_file}"
    return 0
  fi

  local pid
  pid=$("$ADAPTER" --prompt="$prompt" --max-turns="$MAX_TURNS" --log="$log_file" --background)
  echo "$pid" > "${work_dir}/spec-gen.pid"
  echo "  PID=$pid  Log: $log_file"
}

# ──────────────────────────────────────────────────────────
# Main
# ──────────────────────────────────────────────────────────
main() {
  echo "========================================"
  echo " Specula — Spec Generation Batch Runner"
  echo "========================================"
  echo "Targets:      ${#TARGETS[@]}"
  echo "Max parallel: $MAX_PARALLEL"
  echo "Max turns:    $MAX_TURNS"
  echo ""

  echo "Checking prerequisites..."
  if ! check_prereqs; then
    echo ""
    echo "ERROR: Missing prerequisites. Run code analysis first."
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
      running_pids+=("$(cat "${CASE_STUDIES_DIR}/${name}/spec-gen.pid")")
    fi
    echo ""
  done

  if ! $DRY_RUN; then
    echo "[$(date '+%H:%M:%S')] All agents launched. Waiting..."
    echo "  Monitor: tail -f ${CASE_STUDIES_DIR}/*/spec-gen.log"
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
    local spec_dir="${CASE_STUDIES_DIR}/${name}/spec"
    local base="${spec_dir}/base.tla"
    local mc="${spec_dir}/MC.tla"
    local trace="${spec_dir}/Trace.tla"
    local instr="${spec_dir}/instrumentation-spec.md"

    local count=0
    [[ -f "$base" ]] && count=$((count + 1))
    [[ -f "$mc" ]] && count=$((count + 1))
    [[ -f "$trace" ]] && count=$((count + 1))
    [[ -f "$instr" ]] && count=$((count + 1))

    if [[ $count -eq 4 ]]; then
      local lines
      lines=$(wc -l < "$base")
      echo "  OK  ${name} -> ${count}/4 files (base.tla: ${lines} lines)"
    elif [[ $count -gt 0 ]]; then
      echo "  ~~  ${name} -> ${count}/4 files (incomplete)"
      [[ ! -f "$base" ]] && echo "        missing: base.tla"
      [[ ! -f "$mc" ]] && echo "        missing: MC.tla"
      [[ ! -f "$trace" ]] && echo "        missing: Trace.tla"
      [[ ! -f "$instr" ]] && echo "        missing: instrumentation-spec.md"
    else
      echo "  --  ${name} (no output)"
    fi
  done
}

main
