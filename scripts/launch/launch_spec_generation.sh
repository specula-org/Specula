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
#   --artifact=PATH     Explicit path to the artifact repo (bypasses auto-detection)
#
# Prerequisites:
#   - claude CLI installed and authenticated
#   - modeling-brief.md exists at <name>/.specula-output/modeling-brief.md
#   - Source repo cloned at <name>/artifact/<repo>/ (or supplied via --artifact)

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SPECULA_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
SKILL_DIR="$SPECULA_ROOT/.claude/skills/spec_generation"
MAX_PARALLEL=1
MAX_TURNS=0
DRY_RUN=false
CHECK_ONLY=false
AGENT="claude-code"
ARTIFACT=""
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
# Resolve work directory (.specula-output) for a target
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
    local brief="$(get_work_dir "$name")/modeling-brief.md"
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
  local work_dir="$(get_work_dir "$name")"
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

Before writing specs, read \`${brief}\` and determine whether this target is Category A (distributed/message-passing) or Category B (concurrent/lock-free/runtime). If it is Category B, shape the spec around thread-local state, linearization points, stale views, memory ordering, reclamation, and ownership transfer. Do not force a message-bag / protocol-state template onto the code.

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
10. For Category B systems, split API-level operations at real semantic boundaries (read/confirm, reserve/publish, retire/reclaim, signal/complete). Do not collapse them into single actions unless the code is truly atomic there.
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
  local work_dir="$(get_work_dir "$name")"
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

  "$ADAPTER" --prompt-file="$prompt_file" --max-turns="$MAX_TURNS" --log="$log_file" --background &
  local pid=$!
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
      running_pids+=("$(cat "$(get_work_dir "$name")/spec-gen.pid")")
    fi
    echo ""
  done

  if ! $DRY_RUN; then
    echo "[$(date '+%H:%M:%S')] All agents launched. Waiting..."
    echo "  Monitor: tail -f */.specula-output/spec-gen.log"
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
    local spec_dir="$(get_work_dir "$name")/spec"
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
