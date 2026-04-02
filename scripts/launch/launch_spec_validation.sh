#!/usr/bin/env bash
#
# Batch launcher: spawn one Claude Code agent per target system for spec validation.
# Each agent iteratively runs trace validation and invariant checking using existing
# skills until both pass. Harness and traces must already exist (Phase 2.5).
#
# Usage:
#   bash scripts/launch/launch_spec_validation.sh [options] "name" [...]
#
# Example:
#   bash scripts/launch/launch_spec_validation.sh cometbft
#   bash scripts/launch/launch_spec_validation.sh braft sofa-jraft dragonboat
#   bash scripts/launch/launch_spec_validation.sh --artifact=/path/to/repo myproject
#
# Options:
#   --dry-run           Print commands without executing
#   --check             Only verify prerequisites exist
#   --max-parallel=N    Max concurrent agents (default: 1)
#   --max-turns=N       Max agent turns (default: 0 = unlimited)
#   --agent=NAME        Agent adapter to use (default: claude-code)
#   --artifact=PATH     Explicit path to the artifact repo (overrides auto-detection)
#
# Prerequisites:
#   - Spec files at <name>/.specula-output/spec/ (from Phase 2)
#   - Source repo at <name>/artifact/<repo>/ or specified via --artifact

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SPECULA_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
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
# Resolve working directory and artifact repo
# ──────────────────────────────────────────────────────────
get_work_dir() {
  local name="$1"
  if (( ${#TARGETS[@]} == 1 )); then
    echo "$PWD/.specula-output"
  else
    echo "$PWD/${name}/.specula-output"
  fi
}

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
    local spec_dir="$(get_work_dir "$name")/spec"
    local repo_dir
    repo_dir="$(find_repo_dir "$name")"

    printf "  %-20s" "$name"

    if [[ -f "${spec_dir}/base.tla" && -f "${spec_dir}/MC.tla" && -f "${spec_dir}/Trace.tla" ]]; then
      local base_lines
      base_lines=$(wc -l < "${spec_dir}/base.tla")
      printf "specs OK (%dL)" "$base_lines"
    else
      printf "specs MISSING"
      ok=false
    fi

    if [[ -f "${spec_dir}/instrumentation-spec.md" ]]; then
      printf "  instr OK"
    else
      printf "  instr MISSING"
      ok=false
    fi

    if [[ -n "$repo_dir" ]]; then
      printf "  repo OK"
    else
      printf "  repo MISSING"
      ok=false
    fi

    # Warn if traces don't exist (not fatal — agent can adjust instrumentation)
    local traces_dir="$(get_work_dir "$name")/traces"
    local trace_count=0
    [[ -d "$traces_dir" ]] && trace_count=$(find "$traces_dir" -name "*.ndjson" 2>/dev/null | wc -l)
    if [[ $trace_count -gt 0 ]]; then
      printf "  traces OK (%d)" "$trace_count"
    else
      printf "  traces WARN (0 ndjson files)"
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
  local work_dir="$(get_work_dir "$name")"
  local spec_dir="${work_dir}/spec"

  cat <<PROMPT_EOF
# Spec Validation Task: ${name}

You are validating the TLA+ specification for **${name}** through iterative trace validation and invariant checking.

## Inputs

- **Spec directory**: ${spec_dir}
  - base.tla, base.cfg — Base specification
  - MC.tla, MC.cfg — Model checking specification
  - Trace.tla, Trace.cfg — Trace validation specification
  - instrumentation-spec.md — Action-to-code mapping for harness generation
- **Source code**: ${repo_dir}
- **Modeling brief**: ${work_dir}/modeling-brief.md

## Workflow

Read and follow the **validation-workflow** skill:
  ${SPECULA_ROOT}/.claude/skills/validation-workflow/guide.md

This skill orchestrates the iterative loop between trace validation and model checking.
It delegates to two sub-skills (read these too):
  ${SPECULA_ROOT}/.claude/skills/tla-trace-workflow/guide.md
  ${SPECULA_ROOT}/.claude/skills/tla-checking-workflow/guide.md

Determine whether the target is Category A or Category B from \`${work_dir}/modeling-brief.md\`, the trace layout, and the instrumentation spec before debugging. Do not assume linear single-file traces for concurrent systems.

## Pre-step: Verify harness and traces

Harness and traces should already exist from Phase 2.5 (harness generation). Verify:
- Trace files in: ${work_dir}/traces/
- Instrumentation guide: ${work_dir}/harness/INSTRUMENTATION.md

If instrumentation adjustments are needed during validation, read \`harness/INSTRUMENTATION.md\` for how to modify capture points and fields, then re-run \`bash harness/run.sh\` to regenerate traces.

## Critical Rules

1. Follow the validation-workflow skill — do not invent your own methodology.
2. The implementation is ground truth. When spec and implementation disagree, the spec is wrong (unless it's a real bug).
3. For Case C (real bug found): STOP and document it clearly. Do not "fix" real bugs.
4. For abstraction gaps: document them and make a pragmatic choice, then continue.
5. If the system is Category B, preserve the partial-order/timebox validation model. Do not "simplify" it into a linear trace workflow just to make validation easier.
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
  local log_file="${work_dir}/spec-validation.log"
  local prompt_file="${work_dir}/.spec-validation-prompt.md"

  mkdir -p "${work_dir}/traces"
  echo "$prompt" > "$prompt_file"

  echo "[$(date '+%H:%M:%S')] Launching agent: ${name}"

  if $DRY_RUN; then
    echo "  [DRY RUN] $ADAPTER --prompt=<prompt> --max-turns=${MAX_TURNS} --log=${log_file} --background"
    echo "  Prompt saved: ${prompt_file}"
    return 0
  fi

  "$ADAPTER" --prompt-file="$prompt_file" --max-turns="$MAX_TURNS" --log="$log_file" --background &
  local pid=$!
  echo "$pid" > "${work_dir}/spec-validation.pid"
  echo "  PID=$pid  Log: $log_file"
}

# ──────────────────────────────────────────────────────────
# Main
# ──────────────────────────────────────────────────────────
main() {
  echo "========================================"
  echo " Specula — Spec Validation Batch Runner"
  echo "========================================"
  echo "Targets:      ${#TARGETS[@]}"
  echo "Max parallel: $MAX_PARALLEL"
  echo "Max turns:    $MAX_TURNS"
  echo ""

  echo "Checking prerequisites..."
  if ! check_prereqs; then
    echo ""
    echo "ERROR: Missing prerequisites. Run spec generation first."
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
      running_pids+=("$(cat "$(get_work_dir "$name")/spec-validation.pid")")
    fi
    echo ""
  done

  if ! $DRY_RUN; then
    echo "[$(date '+%H:%M:%S')] All agents launched. Waiting..."
    echo "  Monitor: tail -f ${PWD}/*/.specula-output/spec-validation.log"
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
    local changelog="${spec_dir}/changelog.md"

    local status="(check log)"
    if [[ -f "$changelog" ]]; then
      local result
      result=$(grep -i "^## Result" -A1 "$changelog" | tail -1)
      result="${result:-changelog exists, no result yet}"
      status="$result"
    fi

    echo "  ${name}: ${status}"
  done
}

main
