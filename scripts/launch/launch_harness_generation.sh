#!/usr/bin/env bash
#
# Batch launcher: spawn one Claude Code agent per target system for harness generation (Phase 2.5).
# Each agent instruments the source code and collects NDJSON traces for spec validation.
#
# Usage:
#   bash scripts/launch/launch_harness_generation.sh [options] "name" [...]
#
# Example:
#   bash scripts/launch/launch_harness_generation.sh cometbft
#   bash scripts/launch/launch_harness_generation.sh braft sofa-jraft dragonboat
#   bash scripts/launch/launch_harness_generation.sh --artifact=/path/to/repo myproject
#
# Options:
#   --dry-run           Print commands without executing
#   --check             Only verify prerequisites exist
#   --max-parallel=N    Max concurrent agents (default: 1)
#   --max-turns=N       Max agent turns (default: 0 = unlimited)
#   --agent=NAME        Agent adapter to use (default: claude-code)
#   --claude-alias=NAME Claude CLI profile (default: claude; e.g. claude-exp)
#   --artifact=PATH     Explicit path to artifact repo (overrides auto-detection)
#
# Prerequisites:
#   - claude CLI installed and authenticated
#   - Phase 2 complete: spec/base.tla, spec/Trace.tla, spec/instrumentation-spec.md
#   - Source repo at <name>/artifact/<repo>/ or specified via --artifact

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SPECULA_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
SKILL_DIR="$SPECULA_ROOT/.claude/skills/harness-generation"
MAX_PARALLEL=1
MAX_TURNS=0
DRY_RUN=false
CHECK_ONLY=false
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
# Check prerequisites (Phase 2 outputs must exist)
# ──────────────────────────────────────────────────────────
check_prereqs() {
  local ok=true
  for name in "${TARGETS[@]}"; do
    name="$(echo "$name" | xargs)"
    local spec_dir="$(get_work_dir "$name")/spec"
    local repo_dir
    repo_dir="$(find_repo_dir "$name")"

    printf "  %-20s" "$name"

    # Check specs
    if [[ -f "${spec_dir}/base.tla" && -f "${spec_dir}/Trace.tla" ]]; then
      printf "specs OK"
    else
      printf "specs MISSING"
      ok=false
    fi

    # Check instrumentation spec
    if [[ -f "${spec_dir}/instrumentation-spec.md" ]]; then
      printf "  instr OK"
    else
      printf "  instr MISSING"
      ok=false
    fi

    # Check artifact repo
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

  cat <<PROMPT_EOF
# Trace Harness Generation Task: ${name}

You are generating a trace harness for **${name}** — instrumenting the real source code to produce NDJSON traces for TLA+ trace validation.

## Inputs

- **Instrumentation spec**: ${spec_dir}/instrumentation-spec.md
- **Trace spec**: ${spec_dir}/Trace.tla + ${spec_dir}/Trace.cfg
- **Base spec**: ${spec_dir}/base.tla (for understanding spec actions)
- **Source code**: ${repo_dir}

## Workflow

Read and follow the **harness-generation** skill:
  ${SKILL_DIR}/guide.md

Then read the reference:
  ${SKILL_DIR}/references/trace-module-patterns.md

## Output

Write all harness files to: ${work_dir}/harness/
Collect traces to: ${work_dir}/traces/

Expected outputs:
- \`${work_dir}/harness/src/\` — Trace emission module + test scenarios
- \`${work_dir}/harness/apply.sh\` — Apply instrumentation to artifact
- \`${work_dir}/harness/run.sh\` — One-command build + run + collect traces
- \`${work_dir}/harness/INSTRUMENTATION.md\` — Guide for Phase 3 agent to adjust instrumentation
- \`${work_dir}/traces/*.ndjson\` — Trace files from test runs

## Critical Rules

1. Instrument real code, not a simulator. The trace must capture what the real system does.
2. Never hand-write traces. Every trace line must come from running instrumented code.
3. Match the instrumentation spec exactly. Event names, field names, trigger points.
4. Real timestamps only. Sequential integers (1000, 1001, 1002) indicate hand-written traces.
5. run.sh must work end-to-end. Anyone should be able to reproduce traces with a single command.
6. Run a quick trace validation at the end to catch obvious format issues.
PROMPT_EOF

  # Inject per-target extra prompt if present (check case-study root first, then .specula-output)
  local extra="$PWD/.prompt-extra.md"
  if [[ ! -f "$extra" ]]; then
    extra="${work_dir}/.prompt-extra.md"
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
  local work_dir="$(get_work_dir "$name")"
  local log_file="${work_dir}/harness-gen.log"
  local prompt_file="${work_dir}/.harness-gen-prompt.md"

  mkdir -p "${work_dir}/harness" "${work_dir}/traces"
  echo "$prompt" > "$prompt_file"

  echo "[$(date '+%H:%M:%S')] Launching agent: ${name}"

  if $DRY_RUN; then
    echo "  [DRY RUN] $ADAPTER --prompt=<prompt> --max-turns=${MAX_TURNS} --log=${log_file} --background"
    echo "  Prompt saved: ${prompt_file}"
    return 0
  fi

  "$ADAPTER" --prompt-file="$prompt_file" --max-turns="$MAX_TURNS" --claude-alias="$CLAUDE_ALIAS" --log="$log_file" --background &
  local pid=$!
  echo "$pid" > "${work_dir}/harness-gen.pid"
  echo "  PID=$pid  Log: $log_file"
}

# ──────────────────────────────────────────────────────────
# Main
# ──────────────────────────────────────────────────────────
main() {
  echo "========================================"
  echo " Specula — Harness Generation (Phase 2.5)"
  echo "========================================"
  echo "Targets:      ${#TARGETS[@]}"
  echo "Max parallel: $MAX_PARALLEL"
  echo "Max turns:    $MAX_TURNS"
  echo ""

  echo "Checking prerequisites..."
  if ! check_prereqs; then
    echo ""
    echo "ERROR: Missing prerequisites. Run spec generation (Phase 2) first."
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
      running_pids+=("$(cat "$(get_work_dir "$name")/harness-gen.pid")")
    fi
    echo ""
  done

  if ! $DRY_RUN; then
    echo "[$(date '+%H:%M:%S')] All agents launched. Waiting..."
    echo "  Monitor: tail -f */.specula-output/harness-gen.log"
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
    local work_dir="$(get_work_dir "$name")"
    local harness_dir="${work_dir}/harness"
    local traces_dir="${work_dir}/traces"

    local has_run=false has_apply=false has_guide=false trace_count=0
    [[ -f "${harness_dir}/run.sh" ]] && has_run=true
    [[ -f "${harness_dir}/apply.sh" ]] && has_apply=true
    [[ -f "${harness_dir}/INSTRUMENTATION.md" ]] && has_guide=true
    if [[ -d "$traces_dir" ]]; then
      trace_count=$(find "$traces_dir" -name "*.ndjson" 2>/dev/null | wc -l)
    fi

    if $has_run && [[ $trace_count -gt 0 ]]; then
      echo "  OK  ${name} -> run.sh: yes, traces: ${trace_count}"
      $has_guide || echo "        warning: missing INSTRUMENTATION.md"
    elif $has_run; then
      echo "  ~~  ${name} -> run.sh: yes, traces: 0 (no traces generated)"
    else
      echo "  --  ${name} (no harness output)"
    fi
  done
}

main
