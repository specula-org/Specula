#!/usr/bin/env bash
#
# Full Specula pipeline: Code Analysis → Spec Generation → Harness Generation → Validation + Bug Hunting
#
# Runs all phases with optional review agents between each phase.
# All agent logs and review results are saved for inspection.
#
# Usage:
#   bash scripts/launch/launch_pipeline.sh [options] "name|github|lang|reference" [...]
#
# Example (single system):
#   bash scripts/launch/launch_pipeline.sh "cometbft|cometbft/cometbft|Go|Tendermint BFT"
#
# Example (multiple systems):
#   bash scripts/launch/launch_pipeline.sh \
#     "braft|brpc/braft|C++|Raft (Ongaro 2014)" \
#     "sofa-jraft|sofastack/sofa-jraft|Java|Raft (Ongaro 2014)"
#
# Options:
#   --dry-run              Print commands without executing
#   --skip-analysis        Skip code analysis (use existing outputs)
#   --skip-specgen         Skip spec generation (use existing outputs)
#   --skip-harness         Skip harness generation (use existing harness/traces)
#   --skip-validation      Skip validation
#   --enable-reviews        Enable review steps (disabled by default)
#   --max-parallel=N       Max concurrent agents per phase (default: 1)
#   --max-turns=N          Max agent turns (default: 0 = unlimited)
#   --agent=NAME           Agent adapter to use (default: claude-code; e.g., claude-code, codex, copilot-cli)
#   --artifact=PATH        Path to system artifact/source code
#
# Output structure (per system):
#   .specula-output/
#     ├── analysis-report.md          # Phase 1 output
#     ├── modeling-brief.md           # Phase 1 output
#     ├── agent.log                   # Phase 1 agent log
#     ├── review-analysis.md          # Phase 1 review
#     ├── review-analysis.log         # Phase 1 review agent log
#     ├── spec/
#     │   ├── base.tla                # Phase 2 output
#     │   ├── MC.tla                  # Phase 2 output
#     │   ├── Trace.tla               # Phase 2 output
#     │   ├── instrumentation-spec.md # Phase 2 output
#     │   ├── MC_hunt_*.cfg          # Phase 2 output (bug hunting configs)
#     │   ├── changelog.md           # Phase 3 output
#     │   ├── output/                # Phase 3 output (TLC results)
#     │   └── bug-report.md          # Phase 3 output (bug hunting results)
#     ├── harness/                     # Phase 2.5 output
#     │   ├── src/                   # Trace module + test scenarios
#     │   ├── apply.sh               # Apply instrumentation
#     │   ├── run.sh                 # Build + run + collect traces
#     │   └── INSTRUMENTATION.md     # Guide for adjusting instrumentation
#     ├── traces/                      # Phase 2.5 output (NDJSON traces)
#     ├── spec-gen.log                # Phase 2 agent log
#     ├── harness-gen.log             # Phase 2.5 agent log
#     └── pipeline.log                # This script's log

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SPECULA_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

MAX_PARALLEL=1
MAX_TURNS=0
DRY_RUN=false
SKIP_ANALYSIS=false
SKIP_SPECGEN=false
SKIP_HARNESS=false
SKIP_VALIDATION=false
SKIP_CONFIRMATION=false
SKIP_REVIEWS=true
AGENT="claude-code"
ARTIFACT=""
TARGETS=()

# ──────────────────────────────────────────────────────────
# Parse arguments
# ──────────────────────────────────────────────────────────
for arg in "$@"; do
  case "$arg" in
    --dry-run)           DRY_RUN=true ;;
    --skip-analysis)     SKIP_ANALYSIS=true ;;
    --skip-specgen)      SKIP_SPECGEN=true ;;
    --skip-harness)      SKIP_HARNESS=true ;;
    --skip-validation)   SKIP_VALIDATION=true ;;
    --skip-confirmation) SKIP_CONFIRMATION=true ;;
    --enable-reviews)    SKIP_REVIEWS=false ;;
    --max-parallel=*)    MAX_PARALLEL="${arg#*=}" ;;
    --max-turns=*)       MAX_TURNS="${arg#*=}" ;;
    --agent=*)           AGENT="${arg#*=}" ;;
    --artifact=*)        ARTIFACT="${arg#*=}" ;;
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

# ──────────────────────────────────────────────────────────
# Utilities
# ──────────────────────────────────────────────────────────
log() { echo "[$(date '+%H:%M:%S')] $*"; }
divider() { echo ""; echo "════════════════════════════════════════════════════════════"; }

USAGE_SCRIPT="$SPECULA_ROOT/scripts/exp/usage.sh"
QUOTA_5H="${QUOTA_5H:-85}"
QUOTA_7D="${QUOTA_7D:-95}"
QUOTA_MAX_WAITS="${QUOTA_MAX_WAITS:-6}"

wait_for_quota() {
  [[ ! -f "$USAGE_SCRIPT" ]] && return 0
  local waits=0
  while true; do
    local usage_json
    usage_json="$(bash "$USAGE_SCRIPT" 2>/dev/null)" || { log "WARN: usage fetch failed, proceeding"; return 0; }
    local check
    check="$(python3 -c "
import json, sys
d = json.loads('''$usage_json''')
five = d.get('five_hour') or {}
seven = d.get('seven_day') or {}
u5 = five.get('utilization', 0) or 0
u7 = seven.get('utilization', 0) or 0
if u5 > $QUOTA_5H:
    print(f'5h={u5}% (limit $QUOTA_5H%) resets_at={five.get(\"resets_at\",\"\")}')
elif u7 > $QUOTA_7D:
    print(f'7d={u7}% (limit $QUOTA_7D%) resets_at={seven.get(\"resets_at\",\"\")}')
else:
    print('ok')
" 2>/dev/null)" || { log "WARN: usage parse failed, proceeding"; return 0; }
    [[ "$check" == "ok" ]] && return 0
    waits=$((waits + 1))
    if (( waits > QUOTA_MAX_WAITS )); then
      log "ERROR: quota still over limit after $QUOTA_MAX_WAITS waits, aborting"
      exit 1
    fi
    local reset_at
    reset_at="$(echo "$check" | grep -oP 'resets_at=\K\S+' | head -1)"
    if [[ -n "$reset_at" ]]; then
      local sleep_secs=$(( $(date -d "$reset_at" +%s) - $(date +%s) + 120 ))
      (( sleep_secs < 60 )) && sleep_secs=60
      log "Quota: $check — sleeping ${sleep_secs}s (wait $waits/$QUOTA_MAX_WAITS)"
    else
      local sleep_secs=600
      log "Quota: $check — sleeping ${sleep_secs}s (wait $waits/$QUOTA_MAX_WAITS)"
    fi
    sleep "$sleep_secs"
  done
}

extract_names() {
  local names=()
  for target in "${TARGETS[@]}"; do
    IFS='|' read -r name _ _ _ <<< "$target"
    names+=("$(echo "$name" | xargs)")
  done
  echo "${names[@]}"
}

validate_agent_adapter() {
  local adapter="${SCRIPT_DIR}/adapters/${AGENT}.sh"
  if [[ ! -f "$adapter" ]]; then
    echo "ERROR: Unknown agent '${AGENT}' — adapter not found at ${adapter}" >&2
    exit 1
  fi
}

# ──────────────────────────────────────────────────────────
# Work directory helper
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
# Phase runners
# ──────────────────────────────────────────────────────────

run_phase1_analysis() {
  divider
  log "PHASE 1: CODE ANALYSIS"
  divider

  local analysis_args=("--max-parallel=$MAX_PARALLEL" "--max-turns=$MAX_TURNS" "--agent=$AGENT")
  [[ -n "$ARTIFACT" ]] && analysis_args+=("--artifact=$ARTIFACT")
  for target in "${TARGETS[@]}"; do
    analysis_args+=("$target")
  done

  if $DRY_RUN; then
    log "[DRY RUN] bash scripts/launch/launch_code_analysis.sh ${analysis_args[*]}"
    return 0
  fi

  bash "$SCRIPT_DIR/launch_code_analysis.sh" "${analysis_args[@]}"
}

run_review() {
  local phase="$1"
  shift
  local names=("$@")

  if $SKIP_REVIEWS; then
    log "Skipping ${phase} review (--skip-reviews)"
    return 0
  fi

  divider
  log "REVIEW: ${phase}"
  divider

  if $DRY_RUN; then
    log "[DRY RUN] bash scripts/launch/launch_review.sh --agent=$AGENT ${phase} ${names[*]}"
    return 0
  fi

  bash "$SCRIPT_DIR/launch_review.sh" "--agent=$AGENT" "$phase" "${names[@]}"
}

run_phase2_specgen() {
  divider
  log "PHASE 2: SPEC GENERATION"
  divider

  local names
  read -ra names <<< "$(extract_names)"

  local specgen_args=("--max-parallel=$MAX_PARALLEL" "--max-turns=$MAX_TURNS" "--agent=$AGENT")
  [[ -n "$ARTIFACT" ]] && specgen_args+=("--artifact=$ARTIFACT")
  for n in "${names[@]}"; do
    specgen_args+=("$n")
  done

  if $DRY_RUN; then
    log "[DRY RUN] bash scripts/launch/launch_spec_generation.sh ${specgen_args[*]}"
    return 0
  fi

  bash "$SCRIPT_DIR/launch_spec_generation.sh" "${specgen_args[@]}"
}

run_phase2_5_harness() {
  divider
  log "PHASE 2.5: HARNESS GENERATION (instrumentation + trace collection)"
  divider

  local names
  read -ra names <<< "$(extract_names)"

  local harness_args=("--max-parallel=$MAX_PARALLEL" "--max-turns=$MAX_TURNS" "--agent=$AGENT")
  [[ -n "$ARTIFACT" ]] && harness_args+=("--artifact=$ARTIFACT")
  for n in "${names[@]}"; do
    harness_args+=("$n")
  done

  if $DRY_RUN; then
    log "[DRY RUN] bash scripts/launch/launch_harness_generation.sh ${harness_args[*]}"
    return 0
  fi

  bash "$SCRIPT_DIR/launch_harness_generation.sh" "${harness_args[@]}"
}

run_phase3_validation() {
  divider
  log "PHASE 3: SPEC VALIDATION (trace validation + invariant checking + bug hunting)"
  divider

  local names
  read -ra names <<< "$(extract_names)"

  local val_args=("--max-parallel=$MAX_PARALLEL" "--max-turns=$MAX_TURNS" "--agent=$AGENT")
  [[ -n "$ARTIFACT" ]] && val_args+=("--artifact=$ARTIFACT")
  for n in "${names[@]}"; do
    val_args+=("$n")
  done

  if $DRY_RUN; then
    log "[DRY RUN] bash scripts/launch/launch_spec_validation.sh ${val_args[*]}"
    return 0
  fi

  bash "$SCRIPT_DIR/launch_spec_validation.sh" "${val_args[@]}"
}

run_phase4_confirmation() {
  divider
  log "PHASE 4: BUG CONFIRMATION (consolidate + reproduce)"
  divider

  local names
  read -ra names <<< "$(extract_names)"

  local confirm_args=("--max-parallel=$MAX_PARALLEL" "--max-turns=$MAX_TURNS" "--agent=$AGENT")
  [[ -n "$ARTIFACT" ]] && confirm_args+=("--artifact=$ARTIFACT")
  for n in "${names[@]}"; do
    confirm_args+=("$n")
  done

  if $DRY_RUN; then
    log "[DRY RUN] bash scripts/launch/launch_bug_confirmation.sh ${confirm_args[*]}"
    return 0
  fi

  bash "$SCRIPT_DIR/launch_bug_confirmation.sh" "${confirm_args[@]}"
}

# ──────────────────────────────────────────────────────────
# Generate final summary
# ──────────────────────────────────────────────────────────
generate_summary() {
  local names
  read -ra names <<< "$(extract_names)"

  divider
  log "PIPELINE SUMMARY"
  divider

  local summary_file="$PWD/.specula-output/pipeline-summary.md"
  mkdir -p "$PWD/.specula-output"
  {
    echo "# Specula Pipeline Summary"
    echo ""
    echo "Generated: $(date -Iseconds)"
    echo ""
    echo "## Systems Processed"
    echo ""

    for name in "${names[@]}"; do
      local work_dir="$(get_work_dir "$name")"
      local spec_dir="${work_dir}/spec"

      echo "### ${name}"
      echo ""

      # Phase 1 status
      if [[ -f "${work_dir}/modeling-brief.md" ]]; then
        local brief_lines
        brief_lines=$(wc -l < "${work_dir}/modeling-brief.md")
        echo "- **Phase 1 (Analysis)**: OK (modeling-brief: ${brief_lines} lines)"
      else
        echo "- **Phase 1 (Analysis)**: MISSING"
      fi

      # Phase 1 review
      if [[ -f "${work_dir}/review-analysis.md" ]]; then
        local verdict
        verdict=$(grep -i "verdict:" "${work_dir}/review-analysis.md" | tail -1)
        verdict="${verdict:-UNKNOWN}"
        echo "- **Analysis Review**: ${verdict}"
      else
        echo "- **Analysis Review**: SKIPPED"
      fi

      # Phase 2 status
      local spec_count=0
      for f in base.tla MC.tla Trace.tla instrumentation-spec.md; do
        [[ -f "${spec_dir}/${f}" ]] && spec_count=$((spec_count + 1))
      done
      if [[ $spec_count -eq 4 ]]; then
        local base_lines
        base_lines=$(wc -l < "${spec_dir}/base.tla")
        echo "- **Phase 2 (Spec Gen)**: OK (${spec_count}/4 files, base: ${base_lines} lines)"
      elif [[ $spec_count -gt 0 ]]; then
        echo "- **Phase 2 (Spec Gen)**: INCOMPLETE (${spec_count}/4 files)"
      else
        echo "- **Phase 2 (Spec Gen)**: MISSING"
      fi

      # Phase 2 review
      if [[ -f "${spec_dir}/review-specgen.md" ]]; then
        local verdict
        verdict=$(grep -i "verdict:" "${spec_dir}/review-specgen.md" | tail -1)
        verdict="${verdict:-UNKNOWN}"
        echo "- **Spec Gen Review**: ${verdict}"
      else
        echo "- **Spec Gen Review**: SKIPPED"
      fi

      # Phase 2.5 status
      local harness_dir="${work_dir}/harness"
      local traces_dir="${work_dir}/traces"
      if [[ -f "${harness_dir}/run.sh" ]]; then
        local trace_count=0
        [[ -d "$traces_dir" ]] && trace_count=$(find "$traces_dir" -name "*.ndjson" 2>/dev/null | wc -l)
        local instr_guide="no"
        [[ -f "${harness_dir}/INSTRUMENTATION.md" ]] && instr_guide="yes"
        echo "- **Phase 2.5 (Harness)**: OK (traces: ${trace_count}, INSTRUMENTATION.md: ${instr_guide})"
      elif [[ -d "$harness_dir" ]]; then
        echo "- **Phase 2.5 (Harness)**: INCOMPLETE (harness/ exists but no run.sh)"
      else
        echo "- **Phase 2.5 (Harness)**: MISSING"
      fi

      # Phase 3 status
      if [[ -f "${spec_dir}/changelog.md" ]]; then
        local result
        result=$(grep -i "^## Result" -A1 "${spec_dir}/changelog.md" | tail -1)
        result="${result:-in progress (no result yet)}"
        echo "- **Phase 3 (Validation)**: ${result}"
      else
        echo "- **Phase 3 (Validation)**: SKIPPED"
      fi

      # Phase 3 review
      if [[ -f "${spec_dir}/review-validation.md" ]]; then
        local verdict
        verdict=$(grep -i "verdict:" "${spec_dir}/review-validation.md" | tail -1)
        verdict="${verdict:-UNKNOWN}"
        echo "- **Validation Review**: ${verdict}"
      else
        echo "- **Validation Review**: SKIPPED"
      fi

      echo ""

      # List all logs
      echo "**Logs:**"
      for log_file in \
        "${work_dir}/agent.log" \
        "${work_dir}/review-analysis.log" \
        "${work_dir}/spec-gen.log" \
        "${spec_dir}/review-specgen.log" \
        "${spec_dir}/quick-mc.log" \
        "${spec_dir}/review-validation.log"; do
        if [[ -f "$log_file" ]]; then
          local size
          size=$(du -h "$log_file" | cut -f1)
          echo "- \`${log_file#$PWD/}\` (${size})"
        fi
      done
      echo ""
    done
  } > "$summary_file"

  cat "$summary_file"
  echo ""
  log "Summary written to: ${summary_file}"
}

# ──────────────────────────────────────────────────────────
# Main
# ──────────────────────────────────────────────────────────
main() {
  echo "╔══════════════════════════════════════════════════════════╗"
  echo "║        Specula — Full Pipeline Runner                   ║"
  echo "╚══════════════════════════════════════════════════════════╝"
  echo ""
  echo "Targets:      ${#TARGETS[@]}"
  echo "Max parallel: $MAX_PARALLEL"
  echo "Max turns:    $MAX_TURNS"
  echo ""
  echo "Skip phases:  analysis=$SKIP_ANALYSIS specgen=$SKIP_SPECGEN harness=$SKIP_HARNESS validation=$SKIP_VALIDATION confirmation=$SKIP_CONFIRMATION reviews=$SKIP_REVIEWS"
  echo ""

  validate_agent_adapter

  local names
  read -ra names <<< "$(extract_names)"

  local start_time
  start_time=$(date +%s)

  # ── Phase 1: Code Analysis ──
  if ! $SKIP_ANALYSIS; then
    wait_for_quota
    run_phase1_analysis
    run_review "analysis" "${names[@]}"
  else
    log "Skipping Phase 1 (--skip-analysis)"
  fi

  # ── Phase 2: Spec Generation ──
  if ! $SKIP_SPECGEN; then
    wait_for_quota
    run_phase2_specgen
    run_review "specgen" "${names[@]}"
  else
    log "Skipping Phase 2 (--skip-specgen)"
  fi

  # ── Phase 2.5: Harness Generation ──
  if ! $SKIP_HARNESS; then
    wait_for_quota
    run_phase2_5_harness
  else
    log "Skipping Phase 2.5 (--skip-harness)"
  fi

  # ── Phase 3: Spec Validation (iterative trace validation + MC) ──
  if ! $SKIP_VALIDATION; then
    wait_for_quota
    run_phase3_validation
    run_review "validation" "${names[@]}"
  else
    log "Skipping Phase 3 (--skip-validation)"
  fi

  # ── Phase 4: Bug Confirmation (consolidate MC + code review, reproduce) ──
  if ! $SKIP_CONFIRMATION; then
    wait_for_quota
    run_phase4_confirmation
  else
    log "Skipping Phase 4 (--skip-confirmation)"
  fi

  # ── Summary ──
  generate_summary

  local end_time
  end_time=$(date +%s)
  local elapsed=$(( end_time - start_time ))
  local mins=$(( elapsed / 60 ))
  local secs=$(( elapsed % 60 ))

  echo ""
  log "Pipeline completed in ${mins}m ${secs}s"
}

mkdir -p "$PWD/.specula-output"
main 2>&1 | tee "$PWD/.specula-output/pipeline.log"
