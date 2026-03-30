#!/usr/bin/env bash
#
# Run a matrix of ablation experiments: configs × targets.
#
# Usage:
#   bash scripts/exp/ablation/run_matrix.sh [options]
#
# Options:
#   --configs "c1 c2 ..."   Config names to run (default: all)
#   --targets-file FILE     File with targets, one per line (required)
#   --max-budget N          Override max dollar budget (default: from config)
#   --max-parallel N        Max concurrent runs (default: 1)
#   --group GROUP           Only run configs from this group: ablation|baseline|all (default: all)
#   --dry-run               Print matrix without executing
#   --help                  Show this help
#
# Targets file format (one per line, # comments allowed):
#   name|github|lang|reference
#
# Example:
#   bash scripts/exp/ablation/run_matrix.sh \
#     --targets-file targets.txt \
#     --configs "full no-code-analysis bare-llm" \
#     --max-budget 5 \
#     --max-parallel 2

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$SCRIPT_DIR/lib/common.sh"

# ── Parse arguments ──

CONFIGS_FILTER=""
TARGETS_FILE=""
MAX_BUDGET_CLI=""
MAX_PARALLEL=1
GROUP_FILTER="all"
DRY_RUN=false

while [[ $# -gt 0 ]]; do
  case "$1" in
    --configs)       CONFIGS_FILTER="$2"; shift 2 ;;
    --configs=*)     CONFIGS_FILTER="${1#*=}"; shift ;;
    --targets-file)  TARGETS_FILE="$2"; shift 2 ;;
    --targets-file=*) TARGETS_FILE="${1#*=}"; shift ;;
    --max-budget)    MAX_BUDGET_CLI="$2"; shift 2 ;;
    --max-budget=*)  MAX_BUDGET_CLI="${1#*=}"; shift ;;
    --max-parallel)  MAX_PARALLEL="$2"; shift 2 ;;
    --max-parallel=*) MAX_PARALLEL="${1#*=}"; shift ;;
    --group)         GROUP_FILTER="$2"; shift 2 ;;
    --group=*)       GROUP_FILTER="${1#*=}"; shift ;;
    --dry-run)       DRY_RUN=true; shift ;;
    -h|--help)       sed -n '2,/^$/{ s/^# //; s/^#//; p }' "$0"; exit 0 ;;
    *)               die "Unknown option: $1" ;;
  esac
done

[[ -n "$TARGETS_FILE" ]] || die "Missing --targets-file"
[[ -f "$TARGETS_FILE" ]] || die "Targets file not found: $TARGETS_FILE"

# ── Discover configs ──

CONFIGS=()

if [[ -n "$CONFIGS_FILTER" ]]; then
  for name in $CONFIGS_FILTER; do
    local_cfg="$SCRIPT_DIR/configs/${name}.sh"
    [[ -f "$local_cfg" ]] || die "Config not found: $local_cfg"
    CONFIGS+=("$local_cfg")
  done
else
  for cfg in "$SCRIPT_DIR"/configs/*.sh; do
    [[ "$(basename "$cfg")" == _*.sh ]] && continue
    CONFIGS+=("$cfg")
  done
fi

# ── Filter by group ──

if [[ "$GROUP_FILTER" != "all" ]]; then
  FILTERED=()
  for cfg in "${CONFIGS[@]}"; do
    source "$SCRIPT_DIR/configs/_defaults.sh"
    source "$cfg"
    if [[ "$ABLATION_GROUP" == "$GROUP_FILTER" ]]; then
      FILTERED+=("$cfg")
    fi
  done
  CONFIGS=("${FILTERED[@]}")
fi

# ── Load targets ──

TARGETS=()
while IFS= read -r line; do
  [[ -z "${line// /}" || "$line" =~ ^[[:space:]]*# ]] && continue
  TARGETS+=("$line")
done < "$TARGETS_FILE"

(( ${#CONFIGS[@]} > 0 )) || die "No configs selected"
(( ${#TARGETS[@]} > 0 )) || die "No targets loaded from $TARGETS_FILE"

# ── Plan matrix ──

RUN_ID="$(date +%Y%m%d_%H%M%S)"
TOTAL=$(( ${#CONFIGS[@]} * ${#TARGETS[@]} ))

log "══════════════════════════════════════════"
log "Ablation Matrix Experiment"
log "══════════════════════════════════════════"
log "Run ID:       $RUN_ID"
log "Configs:      ${#CONFIGS[@]}"
log "Targets:      ${#TARGETS[@]}"
log "Total runs:   $TOTAL"
log "Max parallel: $MAX_PARALLEL"
log ""

log "Configs:"
for cfg in "${CONFIGS[@]}"; do
  source "$SCRIPT_DIR/configs/_defaults.sh"
  source "$cfg"
  log "  [$ABLATION_GROUP] $ABLATION_ID — $ABLATION_DESC"
done

log ""
log "Targets:"
for t in "${TARGETS[@]}"; do
  IFS='|' read -r n _ _ _ <<< "$t"
  log "  $n"
done
log ""

if $DRY_RUN; then
  log "[DRY RUN] Would run $TOTAL experiments. Exiting."
  exit 0
fi

# ── Execute matrix ──

COMPLETED=0
FAILED=0
PIDS=()
PID_LABELS=()

run_one() {
  local cfg="$1" target="$2"
  local cfg_name
  cfg_name="$(basename "$cfg" .sh)"
  IFS='|' read -r tname _ _ _ <<< "$target"

  local run_args=(
    --config "$cfg"
    --target "$target"
    --run-id "$RUN_ID"
  )
  [[ -n "$MAX_BUDGET_CLI" ]] && run_args+=(--max-budget "$MAX_BUDGET_CLI")

  log "LAUNCH [$cfg_name × $tname]"
  bash "$SCRIPT_DIR/run.sh" "${run_args[@]}" \
    > "$RESULTS_BASE_DIR/$RUN_ID/.log_${cfg_name}_${tname}" 2>&1
}

for cfg in "${CONFIGS[@]}"; do
  for target in "${TARGETS[@]}"; do
    # Throttle to MAX_PARALLEL
    while (( ${#PIDS[@]} >= MAX_PARALLEL )); do
      new_pids=(); new_labels=()
      for i in "${!PIDS[@]}"; do
        if kill -0 "${PIDS[$i]}" 2>/dev/null; then
          new_pids+=("${PIDS[$i]}")
          new_labels+=("${PID_LABELS[$i]}")
        else
          wait "${PIDS[$i]}" 2>/dev/null && COMPLETED=$((COMPLETED+1)) || FAILED=$((FAILED+1))
          log "DONE  ${PID_LABELS[$i]}"
        fi
      done
      PIDS=("${new_pids[@]+"${new_pids[@]}"}")
      PID_LABELS=("${new_labels[@]+"${new_labels[@]}"}")
      (( ${#PIDS[@]} >= MAX_PARALLEL )) && sleep 10
    done

    cfg_name="$(basename "$cfg" .sh)"
    IFS='|' read -r tname _ _ _ <<< "$target"

    mkdir -p "$RESULTS_BASE_DIR/$RUN_ID"
    run_one "$cfg" "$target" &
    PIDS+=($!)
    PID_LABELS+=("$cfg_name × $tname")
  done
done

# Drain remaining
for i in "${!PIDS[@]}"; do
  wait "${PIDS[$i]}" 2>/dev/null && COMPLETED=$((COMPLETED+1)) || FAILED=$((FAILED+1))
  log "DONE  ${PID_LABELS[$i]}"
done

# ── Summary ──

log "══════════════════════════════════════════"
log "MATRIX COMPLETE"
log "  Total:     $TOTAL"
log "  Completed: $COMPLETED"
log "  Failed:    $FAILED"
log "  Results:   $RESULTS_BASE_DIR/$RUN_ID/"
log "══════════════════════════════════════════"
