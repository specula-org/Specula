#!/usr/bin/env bash
#
# Run a single ablation experiment: one config × one target.
#
# Supports two modes:
#   - Single-phase: one agent call (baselines)
#   - Multi-phase: sequential agent calls, one per pipeline phase (Specula)
#
# Usage:
#   bash scripts/exp/ablation/run.sh --config configs/full.sh \
#     --target "etcd-raft|etcd-io/raft|Go|Raft (Ongaro 2014)"
#
# Options:
#   --config FILE        Config file (required)
#   --target "..."       Target in name|github|lang|reference format (required)
#   --run-id ID          Run ID (default: timestamp)
#   --max-budget N       Override max dollar budget (default: from config)
#   --dry-run            Print prompt without executing
#   --help               Show this help

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$SCRIPT_DIR/lib/common.sh"
source "$SCRIPT_DIR/lib/prompt.sh"

# ── Parse arguments ──

CONFIG_FILE=""
TARGET=""
RUN_ID="$(date +%Y%m%d_%H%M%S)"
MAX_BUDGET_CLI=""
START_PHASE=1
DRY_RUN=false

while [[ $# -gt 0 ]]; do
  case "$1" in
    --config)      CONFIG_FILE="$2"; shift 2 ;;
    --config=*)    CONFIG_FILE="${1#*=}"; shift ;;
    --target)      TARGET="$2"; shift 2 ;;
    --target=*)    TARGET="${1#*=}"; shift ;;
    --run-id)      RUN_ID="$2"; shift 2 ;;
    --run-id=*)    RUN_ID="${1#*=}"; shift ;;
    --max-budget)  MAX_BUDGET_CLI="$2"; shift 2 ;;
    --max-budget=*) MAX_BUDGET_CLI="${1#*=}"; shift ;;
    --start-phase) START_PHASE="$2"; shift 2 ;;
    --start-phase=*) START_PHASE="${1#*=}"; shift ;;
    --dry-run)     DRY_RUN=true; shift ;;
    -h|--help)     sed -n '2,/^$/{ s/^# //; s/^#//; p }' "$0"; exit 0 ;;
    *)             die "Unknown option: $1" ;;
  esac
done

[[ -n "$CONFIG_FILE" ]] || die "Missing --config"
[[ -n "$TARGET" ]]      || die "Missing --target"

# Resolve relative config path
if [[ ! "$CONFIG_FILE" =~ ^/ ]]; then
  CONFIG_FILE="$SCRIPT_DIR/$CONFIG_FILE"
fi

# ── Load config ──

load_config "$CONFIG_FILE"
[[ -n "$MAX_BUDGET_CLI" ]] && MAX_BUDGET="$MAX_BUDGET_CLI"

# ── Parse target ──

parse_target "$TARGET"

# ── Locate artifact ──

REPO_DIR="$(find_artifact_repo "$TARGET_NAME")"
[[ -n "$REPO_DIR" ]] || die "Artifact repo not found for '$TARGET_NAME'. Expected at ${CASE_STUDIES_DIR}/${TARGET_NAME}/artifact/<repo>/"

log "Config:  $ABLATION_ID ($ABLATION_GROUP)"
log "Target:  $TARGET_NAME ($TARGET_LANG, $TARGET_REFERENCE)"
log "Repo:    $REPO_DIR"
log "Run ID:  $RUN_ID"

# ── Create workspace ──

WORKSPACE_DIR="$(create_workspace "$RUN_ID" "$ABLATION_ID" "$TARGET_NAME")"
SPEC_DIR="$WORKSPACE_DIR/spec"
REPO_DIR="$(link_artifact "$WORKSPACE_DIR" "$REPO_DIR")"

log "Workspace: $WORKSPACE_DIR"

# ── Skill & tool isolation ──

init_workspace_isolation "$WORKSPACE_DIR"

# ── Resolve adapter ──

ADAPTER="$ADAPTER_DIR/${AGENT}.sh"
[[ -f "$ADAPTER" ]] || die "Agent adapter not found: $ADAPTER"

# ── Run: invoke agent(s) ──

run_single_phase() {
  local prompt_template="$1" phase_name="$2" log_prefix="$3"
  local template_path="$SCRIPT_DIR/prompts/$prompt_template"
  local rendered
  rendered="$(render_prompt "$template_path")"

  local prompt_file="$WORKSPACE_DIR/${log_prefix}.prompt.md"
  local agent_log="$WORKSPACE_DIR/${log_prefix}.log"
  echo "$rendered" > "$prompt_file"

  log "  [$phase_name] Prompt: $(wc -l < "$prompt_file") lines"

  if $DRY_RUN; then
    log "  [$phase_name] DRY RUN — skipped"
    return 0
  fi

  local phase_start
  phase_start=$(date +%s)

  local adapter_args=(
    "--prompt-file=$prompt_file"
    "--log=$agent_log"
  )
  [[ "$MAX_BUDGET" != "0" ]] && adapter_args+=("--max-budget=$MAX_BUDGET")

  local phase_timeout="${PHASE_TIMEOUT:-7200}"  # default 2 hours per phase
  local max_retries=2
  local rate_limit_retries=3
  local attempt rc
  for (( attempt=1; attempt<=max_retries; attempt++ )); do
    set +e
    (cd "$WORKSPACE_DIR" && timeout --signal=KILL "$phase_timeout" bash "$ADAPTER" "${adapter_args[@]}")
    rc=$?
    set -e

    # ── Rate limit (exit 75): wait for quota reset and retry ──
    if [[ $rc -eq 75 ]]; then
      if (( rate_limit_retries <= 0 )); then
        warn "  [$phase_name] RATE LIMITED — max retries exhausted"
        break
      fi
      rate_limit_retries=$((rate_limit_retries - 1))
      # Parse reset time from usage.json or raw.json
      local wait_secs=3600
      local reset_info
      reset_info=$(python3 -c "
import json, re, sys
try:
    with open(sys.argv[1]) as f:
        txt = f.read()
    # Look for 'resets <time>' pattern
    m = re.search(r'resets\s+(.+?)(?:\"|$)', txt)
    if m:
        print(m.group(1).strip())
except:
    pass
" "$WORKSPACE_DIR/${log_prefix}.raw.json" 2>/dev/null || true)
      if [[ -n "$reset_info" ]]; then
        local reset_epoch
        reset_epoch=$(date -d "$reset_info" +%s 2>/dev/null || echo "")
        if [[ -n "$reset_epoch" ]]; then
          local now_epoch
          now_epoch=$(date +%s)
          wait_secs=$(( reset_epoch - now_epoch + 120 ))
          (( wait_secs < 60 )) && wait_secs=60
        fi
      fi
      warn "  [$phase_name] RATE LIMITED — sleeping ${wait_secs}s (retries left: $rate_limit_retries)"
      sleep "$wait_secs"
      # Clean stale output so retry writes fresh data
      rm -f "$WORKSPACE_DIR/${log_prefix}.raw.json"
      # Don't count rate limit retries against max_retries
      attempt=$((attempt - 1))
      continue
    fi

    if [[ $rc -ne 137 ]]; then
      break
    fi
    if (( attempt < max_retries )); then
      warn "  [$phase_name] TIMEOUT (${phase_timeout}s) — retry $attempt/$max_retries"
      # Clean stale output so retry writes fresh data
      rm -f "$WORKSPACE_DIR/${log_prefix}.raw.json"
    else
      warn "  [$phase_name] TIMEOUT after $max_retries attempts — giving up"
    fi
  done

  local phase_end
  phase_end=$(date +%s)
  local phase_elapsed=$(( phase_end - phase_start ))

  # Fix duration_ms in usage.json with actual elapsed time
  local usage_json="$WORKSPACE_DIR/${log_prefix}.usage.json"
  if [[ -f "$usage_json" ]]; then
    python3 -c "
import json, sys
with open(sys.argv[1]) as f:
    d = json.load(f)
d['duration_ms_reported'] = d.get('duration_ms', 0)
d['duration_ms'] = int(sys.argv[2]) * 1000
with open(sys.argv[1], 'w') as f:
    json.dump(d, f, indent=2)
" "$usage_json" "$phase_elapsed" 2>/dev/null || true
  fi

  if [[ $rc -eq 0 ]]; then
    log "  [$phase_name] Done (${phase_elapsed}s)"
  else
    warn "  [$phase_name] Exit code $rc (${phase_elapsed}s)"
  fi

  return $rc
}

START_TS=$(date +%s)
TOTAL_EXIT=0

if $MULTI_PHASE; then
  # ── Multi-phase mode: run each phase as independent agent call ──
  log "Mode: multi-phase (${#PHASE_PROMPTS[@]} phases)"

  for i in "${!PHASE_PROMPTS[@]}"; do
    prompt_tmpl="${PHASE_PROMPTS[$i]}"
    phase_num=$((i + 1))
    phase_label="Phase ${phase_num}/${#PHASE_PROMPTS[@]}"
    log_prefix="agent.p${phase_num}"

    log "── $phase_label: $prompt_tmpl ──"

    if (( phase_num < START_PHASE )); then
      log "  [$phase_label] Skipped (--start-phase=$START_PHASE)"
      continue
    fi

    if ! run_single_phase "$prompt_tmpl" "$phase_label" "$log_prefix"; then
      warn "Phase $phase_num failed — stopping pipeline"
      TOTAL_EXIT=1
      break
    fi
  done
else
  # ── Single-phase mode: one agent call ──
  log "Mode: single-phase"

  if [[ -z "$PROMPT_TEMPLATE" ]]; then
    die "Single-phase config requires PROMPT_TEMPLATE"
  fi

  run_single_phase "$PROMPT_TEMPLATE" "single" "agent"
  TOTAL_EXIT=$?
fi

END_TS=$(date +%s)
ELAPSED=$(( END_TS - START_TS ))

# ── Aggregate usage across all phases ──

python3 -c "
import json, glob, os

ws = '$WORKSPACE_DIR'
total = {'total_cost_usd': 0, 'num_turns': 0, 'duration_ms': 0, 'phases': {}}
model_totals = {}

for uf in sorted(glob.glob(f'{ws}/*.usage.json')):
    phase = os.path.basename(uf).replace('.usage.json', '')
    try:
        d = json.load(open(uf))
        if 'error' in d: continue
        cost = d.get('total_cost_usd', 0)
        turns = d.get('num_turns', 0)
        dur = d.get('duration_ms', 0)
        total['total_cost_usd'] += cost
        total['num_turns'] += turns
        total['duration_ms'] += dur
        total['phases'][phase] = {'cost': cost, 'turns': turns, 'duration_ms': dur}

        for model, u in d.get('model_usage', {}).items():
            if model not in model_totals:
                model_totals[model] = {'inputTokens': 0, 'outputTokens': 0,
                    'cacheReadInputTokens': 0, 'cacheCreationInputTokens': 0, 'costUSD': 0}
            for k in model_totals[model]:
                model_totals[model][k] += u.get(k, 0)
    except:
        pass

total['model_usage'] = model_totals
total['elapsed_seconds'] = $ELAPSED

with open(f'{ws}/usage_total.json', 'w') as f:
    json.dump(total, f, indent=2)
" 2>/dev/null

# ── Record metadata ──

write_metadata "$WORKSPACE_DIR" \
  "config=$ABLATION_ID" \
  "group=$ABLATION_GROUP" \
  "target=$TARGET_NAME" \
  "lang=$TARGET_LANG" \
  "reference=$TARGET_REFERENCE" \
  "run_id=$RUN_ID" \
  "max_budget=$MAX_BUDGET" \
  "multi_phase=$MULTI_PHASE" \
  "num_phases=${#PHASE_PROMPTS[@]}" \
  "exit_code=$TOTAL_EXIT" \
  "elapsed_seconds=$ELAPSED" \
  "timestamp=$(date -Iseconds)"

# ── Quick output summary ──

log "── Output Summary ──"
for f in modeling-brief.md spec/base.tla spec/MC.tla spec/Trace.tla spec/bug-report.md; do
  if [[ -f "$WORKSPACE_DIR/$f" ]]; then
    local_lines=$(wc -l < "$WORKSPACE_DIR/$f")
    log "  OK   $f ($local_lines lines)"
  else
    log "  MISS $f"
  fi
done

# Show aggregated usage
if [[ -f "$WORKSPACE_DIR/usage_total.json" ]]; then
  python3 -c "
import json
d = json.load(open('$WORKSPACE_DIR/usage_total.json'))
cost = d.get('total_cost_usd', 0)
turns = d.get('num_turns', 0)
elapsed = d.get('elapsed_seconds', 0)
print(f'  Total: cost=\${cost:.2f} turns={turns} elapsed={elapsed//60}m{elapsed%60}s')
phases = d.get('phases', {})
for p, v in sorted(phases.items()):
    print(f'    {p}: \${v[\"cost\"]:.2f} ({v[\"turns\"]} turns)')
" 2>/dev/null
fi

log "Results: $WORKSPACE_DIR"
