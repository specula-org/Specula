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
#   --skip-confirmation    Skip Phase 4a bug confirmation
#   --skip-classification  Skip Phase 4b severity classification
#   --skip-repair-loop     Skip the confirmation back-edge repair loop (default: enabled)
#   --max-repair-rounds=N  Per-request repair cap, enforced by re-check (default: 0 = unlimited)
#   --enable-reviews        Enable review steps (disabled by default)
#   --max-parallel=N       Max concurrent agents per phase (default: 1)
#   --max-turns=N          Max agent turns (default: 0 = unlimited)
#   --agent=NAME           Agent adapter to use (default: claude-code; e.g., claude-code, codex, copilot-cli)
#   --claude-alias=NAME    Claude CLI profile (default: claude)
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
SKIP_CLASSIFICATION=false
SKIP_REPAIR_LOOP=false
MAX_REPAIR_ROUNDS="${MAX_REPAIR_ROUNDS:-0}"   # 0 = unlimited (terminates on convergence or budget)
SKIP_REVIEWS=true
AGENT="claude-code"
CLAUDE_ALIAS="${CLAUDE_ALIAS:-claude}"
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
    --skip-classification) SKIP_CLASSIFICATION=true ;;
    --skip-repair-loop)  SKIP_REPAIR_LOOP=true ;;
    --max-repair-rounds=*) MAX_REPAIR_ROUNDS="${arg#*=}" ;;
    --enable-reviews)    SKIP_REVIEWS=false ;;
    --max-parallel=*)    MAX_PARALLEL="${arg#*=}" ;;
    --max-turns=*)       MAX_TURNS="${arg#*=}" ;;
    --agent=*)           AGENT="${arg#*=}" ;;
    --claude-alias=*)    CLAUDE_ALIAS="${arg#*=}" ;;
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
    usage_json="$(CLAUDE_ALIAS="$CLAUDE_ALIAS" bash "$USAGE_SCRIPT" 2>/dev/null)" || { log "WARN: usage fetch failed, proceeding"; return 0; }
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
# Repair-loop helpers (confirmation back-edge)
#
# Repair requests live at <work_dir>/spec/repair-requests/RR-*.md.
# Their frontmatter `status:` is the single source of truth. See
# .claude/skills/bug-confirmation/references/repair-request-format.md.
# ──────────────────────────────────────────────────────────
repair_dir() { echo "$(get_work_dir "$1")/spec/repair-requests"; }

# Read a single frontmatter field (first match in the top block) from an RR file.
rr_field() { sed -n "1,25{s/^${2}:[[:space:]]*//p}" "$1" | head -1 | sed 's/[[:space:]]*$//'; }
rr_status() { rr_field "$1" status | tr -d '[:space:]'; }

# Set status + append a History bullet, atomically (read-modify-write one file).
rr_set_status() {
  python3 - "$1" "$2" "$3" <<'PY'
import sys
path, new_status, note = sys.argv[1], sys.argv[2], sys.argv[3]
with open(path) as fh:
    lines = fh.readlines()
for i, ln in enumerate(lines[:25]):
    if ln.startswith('status:'):
        lines[i] = f'status: {new_status}\n'
        break
if lines and not lines[-1].endswith('\n'):
    lines[-1] += '\n'
lines.append(f'- {note}\n')
with open(path, 'w') as fh:
    fh.writelines(lines)
PY
}

# True if any target has at least one RR file.
has_any_request() {
  local names; read -ra names <<< "$(extract_names)"
  local n d
  for n in "${names[@]}"; do
    d="$(repair_dir "$n")"
    [[ -d "$d" ]] && compgen -G "${d}/RR-*.md" > /dev/null 2>&1 && return 0
  done
  return 1
}

# True if any target has an RR that is not yet terminal (anything other than
# RESOLVED / DEFERRED). Repair handles OPEN/REOPENED, re-check handles RECHECK;
# reset_stale_in_repair recovers IN_REPAIR. The loop runs until none remain.
repair_work_remaining() {
  local names; read -ra names <<< "$(extract_names)"
  local n d f st
  for n in "${names[@]}"; do
    d="$(repair_dir "$n")"
    [[ -d "$d" ]] || continue
    for f in "$d"/RR-*.md; do
      [[ -e "$f" ]] || continue
      st="$(rr_status "$f")"
      [[ "$st" != "RESOLVED" && "$st" != "DEFERRED" ]] && return 0
    done
  done
  return 1
}

# Stable signature of every request's (id, status, round). A round that leaves
# this unchanged made no progress — stop, rather than spin (covers --dry-run and
# a misbehaving agent that never transitions a request).
repair_state_sig() {
  local names; read -ra names <<< "$(extract_names)"
  local n d f
  for n in "${names[@]}"; do
    d="$(repair_dir "$n")"
    [[ -d "$d" ]] || continue
    for f in "$d"/RR-*.md; do
      [[ -e "$f" ]] || continue
      echo "$(basename "$f"):$(rr_status "$f"):$(rr_field "$f" round)"
    done
  done
}

# Crash recovery: a request stuck IN_REPAIR means its repair phase died
# mid-turn. Reset to OPEN so the next round retries it.
reset_stale_in_repair() {
  $DRY_RUN && return 0
  local names; read -ra names <<< "$(extract_names)"
  local n d f
  for n in "${names[@]}"; do
    d="$(repair_dir "$n")"
    [[ -d "$d" ]] || continue
    for f in "$d"/RR-*.md; do
      [[ -e "$f" ]] || continue
      if [[ "$(rr_status "$f")" == "IN_REPAIR" ]]; then
        rr_set_status "$f" "OPEN" "reset (orchestrator): repair phase did not complete; retrying"
        log "  reset $(basename "$f") IN_REPAIR -> OPEN (crash recovery)"
      fi
    done
  done
}

# Regenerate the human-readable rollup index per target.
regenerate_ledger() {
  $DRY_RUN && return 0
  local names; read -ra names <<< "$(extract_names)"
  local n d f ledger
  for n in "${names[@]}"; do
    d="$(repair_dir "$n")"
    [[ -d "$d" ]] || continue
    compgen -G "${d}/RR-*.md" > /dev/null 2>&1 || continue
    ledger="$(get_work_dir "$n")/spec/repair-ledger.md"
    {
      echo "# Repair Ledger — ${n}"
      echo ""
      echo "Updated: $(date -Iseconds)"
      echo ""
      echo "| Request | Bug | Target | Status | Round |"
      echo "|---------|-----|--------|--------|-------|"
      for f in "$d"/RR-*.md; do
        [[ -e "$f" ]] || continue
        echo "| $(rr_field "$f" id) | $(rr_field "$f" bug_id | sed 's/|/\\|/g') | $(rr_field "$f" target) | $(rr_status "$f") | $(rr_field "$f" round) |"
      done
    } > "$ledger"
  done
}

# ──────────────────────────────────────────────────────────
# Phase runners
# ──────────────────────────────────────────────────────────

run_phase1_analysis() {
  divider
  log "PHASE 1: CODE ANALYSIS"
  divider

  local analysis_args=("--max-parallel=$MAX_PARALLEL" "--max-turns=$MAX_TURNS" "--agent=$AGENT" "--claude-alias=$CLAUDE_ALIAS")
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
    log "[DRY RUN] bash scripts/launch/launch_review.sh --agent=$AGENT --claude-alias=$CLAUDE_ALIAS ${phase} ${names[*]}"
    return 0
  fi

  bash "$SCRIPT_DIR/launch_review.sh" "--agent=$AGENT" "--claude-alias=$CLAUDE_ALIAS" "$phase" "${names[@]}"
}

run_phase2_specgen() {
  divider
  log "PHASE 2: SPEC GENERATION"
  divider

  local names
  read -ra names <<< "$(extract_names)"

  local specgen_args=("--max-parallel=$MAX_PARALLEL" "--max-turns=$MAX_TURNS" "--agent=$AGENT" "--claude-alias=$CLAUDE_ALIAS")
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

  local harness_args=("--max-parallel=$MAX_PARALLEL" "--max-turns=$MAX_TURNS" "--agent=$AGENT" "--claude-alias=$CLAUDE_ALIAS")
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

  local val_args=("--max-parallel=$MAX_PARALLEL" "--max-turns=$MAX_TURNS" "--agent=$AGENT" "--claude-alias=$CLAUDE_ALIAS")
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

  local confirm_args=("--max-parallel=$MAX_PARALLEL" "--max-turns=$MAX_TURNS" "--agent=$AGENT" "--claude-alias=$CLAUDE_ALIAS")
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

# Phase 3 in repair mode: consume OPEN/REOPENED requests, repair the spec,
# re-validate (full trace + scoped MC), transition each request to RECHECK.
run_phase3_repair() {
  divider
  log "REPAIR ROUND ${1}: PHASE 3 (scoped spec/fault/invariant repair)"
  divider

  local names
  read -ra names <<< "$(extract_names)"

  local args=("--repair" "--max-parallel=$MAX_PARALLEL" "--max-turns=$MAX_TURNS" "--agent=$AGENT" "--claude-alias=$CLAUDE_ALIAS")
  [[ -n "$ARTIFACT" ]] && args+=("--artifact=$ARTIFACT")
  for n in "${names[@]}"; do
    args+=("$n")
  done

  if $DRY_RUN; then
    log "[DRY RUN] bash scripts/launch/launch_spec_validation.sh ${args[*]}"
    return 0
  fi

  bash "$SCRIPT_DIR/launch_spec_validation.sh" "${args[@]}"
}

# Phase 4 in re-check mode: consume RECHECK requests, settle each finding,
# transition each request to RESOLVED / REOPENED / DEFERRED (never RECHECK).
run_phase4_recheck() {
  divider
  log "REPAIR ROUND ${1}: PHASE 4 (re-check repair requests)"
  divider

  local names
  read -ra names <<< "$(extract_names)"

  # --max-repair-rounds is a PER-REQUEST cap: the re-check agent defers a
  # request once its own `round` reaches the cap (0 = unlimited). The agent,
  # not the orchestrator, writes every RESOLVED / DEFERRED back to confirmed-bugs.md.
  local args=("--recheck" "--max-repair-rounds=$MAX_REPAIR_ROUNDS" "--max-parallel=$MAX_PARALLEL" "--max-turns=$MAX_TURNS" "--agent=$AGENT" "--claude-alias=$CLAUDE_ALIAS")
  [[ -n "$ARTIFACT" ]] && args+=("--artifact=$ARTIFACT")
  for n in "${names[@]}"; do
    args+=("$n")
  done

  if $DRY_RUN; then
    log "[DRY RUN] bash scripts/launch/launch_bug_confirmation.sh ${args[*]}"
    return 0
  fi

  bash "$SCRIPT_DIR/launch_bug_confirmation.sh" "${args[@]}"
}

# Confirmation back-edge: alternate Phase 3 repair and Phase 4 re-check until
# every request is terminal (RESOLVED / DEFERRED). Budget pressure is handled by
# wait_for_quota (WAIT, like every other phase) — the loop never mass-defers on
# quota, since dumping findings to DEFERRED under throttling would be an exploitable
# weakness. DEFERRED is only ever written by the re-check agent, per finding, with
# evidence (and the per-request --max-repair-rounds cap it enforces). The
# orchestrator never edits confirmed-bugs.md.
run_repair_loop() {
  divider
  local cap_disp; cap_disp=$([[ "$MAX_REPAIR_ROUNDS" == 0 ]] && echo "unlimited" || echo "${MAX_REPAIR_ROUNDS} per request")
  log "REPAIR LOOP (confirmation back-edge) — cap=${cap_disp}"
  divider

  reset_stale_in_repair   # recover crashed IN_REPAIR from a prior run
  if ! has_any_request; then
    log "No repair requests emitted by bug confirmation — repair loop is a no-op."
    return 0
  fi

  local round=0 sig_before
  while repair_work_remaining; do
    round=$((round + 1))
    sig_before="$(repair_state_sig)"
    wait_for_quota          # budget pressure -> WAIT, never auto-defer
    run_phase3_repair "$round"
    reset_stale_in_repair   # recover if this round's repair phase died mid-turn
    wait_for_quota
    run_phase4_recheck "$round"
    regenerate_ledger
    if [[ "$(repair_state_sig)" == "$sig_before" ]]; then
      log "Repair loop made no progress in round ${round} (no request changed) — stopping to avoid spin."
      break
    fi
  done

  regenerate_ledger
  log "Repair loop ended after ${round} round(s)."
}

run_phase4b_classification() {
  divider
  log "PHASE 4b: BUG CLASSIFICATION (severity tier assignment)"
  divider

  local names
  read -ra names <<< "$(extract_names)"

  local classify_args=("--max-parallel=$MAX_PARALLEL" "--max-turns=$MAX_TURNS" "--agent=$AGENT" "--claude-alias=$CLAUDE_ALIAS")
  for n in "${names[@]}"; do
    classify_args+=("$n")
  done

  if $DRY_RUN; then
    log "[DRY RUN] bash scripts/launch/launch_bug_classification.sh ${classify_args[*]}"
    return 0
  fi

  bash "$SCRIPT_DIR/launch_bug_classification.sh" "${classify_args[@]}"
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
      if [[ -s "${work_dir}/review-analysis.md" ]]; then
        echo "- **Analysis Review**: written ($(wc -l < "${work_dir}/review-analysis.md") lines)"
      elif [[ -f "${work_dir}/review-analysis.md" ]]; then
        echo "- **Analysis Review**: empty (check log)"
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
      if [[ -s "${spec_dir}/review-specgen.md" ]]; then
        echo "- **Spec Gen Review**: written ($(wc -l < "${spec_dir}/review-specgen.md") lines)"
      elif [[ -f "${spec_dir}/review-specgen.md" ]]; then
        echo "- **Spec Gen Review**: empty (check log)"
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
      if [[ -s "${spec_dir}/changelog.md" ]]; then
        echo "- **Phase 3 (Validation)**: changelog written ($(wc -l < "${spec_dir}/changelog.md") lines)"
      elif [[ -f "${spec_dir}/changelog.md" ]]; then
        echo "- **Phase 3 (Validation)**: changelog empty (check log)"
      else
        echo "- **Phase 3 (Validation)**: SKIPPED"
      fi

      # Phase 3 review
      if [[ -s "${spec_dir}/review-validation.md" ]]; then
        echo "- **Validation Review**: written ($(wc -l < "${spec_dir}/review-validation.md") lines)"
      elif [[ -f "${spec_dir}/review-validation.md" ]]; then
        echo "- **Validation Review**: empty (check log)"
      else
        echo "- **Validation Review**: SKIPPED"
      fi

      # Phase 4a status
      if [[ -s "${spec_dir}/confirmed-bugs.md" ]]; then
        echo "- **Phase 4a (Bug Confirmation)**: confirmed-bugs.md written ($(wc -l < "${spec_dir}/confirmed-bugs.md") lines)"
      elif [[ -f "${spec_dir}/confirmed-bugs.md" ]]; then
        echo "- **Phase 4a (Bug Confirmation)**: empty (check log)"
      else
        echo "- **Phase 4a (Bug Confirmation)**: SKIPPED"
      fi

      # Repair loop status
      local rr_dir="${spec_dir}/repair-requests"
      if compgen -G "${rr_dir}/RR-*.md" > /dev/null 2>&1; then
        local rr_total rr_resolved rr_deferred
        rr_total=$(compgen -G "${rr_dir}/RR-*.md" | wc -l | tr -d ' ')
        rr_resolved=$( { grep -lE '^status:[[:space:]]*RESOLVED' "${rr_dir}"/RR-*.md 2>/dev/null || true; } | wc -l | tr -d ' ')
        rr_deferred=$( { grep -lE '^status:[[:space:]]*DEFERRED' "${rr_dir}"/RR-*.md 2>/dev/null || true; } | wc -l | tr -d ' ')
        echo "- **Repair loop**: ${rr_total} request(s) — ${rr_resolved} resolved, ${rr_deferred} deferred"
      fi

      # Phase 4b status
      if [[ -s "${spec_dir}/bug-severity.md" ]]; then
        echo "- **Phase 4b (Bug Classification)**: bug-severity.md written ($(wc -l < "${spec_dir}/bug-severity.md") lines)"
      elif [[ -f "${spec_dir}/bug-severity.md" ]]; then
        echo "- **Phase 4b (Bug Classification)**: empty (check log)"
      else
        echo "- **Phase 4b (Bug Classification)**: SKIPPED"
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
        "${spec_dir}/review-validation.log" \
        "${work_dir}/bug-confirmation.log" \
        "${work_dir}/bug-classification.log"; do
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
  echo "Agent:        $AGENT  (claude-alias=$CLAUDE_ALIAS)"
  echo ""
  echo "Skip phases:  analysis=$SKIP_ANALYSIS specgen=$SKIP_SPECGEN harness=$SKIP_HARNESS validation=$SKIP_VALIDATION confirmation=$SKIP_CONFIRMATION classification=$SKIP_CLASSIFICATION reviews=$SKIP_REVIEWS"
  echo "Repair loop:  skip=$SKIP_REPAIR_LOOP per_request_cap=$([[ "$MAX_REPAIR_ROUNDS" == 0 ]] && echo unlimited || echo "$MAX_REPAIR_ROUNDS")"
  echo ""

  validate_agent_adapter

  local names
  read -ra names <<< "$(extract_names)"

  # If running a single target, cd into its case-study directory so that
  # downstream scripts (which use $PWD/.specula-output) write into the
  # case study's own directory instead of polluting the repo root.
  if (( ${#TARGETS[@]} == 1 )); then
    local single_name="${names[0]}"
    local case_dir="${SPECULA_ROOT}/case-studies/${single_name}"
    if [[ -d "$case_dir" ]]; then
      cd "$case_dir"
      log "Single target: cd to ${case_dir}"
    fi
  fi

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

  # ── Phase 4a: Bug Confirmation (consolidate MC + code review, reproduce) ──
  if ! $SKIP_CONFIRMATION; then
    wait_for_quota
    run_phase4_confirmation
  else
    log "Skipping Phase 4a (--skip-confirmation)"
  fi

  # ── Repair loop: confirmation back-edge (spec/fault/invariant repair) ──
  if ! $SKIP_CONFIRMATION && ! $SKIP_REPAIR_LOOP; then
    run_repair_loop
  elif $SKIP_REPAIR_LOOP; then
    log "Skipping repair loop (--skip-repair-loop)"
  fi

  # ── Phase 4b: Bug Classification (severity tier assignment) ──
  if ! $SKIP_CLASSIFICATION; then
    wait_for_quota
    run_phase4b_classification
  else
    log "Skipping Phase 4b (--skip-classification)"
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
