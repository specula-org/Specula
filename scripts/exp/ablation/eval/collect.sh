#!/usr/bin/env bash
#
# Collect and compare results across ablation experiment runs.
#
# Scans a run directory, extracts metrics from each config×target,
# and outputs a comparison table.
#
# Usage:
#   bash scripts/exp/ablation/eval/collect.sh <run_id>
#   bash scripts/exp/ablation/eval/collect.sh <run_id> --format csv
#   bash scripts/exp/ablation/eval/collect.sh <run_id> --format json
#
# Options:
#   --format FMT    Output format: table (default), csv, json
#   --eval          Run SANY + TLC checks (not just file existence)
#   --help          Show this help

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ABLATION_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
SPECULA_ROOT="$(cd "$ABLATION_DIR/../../.." && pwd)"
RESULTS_DIR="$ABLATION_DIR/results"

TLA2TOOLS="$SPECULA_ROOT/lib/tla2tools.jar"
COMMUNITY="$SPECULA_ROOT/lib/CommunityModules-deps.jar"

FORMAT="table"
DO_EVAL=false
RUN_ID=""

while [[ $# -gt 0 ]]; do
  case "$1" in
    --format)  FORMAT="$2"; shift 2 ;;
    --format=*) FORMAT="${1#*=}"; shift ;;
    --eval)    DO_EVAL=true; shift ;;
    -h|--help) sed -n '2,/^$/{ s/^# //; s/^#//; p }' "$0"; exit 0 ;;
    -*)        echo "Unknown option: $1" >&2; exit 1 ;;
    *)         RUN_ID="$1"; shift ;;
  esac
done

[[ -n "$RUN_ID" ]] || { echo "Usage: $0 <run_id> [--format table|csv|json] [--eval]" >&2; exit 1; }

RUN_DIR="$RESULTS_DIR/$RUN_ID"
[[ -d "$RUN_DIR" ]] || { echo "Run directory not found: $RUN_DIR" >&2; exit 1; }

# ── Metric extraction ──

check_file_exists() { [[ -f "$1" ]] && echo "yes" || echo "no"; }

count_lines() { [[ -f "$1" ]] && wc -l < "$1" || echo "0"; }

check_sany() {
  local spec_dir="$1"
  local target="MC.tla"
  [[ -f "$spec_dir/$target" ]] || target="base.tla"
  [[ -f "$spec_dir/$target" ]] || { echo "skip"; return; }

  if (cd "$spec_dir" && java -cp "$TLA2TOOLS:$COMMUNITY" tla2sany.SANY "$target" > /dev/null 2>&1); then
    echo "pass"
  else
    echo "fail"
  fi
}

check_tlc() {
  local spec_dir="$1"
  local spec="MC.tla"
  local cfg="MC.cfg"
  [[ -f "$spec_dir/$spec" && -f "$spec_dir/$cfg" ]] || { echo "skip"; return; }

  local output
  output=$(cd "$spec_dir" && timeout 60 java -cp "$TLA2TOOLS:$COMMUNITY" \
    tlc2.TLC "$spec" -config "$cfg" -workers auto -deadlock \
    -simulate num=100 2>&1) || true

  if echo "$output" | grep -q "Error:"; then
    echo "error"
  elif echo "$output" | grep -q "Finished"; then
    echo "pass"
  else
    echo "timeout"
  fi
}

count_bugs() {
  local report="$1/spec/bug-report.md"
  [[ -f "$report" ]] || { echo "0"; return; }
  # Count lines starting with "- Bug" or "## Bug" or containing "confirmed"
  grep -ciE '(confirmed|bug\s+(#|DA-|found))' "$report" 2>/dev/null || echo "0"
}

# ── Collect all results ──

declare -a ROWS=()

for config_dir in "$RUN_DIR"/*/; do
  [[ -d "$config_dir" ]] || continue
  config_name="$(basename "$config_dir")"
  [[ "$config_name" == .* ]] && continue

  for target_dir in "$config_dir"/*/; do
    [[ -d "$target_dir" ]] || continue
    target_name="$(basename "$target_dir")"

    # Read metadata
    local_group="" local_elapsed="" local_exit=""
    if [[ -f "$target_dir/meta.json" ]]; then
      local_group=$(python3 -c "import json; d=json.load(open('$target_dir/meta.json')); print(d.get('group',''))" 2>/dev/null || echo "")
      local_elapsed=$(python3 -c "import json; d=json.load(open('$target_dir/meta.json')); print(d.get('elapsed_seconds',''))" 2>/dev/null || echo "")
      local_exit=$(python3 -c "import json; d=json.load(open('$target_dir/meta.json')); print(d.get('exit_code',''))" 2>/dev/null || echo "")
    fi

    # File existence checks
    has_brief=$(check_file_exists "$target_dir/modeling-brief.md")
    has_base=$(check_file_exists "$target_dir/spec/base.tla")
    has_mc=$(check_file_exists "$target_dir/spec/MC.tla")
    has_trace=$(check_file_exists "$target_dir/spec/Trace.tla")
    has_report=$(check_file_exists "$target_dir/spec/bug-report.md")
    base_lines=$(count_lines "$target_dir/spec/base.tla")
    bug_count=$(count_bugs "$target_dir")

    # Optional evaluation
    sany_result="n/a"
    tlc_result="n/a"
    if $DO_EVAL; then
      sany_result=$(check_sany "$target_dir/spec")
      if [[ "$sany_result" == "pass" ]]; then
        tlc_result=$(check_tlc "$target_dir/spec")
      fi
    fi

    ROWS+=("${config_name}|${target_name}|${local_group}|${has_brief}|${has_base}|${has_mc}|${has_trace}|${base_lines}|${sany_result}|${tlc_result}|${bug_count}|${has_report}|${local_elapsed}|${local_exit}")
  done
done

# ── Output ──

HEADER="config|target|group|brief|base.tla|MC.tla|Trace.tla|base_loc|sany|tlc|bugs|report|elapsed_s|exit"

case "$FORMAT" in
  csv)
    echo "$HEADER"
    for row in "${ROWS[@]}"; do echo "$row"; done
    ;;

  json)
    python3 -c "
import sys, json
header = '$HEADER'.split('|')
rows = []
for line in sys.stdin:
    line = line.strip()
    if not line: continue
    vals = line.split('|')
    rows.append(dict(zip(header, vals)))
json.dump({'run_id': '$RUN_ID', 'results': rows}, sys.stdout, indent=2)
print()
" <<< "$(printf '%s\n' "${ROWS[@]}")"
    ;;

  table|*)
    # Print aligned table
    {
      echo "$HEADER"
      for row in "${ROWS[@]}"; do echo "$row"; done
    } | column -t -s'|'
    ;;
esac
