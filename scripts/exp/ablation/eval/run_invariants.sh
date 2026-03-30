#!/usr/bin/env bash
#
# Evaluate invariant correctness for ablation experiment specs.
# Step 1: Concretize invariant templates to spec variable names (via claude CLI)
# Step 2: Run TLC to check each invariant
#
# Usage:
#   bash scripts/exp/ablation/eval/run_invariants.sh              # all 18 specs
#   bash scripts/exp/ablation/eval/run_invariants.sh agent-basic libgomp  # one spec

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SPECULA_ROOT="$(cd "$SCRIPT_DIR/../../../.." && pwd)"
RESULTS="$SCRIPT_DIR/../results"
TEMPLATES="$SPECULA_ROOT/tools/SysMoBench/data/invariant_templates"
TLA2TOOLS="$SPECULA_ROOT/lib/tla2tools.jar"
COMMUNITY="$SPECULA_ROOT/lib/CommunityModules-deps.jar"

declare -A TEMPLATE_MAP=([etcd-raft]=etcd [autobahn]=autobahn [libgomp]=libgomp)
declare -A RUN_MAP=(
  [full]=20260321_full
  [no-code-analysis]=20260322_134701
  [no-trace-validation]=20260322_134701
  [no-bug-families]=20260322_134701
  [agent-tla-tools]=20260320_124147
  [agent-basic]=20260320_124147
)

evaluate_spec() {
  local cfg="$1" tgt="$2"
  local rid="${RUN_MAP[$cfg]}"
  local spec_dir="$RESULTS/$rid/$cfg/$tgt/spec"
  local template_dir="${TEMPLATE_MAP[$tgt]}"
  local template_file="$TEMPLATES/$template_dir/invariants.yaml"
  local inv_output="$spec_dir/_invariants.json"

  [[ -f "$spec_dir/base.tla" ]] || { echo "$cfg/$tgt: NO SPEC"; return; }
  [[ -f "$template_file" ]] || { echo "$cfg/$tgt: NO TEMPLATE"; return; }
  [[ -f "$spec_dir/MC.tla" ]] || { echo "$cfg/$tgt: NO MC"; return; }

  echo "$cfg/$tgt:"

  # Step 1: Concretize (cache result)
  if [[ ! -f "$inv_output" ]]; then
    echo "  Concretizing..."
    python3 "$SCRIPT_DIR/concretize.py" "$spec_dir/base.tla" "$template_file" "$inv_output"
  else
    local count
    count=$(python3 -c "import json; print(len(json.load(open('$inv_output'))))" 2>/dev/null || echo 0)
    echo "  Cached: $count invariants"
  fi

  [[ -f "$inv_output" ]] || { echo "  Concretization failed"; return; }

  # Step 2: Check each invariant
  local total=0 passed=0 violated=0 errors=0 skipped=0

  for inv_name in $(python3 -c "import json; [print(k) for k in json.load(open('$inv_output'))]" 2>/dev/null); do
    total=$((total + 1))
    local result
    result=$(python3 "$SCRIPT_DIR/check_invariant.py" "$spec_dir" "$inv_output" "$inv_name" "$TLA2TOOLS" "$COMMUNITY" 2>/dev/null || echo "ERROR")

    case "$result" in
      PASS) passed=$((passed + 1)) ;;
      VIOLATED) violated=$((violated + 1)); echo "  VIOLATED: $inv_name" ;;
      SKIP) skipped=$((skipped + 1)) ;;
      *) errors=$((errors + 1)); echo "  $result: $inv_name" ;;
    esac
  done

  local checked=$((total - skipped))
  local pct=0
  (( checked > 0 )) && pct=$((passed * 100 / checked))
  echo "  RESULT: $passed/$checked passed (${pct}%), $violated violated, $errors errors, $skipped skipped"
  echo ""
}

# Main
CONFIGS=(full no-code-analysis no-trace-validation no-bug-families agent-tla-tools agent-basic)
TARGETS=(etcd-raft autobahn libgomp)

if [[ $# -ge 2 ]]; then
  evaluate_spec "$1" "$2"
else
  for cfg in "${CONFIGS[@]}"; do
    for tgt in "${TARGETS[@]}"; do
      evaluate_spec "$cfg" "$tgt"
    done
  done
fi
