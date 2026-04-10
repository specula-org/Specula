#!/usr/bin/env bash
# Clean up TLC working directories that pile up disk space.
#
# What it cleans (in order of safety):
#   1. Any directory named `states/` under the project (TLC default)
#   2. Any directory under the project that *contains* a TLC fingerprint
#      file (`*.fp`). This catches non-default metadirs like `meta_base/`,
#      `output/meta_*`, etc. Detection is by content, not by name, so it
#      won't accidentally match unrelated `meta_*` folders.
#   3. Stale temp metadirs in /tmp:
#         /tmp/tlc-states-*       (from run_model_check.sh)
#         /tmp/tlc_validation_*   (from trace validation MCP handler)
#         /tmp/tlc-hunt*          (manual hunting runs)
#   4. Stale metadirs in $HOME:
#         ~/tlc-states-*
#
# Usage:
#   ./clean_states.sh           # show what would be deleted, then prompt
#   ./clean_states.sh -y        # delete without prompting
#   ./clean_states.sh -n        # dry run only (list, don't delete)

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

ASSUME_YES=false
DRY_RUN=false
while getopts "ynh" opt; do
    case $opt in
        y) ASSUME_YES=true ;;
        n) DRY_RUN=true ;;
        h|*)
            echo "Usage: $0 [-y] [-n]"
            echo "  -y   delete without prompting"
            echo "  -n   dry run (list only)"
            exit 0
            ;;
    esac
done

# Collect targets into a single list, deduplicated.
declare -A SEEN
TARGETS=()

add_target() {
    local d="$1"
    [ -z "$d" ] && return
    [ ! -d "$d" ] && return
    # Resolve to canonical path so dedup works
    local rp
    rp="$(readlink -f "$d" 2>/dev/null || echo "$d")"
    if [ -z "${SEEN[$rp]:-}" ]; then
        SEEN[$rp]=1
        TARGETS+=("$rp")
    fi
}

# Paths inside the project we must NEVER touch (upstream source / test data).
EXCLUDE_PATHS=(
    "$PROJECT_ROOT/tools/tlaplus"
)

is_excluded() {
    local p="$1"
    for ex in "${EXCLUDE_PATHS[@]}"; do
        case "$p" in
            "$ex"|"$ex"/*) return 0 ;;
        esac
    done
    return 1
}

# (1) Directories literally named "states"
while IFS= read -r d; do
    is_excluded "$d" && continue
    add_target "$d"
done < <(find "$PROJECT_ROOT" -type d -name states 2>/dev/null)

# (2) Directories containing TLC fingerprint files (non-default metadirs).
#     We look for *.fp under the project, then take the parent dir.
#     The parent of a parent (e.g. meta_base/<timestamp>/MC_0.fp) is also
#     a candidate, since the TLC convention is metadir/<timestamp>/files.
while IFS= read -r fp; do
    is_excluded "$fp" && continue
    parent="$(dirname "$fp")"
    add_target "$parent"
done < <(find "$PROJECT_ROOT" -type f -name '*.fp' 2>/dev/null)

# (3) Stale /tmp metadirs
for pattern in 'tlc-states-*' 'tlc_validation_*' 'tlc-hunt*'; do
    while IFS= read -r d; do add_target "$d"; done \
        < <(find /tmp -maxdepth 1 -type d -name "$pattern" 2>/dev/null)
done

# (4) Stale $HOME metadirs
while IFS= read -r d; do add_target "$d"; done \
    < <(find "$HOME" -maxdepth 1 -type d -name 'tlc-states-*' 2>/dev/null)

if [ ${#TARGETS[@]} -eq 0 ]; then
    echo "Nothing to clean."
    exit 0
fi

# Filter: never touch anything outside known-safe roots, and never touch
# the project root itself or anything that looks like source code.
SAFE_ROOTS=("$PROJECT_ROOT" "/tmp" "$HOME")
is_safe() {
    local p="$1"
    for root in "${SAFE_ROOTS[@]}"; do
        case "$p" in
            "$root"/*) return 0 ;;
        esac
    done
    return 1
}

FILTERED=()
for d in "${TARGETS[@]}"; do
    if is_safe "$d"; then
        FILTERED+=("$d")
    else
        echo "Skipping (outside safe roots): $d" >&2
    fi
done
TARGETS=("${FILTERED[@]}")

# Sort by size descending for the printout
echo "Found ${#TARGETS[@]} TLC working directories:"
TOTAL_KB=0
declare -a SIZED
for d in "${TARGETS[@]}"; do
    SIZE_KB=$(du -sk "$d" 2>/dev/null | awk '{print $1}')
    [ -z "$SIZE_KB" ] && SIZE_KB=0
    TOTAL_KB=$((TOTAL_KB + SIZE_KB))
    SIZED+=("$SIZE_KB	$d")
done

printf '%s\n' "${SIZED[@]}" | sort -rn | while IFS=$'\t' read -r kb path; do
    hr=$(numfmt --to=iec --suffix=B $((kb * 1024)) 2>/dev/null || echo "${kb}K")
    printf "  %10s  %s\n" "$hr" "$path"
done

TOTAL_HR=$(numfmt --to=iec --suffix=B $((TOTAL_KB * 1024)) 2>/dev/null || echo "${TOTAL_KB}K")
echo "Total: $TOTAL_HR"

if [ "$DRY_RUN" = true ]; then
    echo "(dry run, nothing deleted)"
    exit 0
fi

if [ "$ASSUME_YES" != true ]; then
    read -r -p "Delete all of the above? [y/N] " ans
    case "$ans" in
        y|Y|yes|YES) ;;
        *) echo "Aborted."; exit 1 ;;
    esac
fi

for d in "${TARGETS[@]}"; do
    rm -rf "$d"
done

echo "Freed $TOTAL_HR"
