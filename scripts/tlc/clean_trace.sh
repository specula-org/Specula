#!/bin/bash
################################################################################
# Clean TTrace Output Files
# Usage: ./clean_trace.sh [-n|--dry-run] [-f|--force] SPEC_FILE
################################################################################

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m'

# Options
DRY_RUN=false
FORCE=false
SPEC_FILE=""

# Help function
usage() {
    echo "Usage: $0 [-n|--dry-run] [-f|--force] SPEC_FILE"
    echo ""
    echo "Delete TTrace output files (.bin and .tla), sim logs, and nohup.out."
    echo ""
    echo "Arguments:"
    echo "  SPEC_FILE    Path to the TLA+ spec file (e.g., Traceetcdraft.tla)"
    echo ""
    echo "Options:"
    echo "  -n, --dry-run    Show files to delete without actually deleting"
    echo "  -f, --force      Delete without confirmation"
    echo "  -h, --help       Show this help"
    echo ""
    echo "Examples:"
    echo "  $0 data/workloads/etcdraft/scenarios/snapshot/spec/Traceetcdraft.tla"
    echo "  $0 -n data/workloads/etcdraft/scenarios/snapshot/spec/Traceetcdraft.tla"
    echo "  $0 -f data/workloads/etcdraft/scenarios/snapshot/spec/Traceetcdraft.tla"
    exit 1
}

# Parse arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        -n|--dry-run)
            DRY_RUN=true
            shift
            ;;
        -f|--force)
            FORCE=true
            shift
            ;;
        -h|--help)
            usage
            ;;
        -*)
            echo -e "${RED}Error: Unknown option $1${NC}"
            usage
            ;;
        *)
            SPEC_FILE="$1"
            shift
            ;;
    esac
done

# Validate spec file argument
if [ -z "$SPEC_FILE" ]; then
    echo -e "${RED}Error: SPEC_FILE is required${NC}"
    usage
fi

# Check if spec file exists
if [ ! -f "$SPEC_FILE" ]; then
    echo -e "${RED}Error: Spec file not found: $SPEC_FILE${NC}"
    exit 1
fi

# Extract directory and base name
SPEC_DIR="$(dirname "$SPEC_FILE")"
SPEC_BASENAME="$(basename "$SPEC_FILE" .tla)"

# Find matching TTrace files, sim logs, and nohup.out
shopt -s nullglob
FILES=()
FILES+=("${SPEC_DIR}/${SPEC_BASENAME}_TTrace_"*)
FILES+=("${SPEC_DIR}/sim_${SPEC_BASENAME}"*.log)
if [ -f "${SPEC_DIR}/nohup.out" ]; then
    FILES+=("${SPEC_DIR}/nohup.out")
fi

if [ ${#FILES[@]} -eq 0 ]; then
    echo -e "${YELLOW}No trace/log files found for: $SPEC_FILE${NC}"
    exit 0
fi

# Calculate total size
TOTAL_SIZE=0
for f in "${FILES[@]}"; do
    if [ -f "$f" ]; then
        SIZE=$(stat -c%s "$f" 2>/dev/null || stat -f%z "$f" 2>/dev/null)
        TOTAL_SIZE=$((TOTAL_SIZE + SIZE))
    fi
done

# Human readable size (pure bash, no bc)
human_size() {
    local bytes=$1
    if [ $bytes -ge 1073741824 ]; then
        echo "$((bytes / 1073741824)).$((bytes % 1073741824 * 100 / 1073741824))G"
    elif [ $bytes -ge 1048576 ]; then
        echo "$((bytes / 1048576)).$((bytes % 1048576 * 100 / 1048576))M"
    elif [ $bytes -ge 1024 ]; then
        echo "$((bytes / 1024)).$((bytes % 1024 * 100 / 1024))K"
    else
        echo "${bytes}B"
    fi
}

# Display files
echo -e "${GREEN}Found ${#FILES[@]} trace/log files for: ${SPEC_BASENAME}.tla${NC}"
echo -e "Total size: $(human_size $TOTAL_SIZE)"
echo ""
echo "Files to delete:"
for f in "${FILES[@]}"; do
    if [ -f "$f" ]; then
        echo "  $f"
    fi
done
echo ""

# Dry run mode
if [ "$DRY_RUN" = true ]; then
    echo -e "${YELLOW}[DRY RUN] No files were deleted${NC}"
    exit 0
fi

# Confirm deletion
if [ "$FORCE" != true ]; then
    read -p "Delete these files? [y/N] " -n 1 -r
    echo
    if [[ ! $REPLY =~ ^[Yy]$ ]]; then
        echo -e "${YELLOW}Aborted${NC}"
        exit 0
    fi
fi

# Delete files
DELETED=0
for f in "${FILES[@]}"; do
    if [ -f "$f" ]; then
        if rm "$f" 2>/dev/null; then
            ((DELETED++))
        else
            echo -e "${RED}Failed to delete: $f${NC}"
        fi
    fi
done

echo -e "${GREEN}Deleted $DELETED files ($(human_size $TOTAL_SIZE) freed)${NC}"
