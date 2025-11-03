#!/bin/bash
#
# This script builds and runs the Phase 2: CFA Transformation tool.
# It takes an input TLA+ spec file and outputs a transformed TLA+ spec file.
# Optionally supports --show-tree parameter to display parse tree GUI.
#

# Exit immediately if a command exits with a non-zero status.
set -e

# --- 1. Parse Arguments ---
SHOW_TREE=false
ALGORITHM="all"
DEBUG_MODE=false
INPUT_FILE=""
OUTPUT_FILE=""

# Parse command line arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --show-tree|-show-tree)
            SHOW_TREE=true
            shift
            ;;
        --debug|-debug)
            DEBUG_MODE=true
            shift
            ;;
        --algorithm|-algorithm)
            if [[ -n "$2" && "$2" != --* ]]; then
                ALGORITHM="$2"
                shift 2
            else
                echo "ERROR: --algorithm requires a value"
                exit 1
            fi
            ;;
        *)
            if [ -z "$INPUT_FILE" ]; then
                INPUT_FILE="$1"
            elif [ -z "$OUTPUT_FILE" ]; then
                OUTPUT_FILE="$1"
            fi
            shift
            ;;
    esac
done

# --- 2. Argument Validation ---
if [ -z "$INPUT_FILE" ] || [ -z "$OUTPUT_FILE" ]; then
    echo "ERROR: Invalid number of arguments."
    echo "Usage: ./run.sh <input_file.tla> <output_file.tla> [--show-tree] [--algorithm <algorithm>] [--debug]"
    echo "       ./run.sh --show-tree <input_file.tla> <output_file.tla>"
    echo "       ./run.sh --algorithm sa <input_file.tla> <output_file.tla>"
    echo "       ./run.sh --algorithm pc <input_file.tla> <output_file.tla>"
    echo "       ./run.sh --debug <input_file.tla> <output_file.tla>"
    echo ""
    echo "Algorithm options:"
    echo "  --algorithm all    Run all algorithms (default)"
    echo "  --algorithm sa     Run static analysis only"
    echo "  --algorithm uc     Run unchanged variable analysis only"
    echo "  --algorithm ud     Run undefined variable analysis only"
    echo "  --algorithm pc     Run process cutting analysis only"
    echo ""
    echo "Debug options:"
    echo "  --debug            Print IN/OUT variables for each statement (for debugging)"
    exit 1
fi

# Validate algorithm parameter
case "$ALGORITHM" in
    all|sa|uc|ud|pc)
        ;;
    *)
        echo "ERROR: Invalid algorithm: $ALGORITHM"
        echo "Valid algorithms: all, sa, uc, ud, pc"
        exit 1
        ;;
esac

# Create output directory if it doesn't exist
mkdir -p "$(dirname "$OUTPUT_FILE")"

# Check script execution permission
if [ ! -x "$0" ]; then
    echo "Setting execution permission for the script..."
    chmod +x "$0"
fi

# Check if input file exists
if [ ! -f "$INPUT_FILE" ]; then
    echo "Error: Input file '$INPUT_FILE' does not exist"
    exit 1
fi

# --- 3. Path and Tool Setup ---
# Find the directory where this script is located. This is robust.
SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" &> /dev/null && pwd)
PROJECT_ROOT=$(cd "$SCRIPT_DIR/../.." && pwd) # Resolve to absolute project root

echo "=== [Phase 2] Starting CFA Transformation ==="
echo "Script directory: $SCRIPT_DIR"
echo "Input file: $INPUT_FILE"
echo "Output file: $OUTPUT_FILE"
echo "Algorithm: $ALGORITHM"
if [ "$SHOW_TREE" = true ]; then
    echo "Parse tree GUI will be displayed"
fi
if [ "$DEBUG_MODE" = true ]; then
    echo "Debug mode enabled: IN/OUT variables will be printed"
fi

# --- 4. Build the Java Project with Maven ---
echo "Building the Java project with Maven... (this may take a moment)"
# We run maven from within the script's directory to ensure it finds pom.xml
# The ( ) creates a subshell, so the 'cd' doesn't affect the rest of the script.
(cd "$SCRIPT_DIR" && mvn package -DskipTests)

# Check if Maven build was successful
if [ $? -ne 0 ]; then
    echo "Error: Maven build failed"
    exit 1
fi

# --- 5. Find the JARs ---
# The JAR file is usually in the 'target' directory. We find it dynamically.
JAR_FILE=$(find "$SCRIPT_DIR/target" -name "*-jar-with-dependencies.jar" | head -n 1)

if [ -z "$JAR_FILE" ]; then
    echo "ERROR: Executable JAR file not found. The Maven build might have failed."
    echo "Please check for a '*-jar-with-dependencies.jar' file in the '$SCRIPT_DIR/target' directory."
    exit 1
fi
echo "Found executable JAR: $JAR_FILE"

# The tla2tools.jar is also needed, should be in lib/tla2tools.jar
TLA2TOOLS_JAR="$PROJECT_ROOT/lib/tla2tools.jar"

if [ ! -f "$TLA2TOOLS_JAR" ]; then
    echo "ERROR: TLA2Tools JAR file not found. Please run scripts/setup.sh."
    exit 1
fi
echo "Found TLA2Tools JAR: $TLA2TOOLS_JAR"

# --- 6. Run the Java Application ---
echo "Running the CFA transformation logic..."

# Build Java command with optional parameters
JAVA_ARGS=()
if [ "$SHOW_TREE" = true ]; then
    JAVA_ARGS+=(--show-tree)
fi
if [ "$DEBUG_MODE" = true ]; then
    JAVA_ARGS+=(--debug)
fi
if [ "$ALGORITHM" != "all" ]; then
    JAVA_ARGS+=(--algorithm "$ALGORITHM")
fi
JAVA_ARGS+=("$INPUT_FILE" "$OUTPUT_FILE")

java -cp "$TLA2TOOLS_JAR:$JAR_FILE" CFG.SANYTransformerCli "${JAVA_ARGS[@]}"

# Check if transformation was successful
if [ $? -ne 0 ]; then
    echo "Error: CFA transformation failed"
    exit 1
fi

echo "=== [Phase 2] CFA Transformation successful. ==="
echo "Output written to: $OUTPUT_FILE"
