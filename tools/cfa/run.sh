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
INPUT_FILE=""
OUTPUT_FILE=""

# Parse command line arguments
for arg in "$@"; do
    case $arg in
        --show-tree|-show-tree)
            SHOW_TREE=true
            shift
            ;;
        *)
            if [ -z "$INPUT_FILE" ]; then
                INPUT_FILE="$arg"
            elif [ -z "$OUTPUT_FILE" ]; then
                OUTPUT_FILE="$arg"
            fi
            shift
            ;;
    esac
done

# --- 2. Argument Validation ---
if [ -z "$INPUT_FILE" ] || [ -z "$OUTPUT_FILE" ]; then
    echo "ERROR: Invalid number of arguments."
    echo "Usage: ./run.sh <input_file.tla> <output_file.tla> [--show-tree]"
    echo "       ./run.sh --show-tree <input_file.tla> <output_file.tla>"
    exit 1
fi

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
PROJECT_ROOT="$SCRIPT_DIR/.." # The root is one level up

echo "=== [Phase 2] Starting CFA Transformation ==="
echo "Script directory: $SCRIPT_DIR"
echo "Input file: $INPUT_FILE"
echo "Output file: $OUTPUT_FILE"
if [ "$SHOW_TREE" = true ]; then
    echo "Parse tree GUI will be displayed"
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

# --- 5. Find the Executable JAR ---
# The JAR file is usually in the 'target' directory. We find it dynamically.
JAR_FILE=$(find "$SCRIPT_DIR/target" -name "*-jar-with-dependencies.jar" | head -n 1)

if [ -z "$JAR_FILE" ]; then
    echo "ERROR: Executable JAR file not found. The Maven build might have failed."
    echo "Please check for a '*-jar-with-dependencies.jar' file in the '$SCRIPT_DIR/target' directory."
    exit 1
fi
echo "Found executable JAR: $JAR_FILE"

# --- 6. Run the Java Application ---
echo "Running the CFA transformation logic..."

# Build Java command with optional --show-tree parameter
if [ "$SHOW_TREE" = true ]; then
    java -jar "$JAR_FILE" --show-tree "$INPUT_FILE" "$OUTPUT_FILE"
else
    java -jar "$JAR_FILE" "$INPUT_FILE" "$OUTPUT_FILE"
fi

# Check if transformation was successful
if [ $? -ne 0 ]; then
    echo "Error: CFA transformation failed"
    exit 1
fi

echo "=== [Phase 2] CFA Transformation successful. ==="
echo "Output written to: $OUTPUT_FILE"