#!/bin/bash
#
# This script builds and runs the Phase 2: CFA Transformation tool.
# It takes an input TLA+ spec file and outputs a transformed TLA+ spec file.
#

# Exit immediately if a command exits with a non-zero status.
set -e

# Create output directory if it doesn't exist
mkdir -p "$(dirname "$2")"

# 检查脚本执行权限
if [ ! -x "$0" ]; then
    echo "Setting execution permission for the script..."
    chmod +x "$0"
fi

# 检查输入文件是否存在
if [ ! -f "$1" ]; then
    echo "Error: Input file '$1' does not exist"
    exit 1
fi

# --- 1. Argument Validation ---
if [ "$#" -ne 2 ]; then
    echo "ERROR: Invalid number of arguments."
    echo "Usage: ./phase_2_cfa_transformation/run.sh <path_to_input.tla> <path_to_output.tla>"
    exit 1
fi

INPUT_FILE="$1"
OUTPUT_FILE="$2"

# --- 2. Path and Tool Setup ---
# Find the directory where this script is located. This is robust.
SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" &> /dev/null && pwd)
PROJECT_ROOT="$SCRIPT_DIR/.." # The root is one level up

echo "=== [Phase 2] Starting CFA Transformation ==="
echo "Script directory: $SCRIPT_DIR"
echo "Input file: $INPUT_FILE"
echo "Output file: $OUTPUT_FILE"

# --- 3. Build the Java Project with Maven ---
echo "Building the Java project with Maven... (this may take a moment)"
# We run maven from within the script's directory to ensure it finds pom.xml
# The ( ) creates a subshell, so the 'cd' doesn't affect the rest of the script.
(cd "$SCRIPT_DIR" && mvn package -DskipTests)

# 检查Maven构建是否成功
if [ $? -ne 0 ]; then
    echo "Error: Maven build failed"
    exit 1
fi

# --- 4. Find the Executable JAR ---
# The JAR file is usually in the 'target' directory. We find it dynamically.
JAR_FILE=$(find "$SCRIPT_DIR/target" -name "*-jar-with-dependencies.jar" | head -n 1)

if [ -z "$JAR_FILE" ]; then
    echo "ERROR: Executable JAR file not found. The Maven build might have failed."
    echo "Please check for a '*-jar-with-dependencies.jar' file in the '$SCRIPT_DIR/target' directory."
    exit 1
fi
echo "Found executable JAR: $JAR_FILE"

# --- 5. Run the Java Application ---
echo "Running the CFA transformation logic..."
java -jar "$JAR_FILE" "$INPUT_FILE" "$OUTPUT_FILE"

# 检查转换是否成功
if [ $? -ne 0 ]; then
    echo "Error: CFA transformation failed"
    exit 1
fi

echo "=== [Phase 2] CFA Transformation successful. ==="
echo "Output written to: $OUTPUT_FILE"