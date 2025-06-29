#!/bin/bash

# Specula ETCD Setup - Clone and prepare etcd/raft source code
# This script downloads the latest etcd/raft implementation from GitHub

set -e

echo "=== Specula ETCD Setup - Preparing etcd/raft Source Code ==="
echo

# Get directories
SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
PROJECT_ROOT="$( cd "$SCRIPT_DIR/../../.." &> /dev/null && pwd )"
EXAMPLE_DIR="$( cd "$SCRIPT_DIR/.." &> /dev/null && pwd )"

echo "Project root: $PROJECT_ROOT"
echo "Example directory: $EXAMPLE_DIR"
echo

# Define paths
ETCD_RAFT_DIR="$PROJECT_ROOT/systems/etcd/raft"
SOURCE_DIR="$EXAMPLE_DIR/source"
SOURCE_FILE="$SOURCE_DIR/raft.go"

# Step 1: Create necessary directories
echo "1. Creating directories..."
mkdir -p "$PROJECT_ROOT/systems/etcd"
mkdir -p "$SOURCE_DIR"
echo "✓ Directories created"

# Step 2: Clone etcd/raft repository if not exists
echo
echo "2. Checking etcd/raft repository..."
if [ ! -d "$ETCD_RAFT_DIR" ]; then
    echo "Cloning etcd/raft from https://github.com/etcd-io/raft.git..."
    git clone https://github.com/etcd-io/raft.git "$ETCD_RAFT_DIR"
    echo "✓ Repository cloned successfully"
else
    echo "Repository already exists. Updating..."
    cd "$ETCD_RAFT_DIR"
    git pull origin main || echo "Warning: Failed to update repository"
    cd "$PROJECT_ROOT"
    echo "✓ Repository updated"
fi

# Step 3: Copy raft.go to examples directory
echo
echo "3. Copying raft.go to examples directory..."
if [ -f "$ETCD_RAFT_DIR/raft.go" ]; then
    cp "$ETCD_RAFT_DIR/raft.go" "$SOURCE_FILE"
    echo "✓ Copied raft.go to $SOURCE_FILE"
    
    # Show file info
    echo "File size: $(wc -l < "$SOURCE_FILE") lines"
    echo "File path: $SOURCE_FILE"
else
    echo "Error: raft.go not found in cloned repository"
    echo "Repository contents:"
    ls -la "$ETCD_RAFT_DIR"
    exit 1
fi

# Step 4: Verify setup
echo
echo "4. Verifying setup..."
if [ -f "$SOURCE_FILE" ]; then
    echo "✓ Source file ready: $SOURCE_FILE"
    
    # Check for key Raft functions
    FUNCTIONS_FOUND=0
    for func in "func (r \*raft) tick" "func (r \*raft) Step" "func (r \*raft) handleAppendEntries"; do
        if grep -q "$func" "$SOURCE_FILE"; then
            FUNCTIONS_FOUND=$((FUNCTIONS_FOUND + 1))
        fi
    done
    
    echo "✓ Key Raft functions found: $FUNCTIONS_FOUND/3"
    
    if [ $FUNCTIONS_FOUND -ge 2 ]; then
        echo "✓ Setup completed successfully!"
    else
        echo "Warning: Some expected Raft functions not found. File may be incomplete."
    fi
else
    echo "✗ Setup failed: Source file not found"
    exit 1
fi

echo
echo "=== Setup Summary ==="
echo "✓ etcd/raft repository: $ETCD_RAFT_DIR"
echo "✓ Source file: $SOURCE_FILE"
echo "✓ Ready for instrumentation and testing"
echo
echo "Next steps:"
echo "1. Run instrumentation: bash scripts/run_instrumentation_test.sh"
echo "2. Run full workflow: bash scripts/run_full_test_with_verification.sh"
echo "3. Customize configuration in config/raft_config.yaml if needed" 