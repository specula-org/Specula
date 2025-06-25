#!/bin/bash

# TLAGEN Framework Setup Script
# This script sets up the complete TLAGEN environment

set -e  # Exit on any error

echo "Setting up TLAGEN Framework..."

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Helper functions
print_status() {
    echo -e "${BLUE}[INFO]${NC} $1"
}

print_success() {
    echo -e "${GREEN}[SUCCESS]${NC} $1"
}

print_warning() {
    echo -e "${YELLOW}[WARNING]${NC} $1"
}

print_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

# Check if command exists
command_exists() {
    command -v "$1" >/dev/null 2>&1
}

# Get the script directory
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"

print_status "Project root: $PROJECT_ROOT"

# Check system requirements
print_status "Checking system requirements..."

# Check Python
if command_exists python3; then
    PYTHON_VERSION=$(python3 --version 2>&1 | cut -d' ' -f2)
    print_success "Python found: $PYTHON_VERSION"
else
    print_error "Python 3 is required but not found"
    exit 1
fi

# Check Java
if command_exists java; then
    JAVA_VERSION=$(java -version 2>&1 | head -n1 | cut -d'"' -f2)
    print_success "Java found: $JAVA_VERSION"
else
    print_error "Java 8+ is required but not found"
    print_status "Please install Java 8 or higher:"
    print_status "  Ubuntu/Debian: sudo apt update && sudo apt install openjdk-11-jdk"
    print_status "  macOS: brew install openjdk@11"
    exit 1
fi

# Check Go (optional, for etcd example)
if command_exists go; then
    GO_VERSION=$(go version | cut -d' ' -f3)
    print_success "Go found: $GO_VERSION"
else
    print_warning "Go not found - required for etcd example"
    print_status "To install Go:"
    print_status "  Ubuntu/Debian: sudo apt update && sudo apt install golang-go"
    print_status "  macOS: brew install go"
fi

# Install Python dependencies
print_status "Installing Python dependencies..."
cd "$PROJECT_ROOT"

if [ -f "src/requirements.txt" ]; then
    pip3 install -r src/requirements.txt
    print_success "Python dependencies installed"
else
    print_warning "requirements.txt not found, installing common dependencies..."
    pip3 install pyyaml requests openai anthropic
fi

# Create lib directory and download TLA+ tools
print_status "Setting up TLA+ tools..."
mkdir -p "$PROJECT_ROOT/lib"

# Download tla2tools.jar if not exists
if [ ! -f "$PROJECT_ROOT/lib/tla2tools.jar" ]; then
    print_status "Downloading tla2tools.jar..."
    TLA_TOOLS_URL="https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar"
    
    if command_exists wget; then
        wget -O "$PROJECT_ROOT/lib/tla2tools.jar" "$TLA_TOOLS_URL"
    elif command_exists curl; then
        curl -L -o "$PROJECT_ROOT/lib/tla2tools.jar" "$TLA_TOOLS_URL"
    else
        print_error "Neither wget nor curl found. Please download tla2tools.jar manually:"
        print_status "  URL: $TLA_TOOLS_URL"
        print_status "  Save to: $PROJECT_ROOT/lib/tla2tools.jar"
        exit 1
    fi
    print_success "tla2tools.jar downloaded"
else
    print_success "tla2tools.jar already exists"
fi

# Download CommunityModules-deps.jar if not exists
if [ ! -f "$PROJECT_ROOT/lib/CommunityModules-deps.jar" ]; then
    print_status "Downloading CommunityModules-deps.jar..."
    COMMUNITY_MODULES_URL="https://github.com/tlaplus/CommunityModules/releases/download/202505152026/CommunityModules-deps.jar"
    
    if command_exists wget; then
        wget -O "$PROJECT_ROOT/lib/CommunityModules-deps.jar" "$COMMUNITY_MODULES_URL"
    elif command_exists curl; then
        curl -L -o "$PROJECT_ROOT/lib/CommunityModules-deps.jar" "$COMMUNITY_MODULES_URL"
    else
        print_warning "Could not download CommunityModules-deps.jar automatically"
        print_status "Please download manually from: $COMMUNITY_MODULES_URL"
    fi
    
    if [ -f "$PROJECT_ROOT/lib/CommunityModules-deps.jar" ]; then
        print_success "CommunityModules-deps.jar downloaded"
    else
        print_warning "CommunityModules-deps.jar download failed - this is optional for basic functionality"
    fi
else
    print_success "CommunityModules-deps.jar already exists"
fi

# Set up example directories
print_status "Setting up example directories..."
mkdir -p "$PROJECT_ROOT/examples/etcd/"{config,source,output,runners,spec,scripts}
mkdir -p "$PROJECT_ROOT/examples/etcd/spec/step5/spec"

# Copy default config if not exists
if [ ! -f "$PROJECT_ROOT/examples/etcd/config/raft_config.yaml" ]; then
    print_status "Creating default raft_config.yaml..."
    cat > "$PROJECT_ROOT/examples/etcd/config/raft_config.yaml" << 'EOF'
# TLAGEN Configuration for etcd/raft
system_name: "etcd-raft"
language: "go"

# TLA+ action mappings
actions:
  - name: "tickElection"
    functions: ["tickElection"]
    description: "Handle election timeout"
  
  - name: "tickHeartbeat" 
    functions: ["tickHeartbeat"]
    description: "Handle heartbeat timeout"
  
  - name: "Step"
    functions: ["Step"]
    description: "Process incoming message"

# Instrumentation settings
instrumentation:
  template_language: "go"
  trace_output_format: "ndjson"

# TLA+ specification settings
spec:
  constants:
    Server: ["n1", "n2", "n3"]
    Value: [1, 2, 3]
    Nil: ["Nil"]
    NoLimit: ["NoLimit"]
EOF
    print_success "Default raft_config.yaml created"
fi

# Verify installation
print_status "Verifying installation..."

# Test Java with TLA+ tools
if java -cp "$PROJECT_ROOT/lib/tla2tools.jar" tlc2.TLC -help >/dev/null 2>&1; then
    print_success "TLA+ tools working correctly"
else
    print_warning "TLA+ tools verification failed - may need manual setup"
fi

# Test Python imports
python3 -c "import yaml; import sys; print('Python imports OK')" 2>/dev/null && \
    print_success "Python environment OK" || \
    print_warning "Python environment may have issues"

# Create convenience aliases/scripts
print_status "Creating convenience scripts..."

# Create tlagen command wrapper
cat > "$PROJECT_ROOT/tlagen" << 'EOF'
#!/bin/bash
# TLAGEN command wrapper
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
export PYTHONPATH="$SCRIPT_DIR/src:$PYTHONPATH"
python3 -m src.core."$@"
EOF
chmod +x "$PROJECT_ROOT/tlagen"

print_success "Setup completed successfully!"
echo
print_status "TLAGEN is ready to use!"
echo
print_status "Quick start:"
print_status "  cd examples/etcd"
print_status "  bash scripts/run_instrumentation_test.sh"
echo
print_status "For full workflow:"
print_status "  cd examples/etcd" 
print_status "  bash scripts/run_full_test_with_verification.sh"
echo
print_status "For help:"
print_status "  ./tlagen --help"
echo

# Check if we're in examples/etcd and offer to run a test
if [ "$(basename "$(pwd)")" = "etcd" ] && [ -f "scripts/run_instrumentation_test.sh" ]; then
    echo -n "Would you like to run a quick test now? (y/n): "
    read -r response
    if [ "$response" = "y" ] || [ "$response" = "Y" ]; then
        print_status "Running quick test..."
        bash scripts/run_instrumentation_test.sh
    fi
fi
