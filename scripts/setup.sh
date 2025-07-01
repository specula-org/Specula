#!/bin/bash

# Specula Framework Setup Script
# This script sets up the complete Specula environment with all dependencies

set -e  # Exit on any error

echo "Setting up Specula Framework..."

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

# Check pip
if command_exists pip3; then
    print_success "pip3 found"
else
    print_error "pip3 is required but not found"
    print_status "Please install pip3:"
    print_status "  Ubuntu/Debian: sudo apt update && sudo apt install python3-pip"
    exit 1
fi

# Check Java
if command_exists java; then
    JAVA_VERSION=$(java -version 2>&1 | head -n1 | cut -d'"' -f2)
    print_success "Java found: $JAVA_VERSION"
else
    print_error "Java 11+ is required but not found"
    print_status "Please install Java 11 or higher:"
    print_status "  Ubuntu/Debian: sudo apt update && sudo apt install openjdk-11-jdk"
    print_status "  macOS: brew install openjdk@11"
    exit 1
fi

# Check/Install Maven
if command_exists mvn; then
    MVN_VERSION=$(mvn -version 2>&1 | head -n1 | cut -d' ' -f3)
    print_success "Maven found: $MVN_VERSION"
else
    print_warning "Maven not found - required for CFA tool"
    print_status "Installing Maven..."
    
    # Detect OS and install Maven
    if [[ "$OSTYPE" == "linux-gnu"* ]]; then
        if command_exists apt; then
            sudo apt update && sudo apt install -y maven
        elif command_exists yum; then
            sudo yum install -y maven
        elif command_exists dnf; then
            sudo dnf install -y maven
        else
            print_error "Cannot auto-install Maven. Please install manually:"
            print_status "  Ubuntu/Debian: sudo apt install maven"
            print_status "  CentOS/RHEL: sudo yum install maven"
            exit 1
        fi
    elif [[ "$OSTYPE" == "darwin"* ]]; then
        if command_exists brew; then
            brew install maven
        else
            print_error "Cannot auto-install Maven. Please install Homebrew first or install Maven manually"
            exit 1
        fi
    else
        print_error "Unsupported OS for auto-installation. Please install Maven manually"
        exit 1
    fi
    
    # Verify Maven installation
    if command_exists mvn; then
        MVN_VERSION=$(mvn -version 2>&1 | head -n1 | cut -d' ' -f3)
        print_success "Maven installed successfully: $MVN_VERSION"
    else
        print_error "Maven installation failed"
        exit 1
    fi
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
    print_status "Installing from src/requirements.txt..."
    pip3 install -r src/requirements.txt
    print_success "Python dependencies installed"
else
    print_warning "requirements.txt not found, installing common dependencies..."
    pip3 install anthropic>=0.34.0 openai>=1.0.0 pyyaml>=6.0 requests>=2.25.0 torch>=1.9.0 sentence-transformers>=2.2.0 numpy>=1.21.0
fi

# Create necessary directories
print_status "Creating necessary directories..."
mkdir -p "$PROJECT_ROOT/lib"
mkdir -p "$PROJECT_ROOT/models"

# Download TLA+ tools
print_status "Setting up TLA+ tools..."

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

# Download Hugging Face model
print_status "Setting up Hugging Face embedding model..."
MODEL_DIR="$PROJECT_ROOT/models/huggingface-MiniLM-L6-v2"

if [ ! -d "$MODEL_DIR" ]; then
    print_status "Downloading sentence-transformers/all-MiniLM-L6-v2 model..."
    
    # Create the model directory
    mkdir -p "$MODEL_DIR"
    
    # Use Python to download the model
    python3 -c "
from sentence_transformers import SentenceTransformer
import os
import shutil

model_name = 'sentence-transformers/all-MiniLM-L6-v2'
target_dir = '$MODEL_DIR'

print(f'Downloading model: {model_name}')
print(f'Target directory: {target_dir}')

try:
    # Download model to a temporary cache location
    model = SentenceTransformer(model_name)
    
    # Get the cache directory where the model was downloaded
    cache_dir = model._modules['0'].auto_model.config._name_or_path
    if not os.path.isabs(cache_dir):
        from transformers import AutoModel
        temp_model = AutoModel.from_pretrained(model_name)
        cache_dir = temp_model.config._name_or_path
    
    print(f'Model downloaded successfully to cache')
    
    # Save the model to our target directory
    model.save(target_dir)
    print(f'Model saved to: {target_dir}')
    
except Exception as e:
    print(f'Error downloading model: {e}')
    print('You may need to install additional dependencies or check your internet connection')
    exit(1)
"
    
    if [ $? -eq 0 ] && [ -d "$MODEL_DIR" ]; then
        print_success "Hugging Face model downloaded successfully"
    else
        print_warning "Failed to download Hugging Face model automatically"
        print_status "The model will be downloaded automatically on first use"
        print_status "Make sure you have internet connection when running the framework"
    fi
else
    print_success "Hugging Face model already exists"
fi

# Set up example directories
print_status "Setting up example directories..."
mkdir -p "$PROJECT_ROOT/examples/etcd/"{config,source,output,runners,spec,scripts}
mkdir -p "$PROJECT_ROOT/examples/etcd/spec/step4/spec"

# Copy default config if not exists
if [ ! -f "$PROJECT_ROOT/examples/etcd/config/raft_config.yaml" ]; then
    print_status "Creating default raft_config.yaml..."
    cat > "$PROJECT_ROOT/examples/etcd/config/raft_config.yaml" << 'EOF'
# Specula Configuration for etcd/raft
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

# Verify knowledge base exists
if [ -f "$PROJECT_ROOT/src/rag/initial_errors.json" ]; then
    print_success "Knowledge base found at src/rag/initial_errors.json"
else
    print_warning "Knowledge base not found at src/rag/initial_errors.json"
    print_status "RAG functionality may not work without the knowledge base"
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
print_status "Testing Python dependencies..."
python3 -c "
import sys
missing_packages = []

packages = [
    'yaml', 'anthropic', 'openai', 'requests', 
    'torch', 'sentence_transformers', 'numpy'
]

for package in packages:
    try:
        if package == 'yaml':
            import yaml
        elif package == 'anthropic':
            import anthropic
        elif package == 'openai':
            import openai
        elif package == 'requests':
            import requests
        elif package == 'torch':
            import torch
        elif package == 'sentence_transformers':
            from sentence_transformers import SentenceTransformer
        elif package == 'numpy':
            import numpy
        print(f'✓ {package}')
    except ImportError as e:
        print(f'✗ {package}: {e}')
        missing_packages.append(package)

if missing_packages:
    print(f'Missing packages: {missing_packages}')
    sys.exit(1)
else:
    print('All Python dependencies are available')
" && print_success "Python environment OK" || print_warning "Python environment may have issues"

# Test Maven (for CFA tool)
if command_exists mvn; then
    print_status "Testing Maven..."
    if mvn -version >/dev/null 2>&1; then
        print_success "Maven working correctly"
    else
        print_warning "Maven verification failed"
    fi
fi

# Create convenience aliases/scripts
print_status "Creating convenience scripts..."

# Create specula command wrapper
cat > "$PROJECT_ROOT/specula" << 'EOF'
#!/bin/bash
# Specula Framework Command Wrapper
# Unified interface for all Specula tools and steps

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
export PYTHONPATH="$SCRIPT_DIR/src:$PYTHONPATH"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

print_usage() {
    echo "Specula Framework - Unified Command Interface"
    echo
    echo "Usage: $0 <command> [options]"
    echo
    echo "Commands:"
    echo "  step1 <input> <output> [options]     Generate TLA+ specification from source code"
    echo "  step2 <input> <output> [options]     Transform TLA+ spec using CFA tool"
    echo "  step3 <spec_file> [options]          Verify TLA+ specification using TLC"
    echo "  step4.1 <source> <config> [options] Instrument source code for tracing"
    echo "  step4.2 <spec> <trace> [options]    Validate trace against specification"
    echo "  cfa <input> <output> [options]       Alias for step2"
    echo "  verify <spec_file> [options]         Alias for step3"
    echo "  instrument <source> <config>         Alias for step4.1"
    echo "  validate <spec> <trace>              Alias for step4.2"
    echo "  help                                 Show this help message"
    echo
    echo "Step 1 Options:"
    echo "  --mode <mode>          Generation mode: direct, draft-based, correct-only, etc."
    echo "  --model <model>        Override LLM model"
    echo "  --config <file>        Configuration file path"
    echo "  --no-rag              Disable RAG-based error correction"
    echo
    echo "Step 2 Options:"
    echo "  --config <file>        CFA configuration file"
    echo "  --debug               Enable debug output"
    echo
    echo "Step 3 Options:"
    echo "  --model-check         Run full model checking"
    echo "  --deadlock            Check for deadlocks only"
    echo "  --workers <n>         Number of worker threads"
    echo "  --depth <n>           Maximum search depth"
    echo
    echo "Step 4.1 Options:"
    echo "  --output <dir>        Output directory for instrumented code"
    echo "  --template <file>     Custom instrumentation template"
    echo
    echo "Step 4.2 Options:"
    echo "  --config <file>       Trace validation configuration"
    echo "  --output <dir>        Output directory for validation results"
    echo
    echo "Examples:"
    echo "  # Complete workflow:"
    echo "  $0 step1 source/raft.go output/spec --mode draft-based"
    echo "  $0 step2 output/spec/Raft.tla output/transformed/Raft.tla"
    echo "  $0 step3 output/transformed/Raft.tla --model-check"
    echo "  $0 step4.1 source/raft.go config/raft_config.yaml"
    echo "  $0 step4.2 output/transformed/Raft.tla trace.ndjson"
    echo
    echo "  # Individual steps:"
    echo "  $0 verify output/spec/Raft.tla --deadlock"
    echo "  $0 instrument source/ config.yaml --output instrumented/"
    echo "  $0 validate spec.tla trace.ndjson --config validation.cfg"
}

# Check if no arguments provided
if [ $# -eq 0 ]; then
    print_usage
    exit 1
fi

COMMAND="$1"
shift

case "$COMMAND" in
    "step1"|"p1")
        if [ $# -lt 2 ]; then
            echo -e "${RED}Error:${NC} step 1 requires input and output arguments"
            echo "Usage: $0 step1 <input> <output> [options]"
            exit 1
        fi
        
        echo -e "${BLUE}[Specula step 1]${NC} TLA+ Specification Generation"
        python3 -m src.core.iispec_generator "$@"
        ;;
        
    "step2"|"p2"|"cfa")
        if [ $# -lt 2 ]; then
            echo -e "${RED}Error:${NC} step 2 requires input and output arguments"
            echo "Usage: $0 step2 <input> <output> [options]"
            exit 1
        fi
        
        INPUT_FILE="$1"
        OUTPUT_FILE="$2"
        shift 2
        
        # Parse additional options
        DEBUG_FLAG=""
        CONFIG_FILE=""
        
        while [[ $# -gt 0 ]]; do
            case $1 in
                --debug)
                    DEBUG_FLAG="--debug"
                    shift
                    ;;
                --config)
                    CONFIG_FILE="$2"
                    shift 2
                    ;;
                *)
                    echo -e "${YELLOW}Warning:${NC} Unknown option: $1"
                    shift
                    ;;
            esac
        done
        
        echo -e "${BLUE}[Specula step 2]${NC} TLA+ Specification Transformation (CFA)"
        echo "Input: $INPUT_FILE"
        echo "Output: $OUTPUT_FILE"
        
        # Check if input file exists
        if [ ! -f "$INPUT_FILE" ]; then
            echo -e "${RED}Error:${NC} Input file not found: $INPUT_FILE"
            exit 1
        fi
        
        # Check if CFA tool exists
        CFA_SCRIPT="$SCRIPT_DIR/tools/cfa/run.sh"
        if [ ! -f "$CFA_SCRIPT" ]; then
            echo -e "${RED}Error:${NC} CFA tool not found at: $CFA_SCRIPT"
            echo "Please ensure the CFA tool is properly installed"
            exit 1
        fi
        
        # Create output directory if it doesn't exist
        OUTPUT_DIR="$(dirname "$OUTPUT_FILE")"
        mkdir -p "$OUTPUT_DIR"
        
        # Run CFA transformation
        echo -e "${BLUE}[INFO]${NC} Running CFA transformation..."
        if [ -n "$DEBUG_FLAG" ]; then
            echo "Command: bash $CFA_SCRIPT $INPUT_FILE $OUTPUT_FILE $CONFIG_FILE"
        fi
        
        if [ -n "$CONFIG_FILE" ]; then
            bash "$CFA_SCRIPT" "$INPUT_FILE" "$OUTPUT_FILE" "$CONFIG_FILE"
        else
            bash "$CFA_SCRIPT" "$INPUT_FILE" "$OUTPUT_FILE"
        fi
        
        CFA_EXIT_CODE=$?
        if [ $CFA_EXIT_CODE -eq 0 ]; then
            echo -e "${GREEN}[SUCCESS]${NC} CFA transformation completed successfully"
            echo "Output saved to: $OUTPUT_FILE"
        else
            echo -e "${RED}[ERROR]${NC} CFA transformation failed with exit code: $CFA_EXIT_CODE"
            exit $CFA_EXIT_CODE
        fi
        ;;
        
    "step3"|"p3"|"verify")
        if [ $# -lt 1 ]; then
            echo -e "${RED}Error:${NC} step 3 requires a TLA+ specification file"
            echo "Usage: $0 step3 <spec_file> [options]"
            exit 1
        fi
        
        SPEC_FILE="$1"
        shift
        
        echo -e "${BLUE}[Specula Step 3]${NC} TLA+ Specification Verification"
        echo "Spec file: $SPEC_FILE"
        
        # Check if spec file exists
        if [ ! -f "$SPEC_FILE" ]; then
            echo -e "${RED}Error:${NC} Specification file not found: $SPEC_FILE"
            exit 1
        fi
        
        # Parse options
        MODEL_CHECK=false
        DEADLOCK_ONLY=false
        WORKERS=""
        DEPTH=""
        
        while [[ $# -gt 0 ]]; do
            case $1 in
                --model-check)
                    MODEL_CHECK=true
                    shift
                    ;;
                --deadlock)
                    DEADLOCK_ONLY=true
                    shift
                    ;;
                --workers)
                    WORKERS="-workers $2"
                    shift 2
                    ;;
                --depth)
                    DEPTH="-depth $2"
                    shift 2
                    ;;
                *)
                    echo -e "${YELLOW}Warning:${NC} Unknown option: $1"
                    shift
                    ;;
            esac
        done
        
        # Build TLC command
        TLC_CMD="java -cp $SCRIPT_DIR/lib/tla2tools.jar tlc2.TLC"
        
        if [ "$DEADLOCK_ONLY" = true ]; then
            TLC_CMD="$TLC_CMD -deadlock"
        fi
        
        if [ -n "$WORKERS" ]; then
            TLC_CMD="$TLC_CMD $WORKERS"
        fi
        
        if [ -n "$DEPTH" ]; then
            TLC_CMD="$TLC_CMD $DEPTH"
        fi
        
        # Extract module name from file
        MODULE_NAME=$(basename "$SPEC_FILE" .tla)
        SPEC_DIR=$(dirname "$SPEC_FILE")
        
        echo -e "${BLUE}[INFO]${NC} Running TLC verification..."
        echo "Command: $TLC_CMD $MODULE_NAME"
        
        # Change to spec directory and run TLC
        cd "$SPEC_DIR"
        eval "$TLC_CMD $MODULE_NAME"
        
        TLC_EXIT_CODE=$?
        if [ $TLC_EXIT_CODE -eq 0 ]; then
            echo -e "${GREEN}[SUCCESS]${NC} TLA+ verification completed successfully"
        else
            echo -e "${RED}[ERROR]${NC} TLA+ verification failed with exit code: $TLC_EXIT_CODE"
            exit $TLC_EXIT_CODE
        fi
        ;;
        
    "step4.1"|"p4.1"|"instrument")
        if [ $# -lt 2 ]; then
            echo -e "${RED}Error:${NC} step 4.1 requires source and config arguments"
            echo "Usage: $0 step4.1 <source> <config> [options]"
            exit 1
        fi
        
        SOURCE_PATH="$1"
        CONFIG_FILE="$2"
        shift 2
        
        echo -e "${BLUE}[Specula Step 4.1]${NC} Source Code Instrumentation"
        echo "Source: $SOURCE_PATH"
        echo "Config: $CONFIG_FILE"
        
        # Check if source exists
        if [ ! -e "$SOURCE_PATH" ]; then
            echo -e "${RED}Error:${NC} Source path not found: $SOURCE_PATH"
            exit 1
        fi
        
        # Check if config file exists
        if [ ! -f "$CONFIG_FILE" ]; then
            echo -e "${RED}Error:${NC} Config file not found: $CONFIG_FILE"
            exit 1
        fi
        
        # Parse options
        OUTPUT_DIR=""
        TEMPLATE_FILE=""
        
        while [[ $# -gt 0 ]]; do
            case $1 in
                --output)
                    OUTPUT_DIR="$2"
                    shift 2
                    ;;
                --template)
                    TEMPLATE_FILE="$2"
                    shift 2
                    ;;
                *)
                    echo -e "${YELLOW}Warning:${NC} Unknown option: $1"
                    shift
                    ;;
            esac
        done
        
        # Set default output directory
        if [ -z "$OUTPUT_DIR" ]; then
            OUTPUT_DIR="$(dirname "$SOURCE_PATH")/instrumented"
        fi
        
        echo -e "${BLUE}[INFO]${NC} Running instrumentation..."
        echo "Output directory: $OUTPUT_DIR"
        
        # Create output directory
        mkdir -p "$OUTPUT_DIR"
        
        # Run instrumentation using Python module
        INSTRUMENT_CMD="python3 -m src.instrumentation.instrument_code"
        INSTRUMENT_CMD="$INSTRUMENT_CMD --source $SOURCE_PATH"
        INSTRUMENT_CMD="$INSTRUMENT_CMD --config $CONFIG_FILE"
        INSTRUMENT_CMD="$INSTRUMENT_CMD --output $OUTPUT_DIR"
        
        if [ -n "$TEMPLATE_FILE" ]; then
            INSTRUMENT_CMD="$INSTRUMENT_CMD --template $TEMPLATE_FILE"
        fi
        
        echo "Command: $INSTRUMENT_CMD"
        eval "$INSTRUMENT_CMD"
        
        INSTRUMENT_EXIT_CODE=$?
        if [ $INSTRUMENT_EXIT_CODE -eq 0 ]; then
            echo -e "${GREEN}[SUCCESS]${NC} Source code instrumentation completed"
            echo "Instrumented code saved to: $OUTPUT_DIR"
        else
            echo -e "${RED}[ERROR]${NC} Instrumentation failed with exit code: $INSTRUMENT_EXIT_CODE"
            exit $INSTRUMENT_EXIT_CODE
        fi
        ;;
        
    "step4.2"|"p4.2"|"validate")
        if [ $# -lt 2 ]; then
            echo -e "${RED}Error:${NC} step 4.2 requires spec and trace arguments"
            echo "Usage: $0 step4.2 <spec> <trace> [options]"
            exit 1
        fi
        
        SPEC_FILE="$1"
        TRACE_FILE="$2"
        shift 2
        
        echo -e "${BLUE}[Specula Step 4.2]${NC} Trace Validation"
        echo "Spec file: $SPEC_FILE"
        echo "Trace file: $TRACE_FILE"
        
        # Check if files exist
        if [ ! -f "$SPEC_FILE" ]; then
            echo -e "${RED}Error:${NC} Specification file not found: $SPEC_FILE"
            exit 1
        fi
        
        if [ ! -f "$TRACE_FILE" ]; then
            echo -e "${RED}Error:${NC} Trace file not found: $TRACE_FILE"
            exit 1
        fi
        
        # Parse options
        CONFIG_FILE=""
        OUTPUT_DIR=""
        
        while [[ $# -gt 0 ]]; do
            case $1 in
                --config)
                    CONFIG_FILE="$2"
                    shift 2
                    ;;
                --output)
                    OUTPUT_DIR="$2"
                    shift 2
                    ;;
                *)
                    echo -e "${YELLOW}Warning:${NC} Unknown option: $1"
                    shift
                    ;;
            esac
        done
        
        # Set default output directory
        if [ -z "$OUTPUT_DIR" ]; then
            OUTPUT_DIR="$(dirname "$SPEC_FILE")/validation_results"
        fi
        
        echo -e "${BLUE}[INFO]${NC} Running trace validation..."
        echo "Output directory: $OUTPUT_DIR"
        
        # Create output directory
        mkdir -p "$OUTPUT_DIR"
        
        # Determine the spec directory and trace spec file
        SPEC_DIR=$(dirname "$SPEC_FILE")
        MODULE_NAME=$(basename "$SPEC_FILE" .tla)
        
        # Look for corresponding specTrace.tla or TraceSpec.tla
        TRACE_SPEC=""
        if [ -f "$SPEC_DIR/specTrace.tla" ]; then
            TRACE_SPEC="specTrace"
        elif [ -f "$SPEC_DIR/TraceSpec.tla" ]; then
            TRACE_SPEC="TraceSpec"
        else
            echo -e "${RED}Error:${NC} No trace specification found (specTrace.tla or TraceSpec.tla) in $SPEC_DIR"
            exit 1
        fi
        
        # Copy trace file to spec directory if not already there
        TRACE_NAME=$(basename "$TRACE_FILE")
        if [ "$SPEC_DIR/$TRACE_NAME" != "$TRACE_FILE" ]; then
            cp "$TRACE_FILE" "$SPEC_DIR/$TRACE_NAME"
            echo -e "${BLUE}[INFO]${NC} Copied trace file to spec directory"
        fi
        
        # Build TLC command for trace validation
        cd "$SPEC_DIR"
        
        # Check if config file exists
        if [ -n "$CONFIG_FILE" ] && [ -f "$CONFIG_FILE" ]; then
            TLC_CMD="java -cp $SCRIPT_DIR/lib/tla2tools.jar tlc2.TLC -config $CONFIG_FILE $TRACE_SPEC"
        elif [ -f "specTrace.cfg" ]; then
            TLC_CMD="java -cp $SCRIPT_DIR/lib/tla2tools.jar tlc2.TLC -config specTrace.cfg $TRACE_SPEC"
        else
            TLC_CMD="java -cp $SCRIPT_DIR/lib/tla2tools.jar tlc2.TLC $TRACE_SPEC"
        fi
        
        echo "Command: $TLC_CMD"
        eval "$TLC_CMD"
        
        VALIDATION_EXIT_CODE=$?
        if [ $VALIDATION_EXIT_CODE -eq 0 ]; then
            echo -e "${GREEN}[SUCCESS]${NC} Trace validation completed successfully"
            echo "Results available in: $SPEC_DIR"
        else
            echo -e "${RED}[ERROR]${NC} Trace validation failed with exit code: $VALIDATION_EXIT_CODE"
            exit $VALIDATION_EXIT_CODE
        fi
        ;;
        
    "help"|"-h"|"--help")
        print_usage
        ;;
        
    *)
        echo -e "${RED}Error:${NC} Unknown command: $COMMAND"
        echo "Use '$0 help' for usage information"
        exit 1
        ;;
esac
EOF
chmod +x "$PROJECT_ROOT/specula"



print_success "Setup completed successfully!"
echo
print_status "Specula is ready to use!"
echo
print_status "Verification tests:"
print_status "  Test TLA+ tools: java -cp lib/tla2tools.jar tlc2.TLC -help"
print_status "  Test CFA tool: cd tools/cfa && mvn compile"
echo
print_status "Unified Command Interface:"
print_status "  ./specula help                    # Show all available commands"
print_status "  ./specula step1 <input> <output> # Generate TLA+ specification"
print_status "  ./specula step2 <input> <output> # Transform TLA+ specification"
print_status "  ./specula step3 <spec_file>      # Verify TLA+ specification"
print_status "  ./specula step4.1 <src> <config> # Instrument source code"
print_status "  ./specula step4.2 <spec> <trace> # Validate trace"
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
