#!/bin/bash

# TLA+ RAG Error Correction System Environment Setup Script

set -e

echo "[INFO] Starting TLA+ RAG Error Correction System environment setup..."

# Color definitions
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Check Python version
echo "[CHECK] Checking Python version..."
python_version=$(python3 --version 2>&1 | awk '{print $2}')
echo "        Python version: $python_version"

if ! python3 -c "import sys; exit(0 if sys.version_info >= (3, 8) else 1)" 2>/dev/null; then
    echo -e "${RED}[ERROR] Python 3.8 or higher is required${NC}"
    exit 1
fi

# Check pip
if ! command -v pip3 &> /dev/null; then
    echo -e "${RED}[ERROR] pip3 is not installed${NC}"
    exit 1
fi

# Install Python dependencies
echo "[INSTALL] Installing Python dependencies..."
pip3 install -r requirements.txt

# Check TLA+ tools
echo "[CHECK] Checking TLA+ tools..."
if ! command -v tla_sany &> /dev/null; then
    echo -e "${YELLOW}[WARNING] TLA+ SANY tools not found${NC}"
    echo "Please install TLA+ tools following these steps:"
    echo "1. Download TLA+ tools: https://github.com/tlaplus/tlaplus/releases"
    echo "2. Extract and add to PATH environment variable"
    echo "3. Or use package manager (e.g., apt install tla-plus-tools)"
    
    read -p "Continue with other setup steps? (y/n): " -n 1 -r
    echo
    if [[ ! $REPLY =~ ^[Yy]$ ]]; then
        exit 1
    fi
else
    # Test if tla_sany actually works
    if tla_sany -help &> /dev/null; then
        echo -e "${GREEN}[OK] TLA+ SANY tools installed and working${NC}"
    else
        echo -e "${YELLOW}[WARNING] TLA+ SANY tools found but may not be working properly${NC}"
    fi
fi

# Check environment variables
echo "[CHECK] Checking environment variables..."
if [ -z "$DEEPSEEK_API_KEY" ]; then
    echo -e "${YELLOW}[WARNING] DEEPSEEK_API_KEY environment variable not set${NC}"
    echo "Please set your DeepSeek API key:"
    echo "export DEEPSEEK_API_KEY=your_api_key_here"
    echo ""
    echo "You can add this line to ~/.bashrc or ~/.zshrc for permanent storage"
else
    echo -e "${GREEN}[OK] DEEPSEEK_API_KEY is set${NC}"
fi

# Create necessary directories
echo "[CREATE] Creating necessary directories..."
mkdir -p output
mkdir -p logs
mkdir -p temp

# Check configuration file
echo "[CHECK] Checking configuration file..."
if [ ! -f "config.yaml" ]; then
    echo -e "${YELLOW}[WARNING] config.yaml does not exist, default configuration should be created${NC}"
    # config.yaml should already exist, if not, prompt user
fi

# Run environment check
echo "[TEST] Running environment check..."
python3 main.py --check-env

echo ""
echo -e "${GREEN}[SUCCESS] Environment setup completed!${NC}"
echo ""
echo "Usage:"
echo "  Simple correction mode:"
echo "    python3 main.py --input input.yaml --output ./output --mode simple"
echo ""
echo "  Experimental comparison mode:"
echo "    python3 main.py --input input.yaml --output ./output --mode experiments"
echo ""
echo "  View help:"
echo "    python3 main.py --help"
echo ""
echo "Notes:"
echo "  1. Make sure DEEPSEEK_API_KEY environment variable is set"
echo "  2. Input file must be in YAML format"
echo "  3. Ensure TLA+ tools are properly installed"
