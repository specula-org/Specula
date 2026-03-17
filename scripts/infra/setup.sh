#!/usr/bin/env bash

# Specula setup script (agent skills + trace debugger MCP + TLA+ jars)

set -euo pipefail

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

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

command_exists() {
  command -v "$1" >/dev/null 2>&1
}

setup_skills_root_symlink() {
  local target_link="$1"
  local skills_source="$2"
  local parent_dir
  local existing_target

  parent_dir="$(dirname "$target_link")"
  mkdir -p "$parent_dir"

  if [[ -L "$target_link" ]]; then
    existing_target="$(readlink "$target_link" || true)"
    if [[ "$existing_target" == "$skills_source" ]]; then
      print_success "Skills symlink already configured: $target_link -> $skills_source"
      return 0
    fi
    rm -f "$target_link"
  elif [[ -e "$target_link" ]]; then
    print_warning "Skipping $target_link (exists and is not a symlink)"
    return 0
  fi

  ln -s "$skills_source" "$target_link"
  print_success "Skills configured: $target_link -> $skills_source"
}

setup_claude_mcp() {
  local project_root="$1"
  local python_path="$2"
  local server_path="$3"

  print_status "Configuring tracedebugger MCP for Claude Code..."
  set +e
  claude mcp add --transport stdio --scope project \
    --env "SPECULA_ROOT=$project_root" \
    tracedebugger -- \
    "$python_path" \
    "$server_path"
  local rc=$?
  set -e

  if [[ $rc -eq 0 ]]; then
    print_success "Claude MCP configured: tracedebugger"
  else
    print_warning "Claude MCP auto-config failed. Run manually:"
    echo "  claude mcp add --transport stdio --scope project --env SPECULA_ROOT=$project_root tracedebugger -- $python_path $server_path"
  fi
}

setup_codex_mcp() {
  local project_root="$1"
  local python_path="$2"
  local server_path="$3"

  print_status "Configuring tracedebugger MCP for Codex..."
  set +e
  codex mcp add tracedebugger \
    --env "SPECULA_ROOT=$project_root" -- \
    "$python_path" \
    "$server_path"
  local rc=$?
  set -e

  if [[ $rc -eq 0 ]]; then
    print_success "Codex MCP configured: tracedebugger"
  else
    print_warning "Codex MCP auto-config failed. Run manually:"
    echo "  codex mcp add tracedebugger --env SPECULA_ROOT=$project_root -- $python_path $server_path"
  fi
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
TRACE_DEBUGGER_DIR="$PROJECT_ROOT/tools/trace_debugger"
TRACE_DEBUGGER_VENV="$TRACE_DEBUGGER_DIR/.venv"
TRACE_DEBUGGER_PYTHON="$TRACE_DEBUGGER_VENV/bin/python"
TRACE_DEBUGGER_SERVER="$TRACE_DEBUGGER_DIR/mcp_server.py"
SKILLS_SOURCE="$PROJECT_ROOT/src/skills"
CLAUDE_PROJECT_SKILLS_LINK="$PROJECT_ROOT/.claude/skills"
CODEX_PROJECT_SKILLS_LINK="$PROJECT_ROOT/.agents/skills"

print_status "Project root: $PROJECT_ROOT"

if ! command_exists python3; then
  print_error "Python 3 is required but not found"
  exit 1
fi
print_success "Python found: $(python3 --version 2>&1)"

if ! command_exists java; then
  print_error "Java is required but not found"
  exit 1
fi
print_success "Java found: $(java -version 2>&1 | head -n1)"

if ! command_exists pip3; then
  print_error "pip3 is required but not found"
  exit 1
fi
print_success "pip3 found"

mkdir -p "$PROJECT_ROOT/lib"

print_status "Setting up TLA+ jars..."

if [[ ! -f "$PROJECT_ROOT/lib/tla2tools.jar" ]]; then
  TLA_TOOLS_URL="https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar"
  print_status "Downloading tla2tools.jar..."
  if command_exists wget; then
    wget -O "$PROJECT_ROOT/lib/tla2tools.jar" "$TLA_TOOLS_URL"
  elif command_exists curl; then
    curl -L -o "$PROJECT_ROOT/lib/tla2tools.jar" "$TLA_TOOLS_URL"
  else
    print_error "Need wget or curl to download tla2tools.jar"
    exit 1
  fi
  print_success "Downloaded tla2tools.jar"
else
  print_success "tla2tools.jar already exists"
fi

if [[ ! -f "$PROJECT_ROOT/lib/CommunityModules-deps.jar" ]]; then
  COMMUNITY_MODULES_URL="https://github.com/tlaplus/CommunityModules/releases/download/202505152026/CommunityModules-deps.jar"
  print_status "Downloading CommunityModules-deps.jar..."
  if command_exists wget; then
    wget -O "$PROJECT_ROOT/lib/CommunityModules-deps.jar" "$COMMUNITY_MODULES_URL"
  elif command_exists curl; then
    curl -L -o "$PROJECT_ROOT/lib/CommunityModules-deps.jar" "$COMMUNITY_MODULES_URL"
  else
    print_error "Need wget or curl to download CommunityModules-deps.jar"
    exit 1
  fi
  print_success "Downloaded CommunityModules-deps.jar"
else
  print_success "CommunityModules-deps.jar already exists"
fi

_tlc_out="$(java -cp "$PROJECT_ROOT/lib/tla2tools.jar" tlc2.TLC -help 2>&1 || true)"
if echo "$_tlc_out" | grep -q "TLA+"; then
  print_success "TLA+ tool invocation verified"
else
  print_warning "TLA+ verification command failed; check your Java/JAR setup"
fi

if [[ ! -d "$TRACE_DEBUGGER_DIR" ]]; then
  print_error "Trace debugger directory not found: $TRACE_DEBUGGER_DIR"
  exit 1
fi

print_status "Setting up trace debugger Python environment..."
python3 -m venv "$TRACE_DEBUGGER_VENV"
"$TRACE_DEBUGGER_PYTHON" -m pip install --upgrade pip
"$TRACE_DEBUGGER_PYTHON" -m pip install -r "$TRACE_DEBUGGER_DIR/requirements.txt"
print_success "Trace debugger dependencies installed"

if [[ ! -d "$SKILLS_SOURCE" ]]; then
  print_error "Skills directory not found: $SKILLS_SOURCE"
  exit 1
fi

setup_skills_root_symlink "$CLAUDE_PROJECT_SKILLS_LINK" "$SKILLS_SOURCE"
setup_skills_root_symlink "$CODEX_PROJECT_SKILLS_LINK" "$SKILLS_SOURCE"

if command_exists claude; then
  setup_claude_mcp "$PROJECT_ROOT" "$TRACE_DEBUGGER_PYTHON" "$TRACE_DEBUGGER_SERVER"
else
  print_warning "Claude CLI not found; skipping Claude MCP setup"
fi

if command_exists codex; then
  setup_codex_mcp "$PROJECT_ROOT" "$TRACE_DEBUGGER_PYTHON" "$TRACE_DEBUGGER_SERVER"
else
  print_warning "Codex CLI not found; skipping Codex MCP setup"
fi

if ! command_exists claude && ! command_exists codex; then
  print_warning "No supported agent CLI found. Configure skills and MCP manually after installing Claude Code or Codex."
fi

print_success "Setup completed."
print_status "Trace debugger Python: $TRACE_DEBUGGER_PYTHON"
print_status "Trace debugger server: $TRACE_DEBUGGER_SERVER"
