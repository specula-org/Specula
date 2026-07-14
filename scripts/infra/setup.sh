#!/usr/bin/env bash

# Specula setup script (agent skills + MCP tools + TLA+ jars)

set -euo pipefail

usage() {
  cat <<'EOF'
Usage:
  specula setup

Install Specula's TLA+ tools, Python environments, agent skills, and MCP integrations.

This interactive command may download dependencies, build local tools, and
update agent configuration.

Options:
  -h, --help  Show this help and exit
EOF
}

if (( $# == 0 )); then
  :
elif (( $# == 1 )) && [[ "$1" == "-h" || "$1" == "--help" ]]; then
  usage
  exit 0
else
  unexpected="$1"
  if [[ "$unexpected" == "-h" || "$unexpected" == "--help" ]]; then
    unexpected="$2"
  fi
  printf "specula setup: unexpected argument '%s'\n\n" "$unexpected" >&2
  usage >&2
  exit 2
fi

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'
SKILL_SETUP_INCOMPLETE=false

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

# Prompt user with a yes/no question. Returns 0 for yes, 1 for no.
ask_yn() {
  local prompt="$1"
  local answer
  while true; do
    read -rp "$(echo -e "${BLUE}[?]${NC} ${prompt} (y/n): ")" answer
    case "$answer" in
      [Yy]|[Yy][Ee][Ss]) return 0 ;;
      [Nn]|[Nn][Oo]) return 1 ;;
      *) echo "  Please answer y or n." ;;
    esac
  done
}

# Prompt user to choose global or local install. Prints "global" or "local".
ask_scope() {
  local agent_name="$1"
  local answer
  while true; do
    read -rp "$(echo -e "${BLUE}[?]${NC} Install ${agent_name} skills globally (all projects) or locally (this Specula checkout only)? (global/local): ")" answer
    case "$answer" in
      [Gg]|[Gg][Ll][Oo][Bb][Aa][Ll]) echo "global"; return 0 ;;
      [Ll]|[Ll][Oo][Cc][Aa][Ll]) echo "local"; return 0 ;;
      *) echo "  Please answer global or local." ;;
    esac
  done
}

ask_codex_install() {
  local answer
  while true; do
    read -rp "$(echo -e "${BLUE}[?]${NC} Install Specula for Codex? (y/n/plugin): ")" answer
    case "$answer" in
      [Yy]|[Yy][Ee][Ss]) echo "legacy"; return 0 ;;
      [Nn]|[Nn][Oo]) echo "skip"; return 0 ;;
      [Pp]|[Pp][Ll][Uu][Gg][Ii][Nn]) echo "plugin"; return 0 ;;
      *) echo "  Please answer y, n, or plugin." >&2 ;;
    esac
  done
}

setup_skills() {
  local target_dir="$1"
  local skills_source="$2"
  shift 2
  local -a install_args=(
    --source "$skills_source"
    --target "$target_dir"
  )

  install_args+=("$@")

  print_status "Installing Specula skills into $target_dir..."
  # Isolated mode keeps the caller's CWD and PYTHONPATH from shadowing trusted setup code.
  if python3 -I "$PROJECT_ROOT/src/specula/skill_install.py" "${install_args[@]}"; then
    print_success "Skills configured in $target_dir"
  else
    SKILL_SETUP_INCOMPLETE=true
    print_warning "Specula skill installation is incomplete in $target_dir"
  fi
}

warn_local_skills_scope() {
  print_warning "Local skills are discoverable only when the agent starts in $PROJECT_ROOT or one of its subdirectories."
}

setup_claude_mcp() {
  local project_root="$1"
  local mcp_name="$2"
  local python_path="$3"
  local server_path="$4"
  local scope="$5"

  print_status "Configuring $mcp_name MCP for Claude Code (scope: $scope)..."
  set +e
  CLAUDE_CONFIG_DIR="$CLAUDE_USER_CONFIG_DIR" claude mcp add --transport stdio --scope "$scope" \
    "$mcp_name" \
    --env "SPECULA_ROOT=$project_root" \
    -- \
    "$python_path" \
    "$server_path"
  local rc=$?
  set -e

  if [[ $rc -eq 0 ]]; then
    print_success "Claude MCP configured: $mcp_name (scope: $scope)"
  else
    print_warning "Claude MCP auto-config failed. Run manually:"
    echo "  CLAUDE_CONFIG_DIR=$CLAUDE_USER_CONFIG_DIR claude mcp add --transport stdio --scope $scope --env SPECULA_ROOT=$project_root $mcp_name -- $python_path $server_path"
  fi
}

setup_codex_mcp() {
  local project_root="$1"
  local mcp_name="$2"
  local python_path="$3"
  local server_path="$4"

  print_status "Configuring $mcp_name MCP for Codex..."
  set +e
  codex mcp add "$mcp_name" \
    --env "SPECULA_ROOT=$project_root" -- \
    "$python_path" \
    "$server_path"
  local rc=$?
  set -e

  if [[ $rc -eq 0 ]]; then
    print_success "Codex MCP configured: $mcp_name"
  else
    print_warning "Codex MCP auto-config failed. Run manually:"
    echo "  codex mcp add $mcp_name --env SPECULA_ROOT=$project_root -- $python_path $server_path"
  fi
}

setup_codex_plugin() {
  local project_root="$1"
  local plugin_root="$2"

  print_status "Generating Specula Codex plugin..."
  python3 -I "$SCRIPT_DIR/setup_codex_plugin.py" \
    --project-root "$project_root" \
    --plugin-root "$plugin_root"
  print_success "Codex plugin configured: specula-codex@specula"
  print_status "Rerun this setup script and choose 'plugin' to update the Codex plugin."
}

setup_python_tool_env() {
  local tool_name="$1"
  local tool_dir="$2"
  local venv_dir="$3"
  local python_path="$4"
  local requirements_file="${5:-}"

  if [[ ! -d "$tool_dir" ]]; then
    print_error "$tool_name directory not found: $tool_dir"
    exit 1
  fi

  print_status "Setting up $tool_name Python environment..."
  python3 -I -m venv "$venv_dir"
  "$python_path" -I -m pip install --upgrade pip

  if [[ -n "$requirements_file" && -f "$requirements_file" ]]; then
    "$python_path" -I -m pip install -r "$requirements_file"
  else
    "$python_path" -I -m pip install mcp
  fi

  print_success "$tool_name dependencies installed"
}

build_cfa_jar() {
  local project_root="$1"
  local cfa_dir="$2"

  if [[ ! -d "$cfa_dir" ]]; then
    print_error "CFA tool directory not found: $cfa_dir"
    exit 1
  fi

  if ! command_exists mvn; then
    print_error "mvn is required to build the CFA jar for spec_analyzer"
    exit 1
  fi

  print_status "Building CFA jar for spec_analyzer..."
  (
    cd "$cfa_dir"
    mvn package -DskipTests
  )
  print_success "CFA jar built"
}

# ─── Main ────────────────────────────────────────────────────────────────────

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
# Run the remaining setup from the trusted checkout rather than the caller's directory.
cd "$PROJECT_ROOT"
TRACE_DEBUGGER_DIR="$PROJECT_ROOT/tools/trace_debugger"
TRACE_DEBUGGER_VENV="$TRACE_DEBUGGER_DIR/.venv"
TRACE_DEBUGGER_PYTHON="$TRACE_DEBUGGER_VENV/bin/python"
TRACE_DEBUGGER_SERVER="$TRACE_DEBUGGER_DIR/mcp_server.py"
TOOLS_CFA_DIR="$PROJECT_ROOT/tools/cfa"
SPEC_ANALYZER_DIR="$PROJECT_ROOT/tools/spec_analyzer"
SPEC_ANALYZER_VENV="$SPEC_ANALYZER_DIR/.venv"
SPEC_ANALYZER_PYTHON="$SPEC_ANALYZER_VENV/bin/python"
SPEC_ANALYZER_SERVER="$SPEC_ANALYZER_DIR/mcp_server.py"
INV_CHECKING_TOOL_DIR="$PROJECT_ROOT/tools/inv_checking_tool"
INV_CHECKING_TOOL_VENV="$INV_CHECKING_TOOL_DIR/.venv"
INV_CHECKING_TOOL_PYTHON="$INV_CHECKING_TOOL_VENV/bin/python"
INV_CHECKING_TOOL_SERVER="$INV_CHECKING_TOOL_DIR/mcp_server.py"
SKILLS_SOURCE="$PROJECT_ROOT/skills"
CODEX_PLUGIN_ROOT="$PROJECT_ROOT/.specula-codex"
# Match the launcher's --claude-alias contract exactly: NAME uses ~/.NAME.
CLAUDE_USER_CONFIG_DIR="$HOME/.${CLAUDE_ALIAS:-claude}"
COPILOT_USER_CONFIG_DIR="${COPILOT_HOME:-$HOME/.copilot}"

print_status "Project root: $PROJECT_ROOT"

# ─── Prerequisites ───────────────────────────────────────────────────────────

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

# ─── TLA+ JARs ──────────────────────────────────────────────────────────────

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

# ─── Python tool environments ────────────────────────────────────────────────

setup_python_tool_env \
  "trace debugger" \
  "$TRACE_DEBUGGER_DIR" \
  "$TRACE_DEBUGGER_VENV" \
  "$TRACE_DEBUGGER_PYTHON" \
  "$TRACE_DEBUGGER_DIR/requirements.txt"

build_cfa_jar "$PROJECT_ROOT" "$TOOLS_CFA_DIR"

setup_python_tool_env \
  "spec analyzer" \
  "$SPEC_ANALYZER_DIR" \
  "$SPEC_ANALYZER_VENV" \
  "$SPEC_ANALYZER_PYTHON" \
  "$SPEC_ANALYZER_DIR/requirements.txt"

setup_python_tool_env \
  "invariant checking tool" \
  "$INV_CHECKING_TOOL_DIR" \
  "$INV_CHECKING_TOOL_VENV" \
  "$INV_CHECKING_TOOL_PYTHON"

# ─── Skills directory check ──────────────────────────────────────────────────

if [[ ! -d "$SKILLS_SOURCE" ]]; then
  print_error "Skills directory not found: $SKILLS_SOURCE"
  exit 1
fi

# ─── Agent setup (interactive) ───────────────────────────────────────────────

echo ""
print_status "Agent configuration"
echo ""

# MCP server list (name, python path, server path)
MCP_SERVERS=(
  "tracedebugger|$TRACE_DEBUGGER_PYTHON|$TRACE_DEBUGGER_SERVER"
  "spec_analyzer|$SPEC_ANALYZER_PYTHON|$SPEC_ANALYZER_SERVER"
  "inv_checking_tool|$INV_CHECKING_TOOL_PYTHON|$INV_CHECKING_TOOL_SERVER"
)

# --- Claude Code ---
echo -e "${BLUE}[1/3] Claude Code${NC}"
if ask_yn "Install Specula for Claude Code?"; then
  scope="$(ask_scope "Claude Code")"
  if [[ "$scope" == "global" ]]; then
    setup_skills "$CLAUDE_USER_CONFIG_DIR/skills" "$SKILLS_SOURCE"
    for entry in "${MCP_SERVERS[@]}"; do
      IFS='|' read -r mcp_name mcp_python mcp_server <<< "$entry"
      setup_claude_mcp "$PROJECT_ROOT" "$mcp_name" "$mcp_python" "$mcp_server" "user"
    done
  else
    setup_skills \
      "$PROJECT_ROOT/.claude/skills" \
      "$SKILLS_SOURCE" \
      --shadow-root "$CLAUDE_USER_CONFIG_DIR/skills"
    warn_local_skills_scope
    for entry in "${MCP_SERVERS[@]}"; do
      IFS='|' read -r mcp_name mcp_python mcp_server <<< "$entry"
      setup_claude_mcp "$PROJECT_ROOT" "$mcp_name" "$mcp_python" "$mcp_server" "project"
    done
  fi
else
  print_status "Skipped Claude Code."
fi
echo ""

# --- Codex ---
echo -e "${BLUE}[2/3] Codex${NC}"
codex_install="$(ask_codex_install)"
case "$codex_install" in
  legacy)
    scope="$(ask_scope "Codex")"
    if [[ "$scope" == "global" ]]; then
      setup_skills "$HOME/.agents/skills" "$SKILLS_SOURCE" --legacy-root "$HOME/.codex/skills"
    else
      setup_skills "$PROJECT_ROOT/.agents/skills" "$SKILLS_SOURCE"
      warn_local_skills_scope
    fi
    for entry in "${MCP_SERVERS[@]}"; do
      IFS='|' read -r mcp_name mcp_python mcp_server <<< "$entry"
      setup_codex_mcp "$PROJECT_ROOT" "$mcp_name" "$mcp_python" "$mcp_server"
    done
    ;;
  plugin)
    setup_codex_plugin "$PROJECT_ROOT" "$CODEX_PLUGIN_ROOT"
    ;;
  skip)
    print_status "Skipped Codex."
    ;;
esac
echo ""

# --- Copilot CLI ---
echo -e "${BLUE}[3/3] GitHub Copilot CLI${NC}"
if ask_yn "Install Specula for GitHub Copilot CLI?"; then
  scope="$(ask_scope "Copilot CLI")"
  if [[ "$scope" == "global" ]]; then
    setup_skills \
      "$HOME/.agents/skills" \
      "$SKILLS_SOURCE" \
      --legacy-root "$HOME/.github/skills" \
      --shadow-root "$COPILOT_USER_CONFIG_DIR/skills"
  else
    setup_skills "$PROJECT_ROOT/.github/skills" "$SKILLS_SOURCE"
    warn_local_skills_scope
  fi
  print_warning "Copilot CLI MCP must be configured manually. See README for details."
else
  print_status "Skipped Copilot CLI."
fi
echo ""

# ─── Done ────────────────────────────────────────────────────────────────────

if [[ "$SKILL_SETUP_INCOMPLETE" == true ]]; then
  print_warning "Setup completed with an incomplete Specula skill installation."
  setup_rc=1
else
  print_success "Setup completed."
  setup_rc=0
fi
print_status "Trace debugger Python: $TRACE_DEBUGGER_PYTHON"
print_status "Trace debugger server: $TRACE_DEBUGGER_SERVER"
print_status "Spec analyzer Python: $SPEC_ANALYZER_PYTHON"
print_status "Spec analyzer server: $SPEC_ANALYZER_SERVER"
print_status "Invariant checking tool Python: $INV_CHECKING_TOOL_PYTHON"
print_status "Invariant checking tool server: $INV_CHECKING_TOOL_SERVER"
exit "$setup_rc"
