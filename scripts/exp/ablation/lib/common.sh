#!/usr/bin/env bash
#
# Shared utilities for ablation experiments.
#
# Sourced by run.sh and eval scripts. Do not execute directly.

ABLATION_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SPECULA_ROOT="$(cd "$ABLATION_DIR/../../.." && pwd)"
CASE_STUDIES_DIR="$SPECULA_ROOT/case-studies"
ADAPTER_DIR="$SPECULA_ROOT/scripts/launch/adapters"
RESULTS_BASE_DIR="$ABLATION_DIR/results"

# ── Logging ──

log()  { echo "[$(date '+%H:%M:%S')] $*"; }
warn() { echo "[$(date '+%H:%M:%S')] WARN: $*" >&2; }
die()  { echo "[$(date '+%H:%M:%S')] ERROR: $*" >&2; exit 1; }

# ── Target parsing ──
#
# Target format: "name|github|lang|reference"
# Example: "etcd-raft|etcd-io/raft|Go|Raft (Ongaro 2014)"

parse_target() {
  local target="$1"
  IFS='|' read -r TARGET_NAME TARGET_GITHUB TARGET_LANG TARGET_REFERENCE <<< "$target"
  TARGET_NAME="$(echo "$TARGET_NAME" | xargs)"
  export TARGET_NAME TARGET_GITHUB TARGET_LANG TARGET_REFERENCE
}

# ── Artifact lookup ──

find_artifact_repo() {
  local name="$1"
  local artifact_dir="${CASE_STUDIES_DIR}/${name}/artifact"
  [[ -d "$artifact_dir" ]] || return
  for d in "$artifact_dir"/*/; do
    if [[ -d "${d}.git" || -f "${d}.git" ]]; then
      echo "$d"
      return
    fi
  done
}

# ── Workspace setup ──
#
# Creates an isolated workspace for one experiment run:
#   <results_dir>/<run_id>/<config_id>/<target_name>/
#     ├── .git/                (standalone git repo for Claude Code isolation)
#     ├── .claude/
#     │   ├── skills/          (symlinks to allowed skills only)
#     │   └── settings.json    (MCP tools config, if enabled)
#     ├── artifact/<repo> -> symlink
#     ├── spec/
#     ├── prompt.md
#     ├── agent.log
#     └── meta.json

create_workspace() {
  local run_id="$1" config_id="$2" target_name="$3"
  local ws="${RESULTS_BASE_DIR}/${run_id}/${config_id}/${target_name}"
  mkdir -p "$ws/spec" "$ws/artifact"
  echo "$ws"
}

# Initialize workspace as isolated Claude Code project.
# Must be called AFTER load_config sets SPECULA_SKILLS, TLAPLUS_SKILLS, MCP_TOOLS.
init_workspace_isolation() {
  local workspace="$1"

  # ── git init so Claude Code treats workspace as project root ──
  git init -q "$workspace" 2>/dev/null || true

  # ── .claude/skills/ — symlink only the allowed skills ──
  local skills_dir="$workspace/.claude/skills"
  mkdir -p "$skills_dir"

  local specula_skills_src="$SPECULA_ROOT/.claude/skills"
  local tlaplus_skills_src="$SPECULA_ROOT/tools/tlaplus-ai-tools/skills"

  # Specula skills
  if [[ ${#SPECULA_SKILLS[@]} -gt 0 ]]; then
    if [[ "${SPECULA_SKILLS[0]}" == "ALL" ]]; then
      for d in "$specula_skills_src"/*/; do
        [[ -d "$d" ]] && ln -sfn "$d" "$skills_dir/$(basename "$d")"
      done
      # Also link workflow-overview.md if it exists
      [[ -f "$specula_skills_src/workflow-overview.md" ]] && \
        ln -sfn "$specula_skills_src/workflow-overview.md" "$skills_dir/workflow-overview.md"
    else
      for name in "${SPECULA_SKILLS[@]}"; do
        [[ -d "$specula_skills_src/$name" ]] && \
          ln -sfn "$specula_skills_src/$name" "$skills_dir/$name"
      done
    fi
  fi

  # TLA+ community skills (from tlaplus-ai-tools)
  if [[ ${#TLAPLUS_SKILLS[@]} -gt 0 ]]; then
    if [[ "${TLAPLUS_SKILLS[0]}" == "ALL" ]]; then
      for d in "$tlaplus_skills_src"/*/; do
        [[ -d "$d" ]] && ln -sfn "$d" "$skills_dir/$(basename "$d")"
      done
    else
      for name in "${TLAPLUS_SKILLS[@]}"; do
        [[ -d "$tlaplus_skills_src/$name" ]] && \
          ln -sfn "$tlaplus_skills_src/$name" "$skills_dir/$name"
      done
    fi
  fi

  local skill_count
  skill_count=$(find "$skills_dir" -mindepth 1 -maxdepth 1 | wc -l)
  log "Skills: $skill_count installed in workspace"

  # ── .claude/settings.json — MCP tools config ──
  if $MCP_TOOLS; then
    # Copy MCP server definitions from project settings, plus auto-approve
    python3 -c "
import json, os

# Read project settings to extract MCP config
proj_settings = '$SPECULA_ROOT/.claude/settings.local.json'
mcp_config = {}
if os.path.exists(proj_settings):
    with open(proj_settings) as f:
        d = json.load(f)
    if d.get('enableAllProjectMcpServers'):
        mcp_config['enableAllProjectMcpServers'] = True
    if d.get('enabledMcpjsonServers'):
        mcp_config['enabledMcpjsonServers'] = d['enabledMcpjsonServers']

# Also copy mcpServers if defined
mcp_json = os.path.join('$SPECULA_ROOT', '.mcp.json')
if os.path.exists(mcp_json):
    os.symlink(mcp_json, os.path.join('$workspace', '.mcp.json'))

# Auto-approve all tool calls for unattended runs
mcp_config['permissions'] = {
    'allow': [
        'Bash(*)',
        'Read(*)',
        'Edit(*)',
        'Write(*)',
        'Glob(*)',
        'Grep(*)',
        'mcp__tla-trace-debugger__*',
        'mcp__tlc-output-reader__*',
        'mcp__tla-spec-analyzer__*',
        'Skill(*)',
        'WebFetch(*)',
        'WebSearch(*)'
    ],
    'deny': []
}

settings_path = os.path.join('$workspace', '.claude', 'settings.local.json')
with open(settings_path, 'w') as f:
    json.dump(mcp_config, f, indent=2)
" 2>/dev/null
    log "MCP tools: enabled"
  else
    # No MCP tools — just auto-approve basic tools
    cat > "$workspace/.claude/settings.local.json" <<'SETTINGS'
{
  "permissions": {
    "allow": ["Bash(*)", "Read(*)", "Edit(*)", "Write(*)", "Glob(*)", "Grep(*)"],
    "deny": []
  }
}
SETTINGS
    log "MCP tools: disabled"
  fi
}

link_artifact() {
  local workspace="$1" source_repo="$2"
  local repo_name
  repo_name="$(basename "$source_repo")"
  # Remove trailing slash
  source_repo="${source_repo%/}"
  ln -sfn "$source_repo" "$workspace/artifact/$repo_name"
  echo "$workspace/artifact/$repo_name"
}

# ── Metadata ──

write_metadata() {
  local workspace="$1"
  shift
  # Remaining args are key=value pairs
  local json="{"
  local first=true
  while [[ $# -gt 0 ]]; do
    local key="${1%%=*}" val="${1#*=}"
    $first || json+=","
    json+="\"$key\":\"$val\""
    first=false
    shift
  done
  json+="}"
  echo "$json" > "$workspace/meta.json"
}

# ── Config loading ──

load_config() {
  local config_path="$1"
  [[ -f "$config_path" ]] || die "Config not found: $config_path"

  # Load defaults first
  source "$ABLATION_DIR/configs/_defaults.sh"
  # Then load the specific config (overrides defaults)
  source "$config_path"

  # Validate required fields
  [[ -n "$ABLATION_ID" ]]    || die "Config missing ABLATION_ID"
  [[ -n "$ABLATION_GROUP" ]] || die "Config missing ABLATION_GROUP"

  if $MULTI_PHASE; then
    (( ${#PHASE_PROMPTS[@]} > 0 )) || die "Multi-phase config requires PHASE_PROMPTS"
  else
    [[ -n "$PROMPT_TEMPLATE" ]] || die "Single-phase config requires PROMPT_TEMPLATE"
  fi
}
