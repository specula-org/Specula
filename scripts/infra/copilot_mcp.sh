#!/usr/bin/env bash

# Copilot CLI MCP setup helpers. This file is sourced by setup.sh.

copilot_mcp_cli_available() {
  local config_dir="$1"
  local help_text

  if ! command -v copilot >/dev/null 2>&1; then
    return 1
  fi

  help_text="$(COPILOT_HOME="$config_dir" copilot mcp add --help 2>&1 || true)"
  grep -Eq '^Usage:[[:space:]]+copilot[[:space:]]+mcp[[:space:]]+add([[:space:]]|$)' <<< "$help_text"
}

copilot_mcp_config_status() {
  local config_json="$1"
  local mcp_name="$2"
  local project_root="$3"
  local python_path="$4"
  local server_path="$5"

  COPILOT_MCP_NAME="$mcp_name" \
    COPILOT_MCP_PROJECT_ROOT="$project_root" \
    COPILOT_MCP_PYTHON="$python_path" \
    COPILOT_MCP_SERVER="$server_path" \
    python3 -I -c '
import json
import os
import sys

try:
    payload = json.load(sys.stdin)
except (TypeError, ValueError):
    print("invalid")
    raise SystemExit(0)

name = os.environ["COPILOT_MCP_NAME"]
if not isinstance(payload, dict):
    print("invalid")
    raise SystemExit(0)

if "mcpServers" not in payload:
    print("absent")
    raise SystemExit(0)
servers = payload["mcpServers"]
if not isinstance(servers, dict):
    print("invalid")
    raise SystemExit(0)
if name not in servers:
    print("absent")
    raise SystemExit(0)
entry = servers[name]

if not isinstance(entry, dict):
    print("invalid")
    raise SystemExit(0)

source = str(entry.get("source") or "unknown").replace(":", "-").replace("\n", "-")
env = entry.get("env")
matches = (
    entry.get("command") == os.environ["COPILOT_MCP_PYTHON"]
    and entry.get("args") == [os.environ["COPILOT_MCP_SERVER"]]
    and entry.get("type") in (None, "local", "stdio")
    and entry.get("tools") in (None, ["*"])
    and isinstance(env, dict)
    and env.get("SPECULA_ROOT") == os.environ["COPILOT_MCP_PROJECT_ROOT"]
)
print(("match:" if matches else "conflict:") + source)
' <<< "$config_json"
}

copilot_user_mcp_config_status() {
  local config_dir="$1"
  local mcp_name="$2"
  local project_root="$3"
  local python_path="$4"
  local server_path="$5"
  local config_file="$config_dir/mcp-config.json"
  local config_json

  if [[ ! -e "$config_file" && ! -L "$config_file" ]]; then
    printf '%s\n' "absent"
    return 0
  fi
  if [[ ! -f "$config_file" || ! -r "$config_file" ]]; then
    printf '%s\n' "invalid"
    return 0
  fi
  if ! config_json="$(< "$config_file")"; then
    printf '%s\n' "invalid"
    return 0
  fi

  copilot_mcp_config_status \
    "$config_json" \
    "$mcp_name" \
    "$project_root" \
    "$python_path" \
    "$server_path"
}

print_copilot_mcp_add_command() {
  local config_dir="$1"
  local project_root="$2"
  local mcp_name="$3"
  local python_path="$4"
  local server_path="$5"

  printf '  COPILOT_HOME=%q copilot mcp add %q --env %q -- %q %q\n' \
    "$config_dir" \
    "$mcp_name" \
    "SPECULA_ROOT=$project_root" \
    "$python_path" \
    "$server_path"
}

setup_copilot_mcp_server() {
  local config_dir="$1"
  local project_root="$2"
  local mcp_name="$3"
  local python_path="$4"
  local server_path="$5"
  local config_status
  local add_output
  local add_rc

  print_status "Configuring $mcp_name MCP for GitHub Copilot CLI..."

  config_status="$(copilot_user_mcp_config_status \
    "$config_dir" \
    "$mcp_name" \
    "$project_root" \
    "$python_path" \
    "$server_path")"
  case "$config_status" in
    match:*)
      print_success "Copilot MCP already configured: $mcp_name (source: user)"
      return 0
      ;;
    conflict:*)
      print_warning "Copilot user MCP '$mcp_name' already exists and was left unchanged."
      print_status "Review or remove it in $config_dir/mcp-config.json before rerunning setup."
      return 0
      ;;
    invalid)
      print_warning "Copilot user MCP configuration at $config_dir/mcp-config.json could not be read safely and was left unchanged."
      return 0
      ;;
    absent)
      ;;
    *)
      print_warning "Copilot user MCP configuration at $config_dir/mcp-config.json was not recognized and was left unchanged."
      return 0
      ;;
  esac

  set +e
  add_output="$(COPILOT_HOME="$config_dir" copilot mcp add "$mcp_name" \
    --env "SPECULA_ROOT=$project_root" -- \
    "$python_path" \
    "$server_path" 2>&1)"
  add_rc=$?
  set -e

  if [[ $add_rc -eq 0 ]]; then
    print_success "Copilot MCP configured: $mcp_name"
    return 0
  fi

  print_warning "Copilot MCP auto-config failed for '$mcp_name'; existing configuration was not changed."
  if [[ -n "$add_output" ]]; then
    printf '  %s\n' "$add_output"
  fi
  print_status "Run manually after resolving the error:"
  print_copilot_mcp_add_command \
    "$config_dir" \
    "$project_root" \
    "$mcp_name" \
    "$python_path" \
    "$server_path"
}

setup_copilot_mcp_servers() {
  local config_dir="$1"
  local project_root="$2"
  shift 2
  local entry
  local mcp_name
  local mcp_python
  local mcp_server

  if ! copilot_mcp_cli_available "$config_dir"; then
    print_warning "Automatic Copilot MCP setup requires Copilot CLI 1.0.21 or newer; upgrade the CLI or configure the MCP servers manually."
    return 0
  fi

  for entry in "$@"; do
    IFS='|' read -r mcp_name mcp_python mcp_server <<< "$entry"
    setup_copilot_mcp_server \
      "$config_dir" \
      "$project_root" \
      "$mcp_name" \
      "$mcp_python" \
      "$mcp_server"
  done
}
