#!/usr/bin/env bash
#
# Prompt generation utilities for ablation experiments.
#
# Reads a prompt template and substitutes variables.
# Sourced by run.sh. Do not execute directly.

# ── Prompt rendering ──
#
# Templates use ${VAR} syntax. Available variables:
#
#   TARGET_NAME, TARGET_GITHUB, TARGET_LANG, TARGET_REFERENCE
#   WORKSPACE_DIR, REPO_DIR, SPEC_DIR
#   SPECULAR_ROOT
#   SKILL_DIR_ANALYSIS, SKILL_DIR_SPECGEN, SKILL_DIR_HARNESS
#   SKILL_DIR_TRACE, SKILL_DIR_CHECKING

render_prompt() {
  local template_path="$1"
  [[ -f "$template_path" ]] || die "Prompt template not found: $template_path"

  # Export all variables needed by envsubst
  export WORKSPACE_DIR REPO_DIR SPEC_DIR SPECULAR_ROOT
  export TARGET_NAME TARGET_GITHUB TARGET_LANG TARGET_REFERENCE
  export SKILL_DIR_ANALYSIS="$SPECULAR_ROOT/.claude/skills/code_analysis"
  export SKILL_DIR_SPECGEN="$SPECULAR_ROOT/.claude/skills/spec_generation"
  export SKILL_DIR_HARNESS="$SPECULAR_ROOT/.claude/skills/harness-generation"
  export SKILL_DIR_TRACE="$SPECULAR_ROOT/.claude/skills/tla-trace-workflow"
  export SKILL_DIR_CHECKING="$SPECULAR_ROOT/.claude/skills/tla-checking-workflow"
  export TLA2TOOLS_JAR="$SPECULAR_ROOT/lib/tla2tools.jar"
  export COMMUNITY_JAR="$SPECULAR_ROOT/lib/CommunityModules-deps.jar"
  export TLAPLUS_AI_TOOLS_DIR="$SPECULAR_ROOT/tools/tlaplus-ai-tools"
  export SYSMOBENCH_DIR="$SPECULAR_ROOT/tools/SysMoBench"

  envsubst < "$template_path"
}
