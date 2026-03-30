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
#   SPECULA_ROOT
#   SKILL_DIR_ANALYSIS, SKILL_DIR_SPECGEN, SKILL_DIR_HARNESS
#   SKILL_DIR_TRACE, SKILL_DIR_CHECKING

render_prompt() {
  local template_path="$1"
  [[ -f "$template_path" ]] || die "Prompt template not found: $template_path"

  # Export all variables needed by envsubst
  export WORKSPACE_DIR REPO_DIR SPEC_DIR SPECULA_ROOT
  export TARGET_NAME TARGET_GITHUB TARGET_LANG TARGET_REFERENCE
  export SKILL_DIR_ANALYSIS="$SPECULA_ROOT/.claude/skills/code_analysis"
  export SKILL_DIR_SPECGEN="$SPECULA_ROOT/.claude/skills/spec_generation"
  export SKILL_DIR_HARNESS="$SPECULA_ROOT/.claude/skills/harness-generation"
  export SKILL_DIR_TRACE="$SPECULA_ROOT/.claude/skills/tla-trace-workflow"
  export SKILL_DIR_CHECKING="$SPECULA_ROOT/.claude/skills/tla-checking-workflow"
  export TLA2TOOLS_JAR="$SPECULA_ROOT/lib/tla2tools.jar"
  export COMMUNITY_JAR="$SPECULA_ROOT/lib/CommunityModules-deps.jar"
  export TLAPLUS_AI_TOOLS_DIR="$SPECULA_ROOT/tools/tlaplus-ai-tools"
  export SYSMOBENCH_DIR="$SPECULA_ROOT/tools/SysMoBench"

  envsubst < "$template_path"
}
