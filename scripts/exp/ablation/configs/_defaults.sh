# Default experiment configuration.
# Sourced by all config files. Override values as needed.

ABLATION_ID=""
ABLATION_GROUP=""       # "ablation" or "baseline"
ABLATION_DESC=""

# Agent settings
MAX_BUDGET="${MAX_BUDGET:-0}"   # 0 = unlimited (can be overridden by CLI), in USD
AGENT="claude-code"

# ── Single-phase mode (baselines) ──
# PROMPT_TEMPLATE: filename under prompts/ for a single agent call
PROMPT_TEMPLATE=""

# ── Multi-phase mode (Specula pipeline) ──
# When MULTI_PHASE=true, PHASE_PROMPTS is used instead of PROMPT_TEMPLATE.
# Each entry is a prompt filename. Phases run sequentially in the same workspace,
# each as an independent agent call. Previous phases' outputs are visible as files.
MULTI_PHASE=false
PHASE_PROMPTS=()

# Skill isolation — controls which skills are visible in workspace .claude/skills/
SPECULA_SKILLS=("ALL")
TLAPLUS_SKILLS=()
MCP_TOOLS=true
