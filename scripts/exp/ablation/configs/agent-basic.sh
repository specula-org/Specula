# Baseline: agent loop with file tools, no TLA+ MCP, no Specula skills.
# Generic coding agent applied to TLA+ spec generation.

ABLATION_ID="agent-basic"
ABLATION_GROUP="baseline"
ABLATION_DESC="Agent loop with file/bash tools, no TLA+ tools, no methodology"
PROMPT_TEMPLATE="agent-basic.md"

SPECULA_SKILLS=()
TLAPLUS_SKILLS=()
MCP_TOOLS=false
