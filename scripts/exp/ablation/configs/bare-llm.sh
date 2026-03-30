# Baseline: bare LLM, single prompt, no tools, no methodology.
# Corresponds to SysMoBench "Basic Modeling Agent".

ABLATION_ID="bare-llm"
ABLATION_GROUP="baseline"
ABLATION_DESC="Single LLM prompt with feedback loop for syntax/runtime errors"
PROMPT_TEMPLATE="bare-llm.md"

SPECULA_SKILLS=()
TLAPLUS_SKILLS=()
MCP_TOOLS=false
