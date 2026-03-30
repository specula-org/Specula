# Ablation: skip Phase 1 (code analysis).
# Spec generation receives only generic system info, no modeling brief.

ABLATION_ID="no-code-analysis"
ABLATION_GROUP="ablation"
ABLATION_DESC="Skip Phase 1: no code analysis, generic system description only"

MULTI_PHASE=true
PHASE_PROMPTS=(
  "no-code-analysis-p2.md"  # Phase 2: Spec Gen with generic brief
  "full-p2.5.md"            # Phase 2.5: Harness (same as full)
  "full-p3a.md"             # Phase 3A: Trace Validation (same as full)
  "full-p3b.md"             # Phase 3B: Model Checking (same as full)
)

SPECULA_SKILLS=("spec_generation" "harness-generation" "tla-trace-workflow" "tla-checking-workflow" "validation-workflow")
TLAPLUS_SKILLS=()
MCP_TOOLS=true
