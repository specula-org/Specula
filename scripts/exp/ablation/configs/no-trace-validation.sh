# Ablation: skip Phase 2.5 + Phase 3A (harness + trace validation).
# Spec goes directly to model checking without trace-based refinement.

ABLATION_ID="no-trace-validation"
ABLATION_GROUP="ablation"
ABLATION_DESC="Skip trace validation: no harness, no trace-based spec refinement"

MULTI_PHASE=true
PHASE_PROMPTS=(
  "full-p1.md"                  # Phase 1: Code Analysis (same as full)
  "no-trace-validation-p2.md"   # Phase 2: Spec Gen (no Trace.tla needed)
  "full-p3b.md"                 # Phase 3B: Model Checking (same as full)
)

SPECULA_SKILLS=("code_analysis" "spec_generation" "tla-checking-workflow" "validation-workflow")
TLAPLUS_SKILLS=()
MCP_TOOLS=true
