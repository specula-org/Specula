# Ablation: skip all verification (Phase 2.5 + Phase 3A + Phase 3B).
# Only code analysis and spec generation, no checking at all.

ABLATION_ID="no-phase-3"
ABLATION_GROUP="ablation"
ABLATION_DESC="Skip all verification: no harness, no trace validation, no model checking"

MULTI_PHASE=true
PHASE_PROMPTS=(
  "full-p1.md"              # Phase 1: Code Analysis (same as full)
  "no-trace-validation-p2.md"  # Phase 2: Spec Gen (no Trace.tla needed)
)

SPECULA_SKILLS=("code_analysis" "spec_generation")
TLAPLUS_SKILLS=()
MCP_TOOLS=true
