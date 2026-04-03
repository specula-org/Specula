# Ablation: Phase 1 without bug family framework.
# Code analysis runs, but findings are not organized into bug families.

ABLATION_ID="no-bug-families"
ABLATION_GROUP="ablation"
ABLATION_DESC="Phase 1 without bug family grouping; flat analysis only"

MULTI_PHASE=true
PHASE_PROMPTS=(
  "no-bug-families-p1.md"  # Phase 1: Analysis without bug families
  "full-p2.md"             # Phase 2: Spec Gen (same as full)
  "full-p2.5.md"           # Phase 2.5: Harness (same as full)
  "full-p3a.md"            # Phase 3A: Trace Validation (same as full)
  "full-p3b.md"            # Phase 3B: Model Checking (same as full)
  "full-p4.md"             # Phase 4: Bug Confirmation (same as full)
)

SPECULA_SKILLS=("ALL")
TLAPLUS_SKILLS=()
MCP_TOOLS=true
