# Full Specula pipeline — all phases, each as independent agent call.
# Group 1 (ablation) baseline.

ABLATION_ID="full"
ABLATION_GROUP="ablation"
ABLATION_DESC="Full Specula pipeline (5 phases, sequential agent calls)"

MULTI_PHASE=true
PHASE_PROMPTS=(
  "full-p1.md"    # Phase 1: Code Analysis → modeling-brief.md
  "full-p2.md"    # Phase 2: Spec Generation → base.tla, MC.tla, Trace.tla
  "full-p2.5.md"  # Phase 2.5: Harness → instrumented code + traces
  "full-p3a.md"   # Phase 3A: Trace Validation → iterative spec fixes
  "full-p3b.md"   # Phase 3B: Model Checking → bug-report.md
)

SPECULA_SKILLS=("ALL")
TLAPLUS_SKILLS=()
MCP_TOOLS=true
