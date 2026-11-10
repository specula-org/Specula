Implemented and evaluated both routes: 105 code-derived cases and 43 TLC-generated cases.

- Preserved 18 baseline mismatches covering three model errors.
- Applied three source-backed repairs; all 148 cases now match.
- Preserved original files and invariant bodies.

[Report](/workspace/out/report.md) · [Results](/workspace/out/results.json) · [Framework](/workspace/out/framework/README.md) · [Repairs](/workspace/out/repaired-spec/base.tla)

Next steps: validate reachable cluster histories, exercise actual Node channel schedules, and review the recorded invariant issues. This remains a local-action pilot, not general conformance evidence.