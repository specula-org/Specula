# Usage

## Skills

| Skill | Purpose |
|-------|---------|
| `/code-analysis` | Analyze target codebase, mine git history and issues, produce a modeling brief |
| `/spec-generation` | Generate TLA+ specifications (base, model-checking, trace validation, instrumentation mapping) |
| `/harness-generation` | Instrument source code to emit NDJSON traces, write test scenarios, collect traces |
| `/validation-workflow` | Iterative trace validation + model checking until convergence, then bug hunting |
| `/tla-trace-workflow` | Validate a single trace against a TLA+ spec (used by validation-workflow) |
| `/tla-checking-workflow` | Run TLC model checking and classify counterexamples (used by validation-workflow) |
| `/bug-confirmation` | Validate TLA+ counterexamples against real code, reproduce bugs |
| `/bug-recording` | Record confirmed bugs to the shared bug tracker |

Each skill has a detailed guide in `skills/<skill-name>/guide.md`.
