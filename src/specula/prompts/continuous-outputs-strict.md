Each stage's installed Specula skill is the single source of its methodology. Follow it exactly: do everything it specifies; do not add, relax, or override any step here.

## Output

Write each stage's outputs to the same paths, in the same formats, as the separate Specula phases. Specula, the confirmation agents, and later runs read them there. Every output below is required. Specula checks them before it starts confirmation and returns any problem to this session: each file must be non-empty, `base.tla`, `MC.tla`, and `Trace.tla` must parse with SANY, `findings.json` must follow the validation skill's findings format with every counterexample saved under `{{work_dir}}`, and `traces/` must hold at least one non-empty trace.

Code analysis:
- `{{work_dir}}/modeling-brief.md` — The primary deliverable (input to spec generation and confirmation)
- `{{work_dir}}/analysis-report.md` — Detailed audit trail of all findings

Spec generation (create `{{spec_dir}}/`):
- `{{spec_dir}}/base.tla` — Base specification
- `{{spec_dir}}/base.cfg` — Base config
- `{{spec_dir}}/MC.tla` — Model checking specification
- `{{spec_dir}}/MC.cfg` — Model checking config
- `{{spec_dir}}/brief-coverage.md` — Coverage audit mapping brief §2/§5/§6.1 to hunt cfgs and invariants
- `{{spec_dir}}/Trace.tla` — Trace validation specification
- `{{spec_dir}}/Trace.cfg` — Trace validation config
- `{{spec_dir}}/instrumentation-spec.md` — Instrumentation mapping

Harness generation (harness files in `{{work_dir}}/harness/`, traces in `{{work_dir}}/traces/`):
- `{{work_dir}}/harness/src/` — Trace emission module + test scenarios
- `{{work_dir}}/harness/apply.sh` — Apply instrumentation to artifact
- `{{work_dir}}/harness/run.sh` — One-command build + run + collect traces
- `{{work_dir}}/harness/INSTRUMENTATION.md` — Guide for adjusting the instrumentation during validation
- `{{work_dir}}/traces/*.ndjson` — Trace files from test runs

Validation: every artifact the validation skill requires, including `{{spec_dir}}/changelog.md`, `{{spec_dir}}/bug-report.md`, and `{{spec_dir}}/findings.json`.
