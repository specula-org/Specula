Each stage's skill is the methodology reference for that stage: apply its procedure, references, and rules. The Output section below is this session's contract. Its required outputs must exist and be valid when you request confirmation. The other files the skills describe are recommendations: write them when they help you or a later reader, for example to keep working state across compaction or to record why the model looks as it does.

## Output

Write each output to the path below, in the format its stage's skill describes. Specula, the confirmation agents, and later runs read them there.

### Required

Specula checks these before it starts confirmation and returns any problem to this session: each file must be non-empty, `base.tla`, `MC.tla`, and `Trace.tla` must parse with SANY, and `findings.json` must follow the validation skill's findings format with every counterexample saved under `{{work_dir}}`.

- `{{work_dir}}/modeling-brief.md` — Modeling brief, including the code-review Scenarios that confirmation reads
- `{{spec_dir}}/base.tla` — Base specification
- `{{spec_dir}}/MC.tla` — Model checking specification
- `{{spec_dir}}/MC.cfg` — Model checking config (hunt configs such as `MC_hunt_*.cfg` sit beside it)
- `{{spec_dir}}/Trace.tla` — Trace validation specification
- `{{spec_dir}}/Trace.cfg` — Trace validation config
- `{{work_dir}}/harness/run.sh` — One-command build + run + collect traces
- `{{work_dir}}/traces/*.ndjson` — Trace files from test runs. Required whenever the harness can run; if it cannot, explain why in `bug-report.md`, and Specula records in the summary that trace validation did not run
- `{{spec_dir}}/bug-report.md` — Bug hunting results, also when no bug was found
- `{{spec_dir}}/findings.json` — Machine-readable mirror of the bug report (`"findings": []` when there is none)

### Recommended

Specula does not require these. Write them when they are useful, at the paths the skills use:

- `{{work_dir}}/analysis-report.md` — Detailed audit trail of the analysis
- `{{spec_dir}}/base.cfg` — Base config
- `{{spec_dir}}/brief-coverage.md` — Coverage audit mapping the brief to hunt configs and invariants
- `{{spec_dir}}/instrumentation-spec.md` — Instrumentation mapping
- `{{work_dir}}/harness/src/` and `{{work_dir}}/harness/apply.sh` — The harness layout the skill describes behind `run.sh`
- `{{work_dir}}/harness/INSTRUMENTATION.md` — Guide for adjusting the instrumentation
- `{{spec_dir}}/changelog.md` — Record of model fixes across validation rounds
