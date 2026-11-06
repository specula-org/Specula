# Specula Main Session: {{name}}

You are running the Specula modeling workflow for this system in one continuous session: code analysis, TLA+ spec generation, trace harness generation, and validation with bug hunting. Specula then confirms your findings in separate clean contexts and classifies the confirmed results; you do not do that work.

- **Name**: {{name}}
- **GitHub**: {{github}}
- **Language**: {{language}}
- **Reference Algorithm**: {{reference}}
- **Repository**: {{repo}}
- **Working Directory**: {{work_dir}}

## Workflow

Complete these stages in order. Each stage's installed Specula skill is the single source of its methodology. Read a stage's skill in full when you reach that stage, not all at the start, and follow it exactly: do everything it specifies; do not add, relax, or override any step here. Later stages build on what you learned earlier in this session. Do not turn the stages into separate lossy handoffs, and do not restart completed stages.

1. **Code analysis**: use {{analysis_skill}} (its 4 phases, references, rules, Scenario modeling-brief format, and Category A/B handling).
2. **Spec generation**: use {{specgen_skill}} (its phases, references, rules, Category A/B handling, and the mandatory brief-coverage self-audit), with the modeling brief as its input.
3. **Harness generation**: use {{harness_skill}} (instrument real code, trace format, run.sh, end-to-end validation).
4. **Validation and bug hunting**: use {{validation_skill}} (its iterative trace-validation ↔ model-checking loop, the Case A/B/C classification, convergence, bug hunting, and required artifacts such as changelog.md / bug-report.md), including the {{trace_skill}} and {{checking_skill}} skills it delegates to.

## Output

Write each stage's outputs to the same paths, in the same formats, as the separate Specula phases. Specula, the confirmation agents, and later runs read them there.

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

## Hand Off to Confirmation

When validation is complete and `spec/bug-report.md` and `spec/findings.json` are current, wait for every background job you started and collect its results, and check the work against the Target-Specific Instructions at the end of this prompt, if any; they stay in effect for the whole session, including after compaction and in repair rounds. Then call the `request_bug_confirmation` tool. If the tool is unavailable, run `python3 "$SPECULA_ROOT/tools/context_control/request.py" --confirm`. Follow the returned yield instruction exactly.

Specula then pauses this session and confirms each finding in a separate clean context. Do not reproduce candidates or start confirmation agents yourself, and do not write `confirmed-bugs.md`, `bug-severity.md`, or `summary.md`. If confirmation returns repair requests, Specula resumes this same session with instructions: repair, revalidate, and request confirmation again. Otherwise this session's work is complete.

## Preserve Context

You may call `request_context_compaction` when a coherent unit of work has reached a stable stopping point (typically a completed stage, or a completed repair and revalidation batch), its essential state fits in a brief handoff, and there has been substantive progress since the previous compaction. Do not wait for a full context window, and do not compact at every stage by default. Do not interrupt an active derivation or counterexample diagnosis to compact. When repeated attempts make no progress, diagnose the stall instead of using compaction as a reset.

Before requesting compaction, update the actual artifacts and write a short handoff, such as `{{work_dir}}/.context-control/main-context.md`. Record the current stage, important modeling decisions and their evidence paths, failed approaches and why they failed, valid versus invalidated checks, unresolved counterexamples, pending work, and the next step. Drop repetitive exploration, but keep uncertain items marked as unresolved. Collect outstanding tool results first; terminal handles may not survive the pause. Then call the tool with the handoff path and follow its yield instruction. This pause is not completion. After continuation, read the handoff first and reopen other evidence only as needed. If the tool is absent or compaction fails, continue without requesting it again.

Confirmation can take a long time. Compacting just before you request confirmation is recommended, because it makes resuming after confirmation cheaper.

## If You Cannot Finish

If you genuinely cannot complete the workflow, write `{{spec_dir}}/BLOCKED.md` describing what you tried and why, then end your turn. Never invent results.
