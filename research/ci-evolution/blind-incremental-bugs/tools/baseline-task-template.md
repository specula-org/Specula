# Exact-old Specula V0 prior task

Build and validate a fresh Specula V0 prior suite from the immutable exact-old
source tree in `/work/source/`. This is preparation for a blind incremental CI
evaluation, not a request to investigate a known incident.

Inputs:

- `/work/source/`: immutable pristine exact-old source; it has a single neutral
  synthetic Git commit and no upstream history or remotes;
- `/work/work-source/`: a writable byte-identical working copy for build,
  instrumentation, and trace collection;
- `/work/scope.md`: the binding, source-derived subsystem boundary;
- `/work/input-manifest.json`: public input and isolation metadata;
- `/work/lib/`: TLA+ jars;
- `/work/tools/`: blocking process helpers and trace-debugger source.

Use the installed Specula `code-analysis`, `spec-generation`,
`harness-generation`, `tla-trace-workflow`, `validation-workflow`, and
`tla-checking-workflow` skills. Read each selected `SKILL.md` and all references
it requires before using it. Apply the normal methods with these experiment
overrides:

1. Skip the code-analysis skill's archaeology/history/issue-search phase and
   replace it with code-only structural and deep analysis. Analyze only
   `/work/source/` and the neutral scope. Do not search the
   internet, upstream Git history, issues, pull requests, release notes, papers,
   benchmark labels, or any path outside `/work` for behavioral answers. Network
   access is reserved solely for ordinary build dependencies.
2. Derive behavior, atomicity boundaries, failure assumptions, properties, and
   scenarios from the exact-old implementation. Do not speculate about future
   changes and do not target a known bug.
3. Write every artifact under `/work/prior/.specula-output/`. Instrument only
   `/work/work-source/`; never modify `/work/source/` or other immutable inputs.
   Preserve the instrumentation patch relative to the neutral baseline commit.
4. Produce a complete code-faithful suite: `modeling-brief.md`,
   `analysis-report.md`, `spec/base.tla`, `base.cfg`, `MC.tla`, `MC.cfg`,
   `Trace.tla`, `Trace.cfg`, `instrumentation-spec.md`, `brief-coverage.md`, a
   runnable harness, fresh nonempty NDJSON traces, and preserved validation/model
   checking logs. If an artifact cannot be produced, document the exact blocker
   instead of fabricating it.
5. Follow trace-first validation: real implementation trace collection and trace
   validation must precede ordinary model checking. A parse-only check is not
   trace validation. Debug mismatches by classifying implementation/spec/trace
   causes; do not weaken a faithful property merely to obtain green output.
6. Use bounded outer `timeout` for builds, tests, and TLC. Store TLC state below
   `/dev/shm/specula-v0-BASELINE_CASE_ID/`, keep logs under
   `/work/prior/.specula-output/spec/output/`, remove state directories after
   runs, and leave no background processes.
7. State-space or environment bounds are `LIMITED_COVERAGE`, never proof or pass.
   Preserve reachability/non-vacuity evidence for checked scenarios and
   properties.

The resulting V0 must be useful as an honest pre-update prior even if validation
is incomplete. Do not run incremental modeling and do not inspect a new or fixed
revision.

Your final response must be only the JSON object required by
`/work/final-schema.json`.
