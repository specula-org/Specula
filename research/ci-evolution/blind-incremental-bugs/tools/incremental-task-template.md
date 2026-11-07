# Blind end-to-end incremental Specula task

Use the installed `incremental-modeling` skill and execute every currently
implemented part in order: Generation, Validation, and Model Checking. If model
checking produces an actual finding, preserve the standard findings and
counterexample artifacts. A separate, blinded grader will run the old and fixed
implementation controls after your output is frozen.

Inputs:

- `/work/old-source/`: immutable exact-old changed-file snapshot;
- `/work/new-source/`: immutable updated changed-file snapshot;
- `/work/previous/.specula-output/`: immutable, exact-old V0 prior suite;
- `/work/current/.specula-output/`: writable current run seeded from the prior;
- `/work/current/.specula-output/artifact/`: complete writable updated source
  tree with exactly two neutral synthetic commits, `baseline` and `update`;
- `/work/model-scope.md` and `/work/case.json`: public scope and opaque update
  metadata;
- `/work/input-manifest.json`: public input identities and isolation contract;
- `/work/lib/`: TLA+ jars;
- `/work/tools/`: blocking process helpers and trace-debugger source.

Read the incremental skill and all underlying skills/references it selects. Keep
all edits and outputs under `/work/current/.specula-output/`.

Blindness rules:

- Analyze the supplied old/new source and neutral synthetic diff yourself.
- Do not search the internet, upstream history, issues, pull requests,
  advisories, release notes, papers, benchmark labels, or paths outside `/work`
  for answers. Network is reserved only for ordinary build dependencies.
- Do not assume the update is buggy. Report `NO_MODEL_CHANGE`, a sound update,
  an unsupported/limited result, or findings strictly from your own evidence.
- Do not access a fixed revision or a Gold oracle; neither is supplied.

Validation requirements:

- Rebase and reuse the prior harness where compatible; record incompatibility
  honestly rather than silently substituting weaker evidence.
- Run prior scenarios on the updated implementation and collect fresh, nonempty
  traces. Add update-focused scenarios only when derived from the visible diff.
- Show that trace fields are actually consumed by `Trace.tla` and run real TLC
  trace validation before ordinary model checking. Parse-only checks do not
  count.
- Preserve exact commands, logs, trace inventories, and coverage evidence.

Model-checking requirements:

- Execute standard convergence and every applicable update-focused/open/full
  campaign specified by the incremental and validation/checking skills.
- Keep TLC states below `/dev/shm/specula-e2e-INCREMENTAL_CASE_ID/` and logs in
  `spec/output/`; remove state directories after every run.
- Use bounded outer `timeout` for builds, tests, and TLC. Do not leave background
  processes running.
- Record resource bounds as `LIMITED_COVERAGE`, never as proof or pass. Require
  reachability/non-vacuity evidence before crediting properties.
- Do not weaken a faithful model or property merely to obtain green output.

Your final response must be only the JSON object required by
`/work/final-schema.json`. Map `MODEL_CHANGE_REQUIRED` to `MODEL_UPDATED`.
