# Validation 1: Reuse the Prior Harness

Treat the previous harness as a validated CI asset, not scaffolding to regenerate. Work in the new run; keep the prior `.specula-output/` immutable.

## 1. Establish Provenance

- Confirm the prior harness, traces, source revision, build configuration, and validation changelog belong to the supplied old run.
- Preserve the prior system category and trace strategy: Category A single-file traces or Category B per-thread timebox traces.
- Read the current `instrumentation-spec.md`, `Trace.tla`, and update Scenarios before editing the harness.
- Read and apply the relevant category-specific parts of the installed Specula **harness-generation** skill. Do not repeat its language templates here.

## 2. Rebase, Do Not Regenerate

Copy the prior `harness/` and reusable scenario definitions into the current run. Reapply its patch or copy-and-patch recipe to the new source using symbol/context evidence rather than stale line numbers.

Preserve working components unless the update invalidates them:

- trace writer, ID mapping, timestamp/timebox strategy, preprocessor, and cleanup scripts;
- build and test commands already proven by the prior run;
- unaffected instrumentation points and scenario setup;
- prior artifact/build caches only when source SHA, configuration, and provenance make reuse safe.

Change only what is necessary for:

- affected Actions and selected Interaction Actions;
- new/revised event fields, capture timing, or Action names required by the current Trace spec;
- source drift that prevents the old patch from applying;
- new focused scenarios that the prior harness cannot trigger.

If the update changes the system architecture enough that the prior harness cannot be rebased, record the exact incompatibility. Adapt the smallest reusable layer; do not silently replace the entire harness with weaker instrumentation.

## 3. Densify Instrumentation Around the Update

The update window deserves denser observation than unchanged code. Reuse all sound prior probes, then add enough update-local probes to observe the changed behavior entering, taking effect, and becoming visible to old context.

For each update Scenario, instrument the real code boundaries that expose:

- the old producer or setup state consumed by an affected Action;
- the guard/branch identity and relevant pre-state at the affected Action;
- the affected Action's committed post-state at its real atomic boundary;
- the first unchanged consumer, persistence, retry, recovery, or message path that observes the result;
- high-risk fault/interleaving boundaries selected as `InteractionActions`.

Cover every changed special/general call site rather than assuming one probe represents them all. Capture the fields that distinguish old behavior, new behavior, and competing unchanged branches. When the prior harness already provides all of this evidence, retain it instead of adding duplicate events.

“More instrumentation” means more semantic observation points around the update, not logging every changed line. Avoid unrelated probes and probe effects. For Category B, keep intervals tight and the hot path lock-free; prefer a few precise per-thread timebox events over shared logging that serializes the race.

## 4. Close Instrumentation Semantics

- Event names, field names, and pre/post capture timing must match `Trace.tla` and `instrumentation-spec.md` exactly.
- Every mandatory update identity or post-state field must be emitted on the real changed path and required by Trace validation.
- Never make a Trace check optional solely because the old harness lacks the field; update the harness instead.
- Keep silent Actions narrowly guarded. Prefer observing an affected or high-risk interaction Action over making it silent.
- Instrument real code, never a simulator, and never hand-write traces.

Update `harness/INSTRUMENTATION.md` with only the changed points and the normal rebuild/rerun instructions.

## 5. CI Reproducibility

The current `harness/run.sh` must remain a one-command path that applies instrumentation to the new source, builds it, executes selected scenarios, and writes fresh traces. Wrap builds and tests in bounded timeouts and treat a timeout as evidence rather than blindly retrying.
