# Incremental validation handoff

- Source: `16c5274b589aa75c634a1a5f2b05cf66aaf37dcc`; harness command: `bash .specula-output/harness/run.sh` from the target directory.
- Harness provenance: minimally rebased V00 adapter; canonical sources are under `harness/src/`, and `harness/patches/instrumentation.patch` reverses cleanly. The five inherited scenarios were freshly regenerated; archived old-version traces are superseded, not reused as new-source correspondence.
- Fresh suite: `traces/{raw-elections-reads-recovery,node-lifecycle,membership-snapshots,same-batch-replay,partition-batching,joint-explicit,joint-autoleave,joint-snapshot-recovery}.ndjson`, 4,629 events. The audit reports every event and required inherited/joint witness visited.
- Coverage: V2 enter/application, both joint quorum halves, joint ReadIndex, explicit leave, Advance auto-leave, snapshot persistence/compaction, and crash/restart; unchanged producer/consumer coverage remains the five inherited scenario families.
- Outcome: all eight traces passed exact full-post-state correspondence; seven also passed all normal `Trace.cfg` invariants. The recovery trace intentionally violates retained `ConfigurationOrigin` at restart after correspondence through all 230 events. `TraceCorrespondence.cfg` isolates matching only so the bug trace can be fully consumed; the failing invariant remains enabled in normal trace and update MC configs.
- Semantic spec changed during validation only for the observed empty-V2 2/10 encoding and the narrowly permitted Advance auto-leave suffix in AckPreservation. SANY and affected/full trace regressions passed after that repair.
- Uncached upstream tests and the race-enabled eight-scenario harness passed; current logs use label `20260913-190126-1248720`.
