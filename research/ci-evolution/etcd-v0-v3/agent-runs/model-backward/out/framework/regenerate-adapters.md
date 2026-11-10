Give another agent the following task, together with the new source/model snapshots and `protocol.schema.json`. This document is an instruction for a future adaptation, not evidence of independent generation in this run.

“Keep the generic runner, protocol, and comparator tests unchanged. Generate only target/language adapters and declarative target descriptors. Work from the provided source diff and original model operators. Do not add a second executable protocol oracle in the runner, a scripting language, or a substitute formal model.

Implement an adapter CLI accepting `--input`, `--output`, `--work`; any model path comes from the manifest. Read JSON-array cases and emit JSONL results. Execute the real source implementation, preferably through package-local tests or supported constructors. Separate setup failures from real return/drop/panic outcomes. Capture raw execution evidence, the mapped actual pre-state and input, and the whole declared output state, messages and side effects. Never infer an expected transition in the adapter.

Generate a model adapter that invokes actual original operators/transitions in a bounded local run, both for testing supplied code-derived cases and for exporting model-derived cases plus successor observations. Enumeration/projection glue is permitted; transition reimplementation is not. Serialize every candidate, including disabled/unsupported actions, so coverage cannot silently disappear.

Provide target input domains and an observation map for every family. Document structural validity checks, hidden state, lifecycle ownership, external effects, ordering, nondeterminism and reachability. Treat shared mappings as a source of correlated errors. Keep contexts, sizes, status categories, errors and message multiplicities exact wherever relevant to the chosen domain. Give every excluded component an explicit reason and expansion task.

Run both directions against the preserved baseline. Triage setup/projection errors separately from behavioral mismatches. Repair only source-backed behavioral model errors in a separate copy; keep source and invariants unchanged. Retain the baseline evidence and replay the same cases on the repair. Produce machine-readable counts, commands, durations and unsupported cases. Do not claim general conformance or independent discovery.”

For this Go/TLC target, adapter limits and command examples are in `README.md` and `targets/etcd/observations.md`. A new language changes executable calls and marshaling, not the language-independent JSON protocol or runner.
