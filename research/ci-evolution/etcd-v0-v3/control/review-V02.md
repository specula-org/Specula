# V02 coordinator checks

The supported action results are promising: 239 code-derived and 103 TLC-generated instances match after repair; 21 selected old-version controls also match. Verify the final retained files after the agent exits and rerun the published suite from fresh directories. Run the generated actual-Node tests under the race detector because observers inspect live internal fields after Status barriers.

R1/R2 are pre-existing defects still present in the archived provisional V02 model. The archived model predates this experiment's new V01 repairs. Do not report them as evidence that the current agent lost an established repair during an actual new sequential update. They demonstrate persistence of old defects and the value of retained action cases. V03 will actually evolve from the currently repaired V02 model.

R3 broadens the reference API behavior to include empty RawNode Ready calls; native evidence shows unchanged projected Go state and an empty result. Treat this carefully as an API/abstraction boundary. The old temporal model can already represent stuttering; exact API-action matching is a stronger requirement. If the expanded reference is retained, assess idle Ready/Advance cycles and auxiliary readySeq growth during phase 3. Do not silently let extra auxiliary states dominate search or declare every disabled/no-op discrepancy a protocol modeling bug.

Malformed persisted ConfStates are explicitly outside the supported input domain. Keep their six disagreement records as scope diagnostics. Do not count them as six known system bugs or claim that arbitrary malformed input behavior has been validated.

Invariant assessment must compare semantics, including helpers and observers. For example, extending ConfKinds with V2 changes CampaignContract's meaning even if its predicate text is unchanged. Preserve the requirement for all pending configuration entries while leaving the actual StepHup implementation scan legacy-only. A source-backed behavior is not sufficient evidence to weaken the correctness requirement. Classify representation/type migration separately from a new or relaxed requirement.
