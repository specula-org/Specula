# Exploration checks queued for phase 3

No new global model-checking campaign has run yet. These checks come from actual model inspection during phase 1.

1. Historical MC and hunt configs contain explicit finite workload/fault bounds. Several old election hunts still select legacy workload kinds; verify V2 entries and CampaignDecisionEligibility are enabled in the actual current configurations.
2. ConfigurationProgress.tla already provides a concrete-trace-seeded service pump with nondeterministic message selection and a temporal settled predicate. Reuse/adapt its justified environment if an automatic-membership progress property needs an unbounded fair service suffix. Do not call a copied successful/failed trace suffix autonomous exploration.
3. The V02 action-validation draft permits RawNode.Ready with an empty batch, whereas the historical protocol model required ContainsUpdates. Native evidence confirms the empty call leaves the projected Go state unchanged and returns an empty Ready. Classify this modeling-scope difference before claiming another implementation/model bug.
4. If empty Ready is retained in the complete reference, inspect its effect on exploration: NewReady increments readySeq and Ready/Advance can form idle cycles. readySeq and application jobs' batch labels appear to be auxiliary identities; check all control/property uses before any view quotient or elision. Do not assume syntactic field removal is automatically sound. A focused view may need to avoid exploring infinitely many auxiliary renamings while preserving real Ready/Advance interleavings.
5. Attribute misses separately to fidelity, stale/missing property, inaccessible scenario, bounds, or search cost. A liveness failure must not be inferred from a finite timeout alone.

## Confirmed configuration omissions before new campaigns

- V01/V03 `MC.cfg` and the inherited election hunt enumerate Normal/AddVoter/AddLearner/Remove/Update/Read, but not V2. Even with a faithful Hup operator, these campaigns do not inject the newly introduced request type.
- V02/V03 `Update_full.cfg` includes V2 but lists update predicates without CampaignDecisionEligibility. Its broader transition relation does not make an unchecked property checked.
- The inherited management liveness property covers applying an existing committed configuration entry. It does not require creation and completion of an automatic leave entry; all ordinary MC liveness properties are commented out. This is a property/monitor coverage gap, distinct from exploration speed.

These are static configuration observations, not measured bug-discovery outcomes. The baseline campaigns must still be executed and their actual depth/state counts recorded.

## Baseline instrumentation preflight

The first V01/V03 diagnostic invocations requested TLC `-coverage 1` with a 6 GiB heap and failed before initial-state generation with Java OOM. They are startup/tooling failures, not model-search passes or evidence that the original campaign cannot find a bug. The same V03 suite with coverage telemetry omitted initialized 81 states promptly and entered exploration. Keep coverage telemetry out of the comparable timing runs; retain the startup failures separately.

## Candidate search adaptation to test after property validation

Existing traces may be useful as long legal input prefixes rather than only fidelity checks. `Trace.MatchEvent` dispatches the original reference action, while `TraceNext` separately enforces old recorded post-state equality. A new-version guided setup can replay old input events through actual new-version actions from its own Init, without asserting the old post-state. Branch from successfully replayed prefixes around changed mechanisms into the complete/focused reference actions. This yields model-reachable prefixes by construction; it is not a freshly code-validated new-version trace. A real public-API reproduction must still validate any resulting complete counterexample.

Preserve prefix provenance and full model counterexamples. If a prefix no longer executes, report it as inapplicable; do not inject an arbitrary replacement state. Count setup operations separately from additional exploration budgets. For fair timing ablations, match constants/property/input domains between guided and unguided variants; inherited MC.cfg with different trace settings is a separate baseline, not a matched ablation. This is guided under-approximate hunting, not exhaustive coverage or a new refinement proof.

For automatic-exit progress, the inherited ConfigurationProgress service pump is a possible starting point. It tracks applying an already-proposed entry, which is not the required property of eventually creating/applying a leave entry. The new property must cover that missing obligation. Fair service must include leader heartbeat progress when earlier queues drain; otherwise a correct old implementation can stall merely because the test environment never prompts publication. Prefer a finite, explicitly justified service environment with old-version controls; a finite timeout does not establish a liveness bug.

`readySeq`, `ready.id`, and queued job `batch` are currently write-only auxiliary identities outside protocol guards/properties (review again after observer changes). A view quotient may canonicalize these fields while retaining budgets, real state, and obligation monitors. Otherwise empty Raw Ready/Advance cycles generate unbounded distinct names. Validate the quotient's dependency assumptions and negative controls before using it for a liveness cycle.
