# Coordinator review of V01 prototype

The final V01 directional results need an independent rerun in fresh directories before acceptance. The run compares real original Go/TLA operators and exposes three source-backed model mismatches, but the adapter currently permits stale exported results when a work directory is reused.

## Reproduced stale-successor problem

Evidence: `results/framework-stale-output-control/result-v2.json` and its retained adapter copy.

1. Run one normal Hup case through the TLC adapter in `reused-v2`: exit 0, one result with `adapter_status=ok`.
2. Disable `LocalNext` with a leading `FALSE` in the copied test wrapper and run again in the same directory: exit 0, one stale result still marked `ok`.
3. Run the identical disabled wrapper in a new directory: exit 0, one `unsupported` result instead.

This is a synthetic checker control, not an etcd bug. The production adapter loads `*.json` from an existing results directory after every run. Its source files, initial-state inputs, and the absence of a current successor do not invalidate the prior export. Enforce a fresh, exclusive invocation workspace and avoid consuming any output from failed commands. Keep all prior attempts under distinct paths.

## Disabled actions

A well-formed corresponding pre-state/input for which the original model action has no successor should be distinguishable from an adapter/setup failure. Export the pre-state and input observation even when no successor exists. If those agree with Go and Go executes, report a behavioral mismatch (`model disabled, implementation enabled`). If the state cannot be mapped or preconditions cannot be established, report unresolved setup instead. Do not drop such cases from model-generated coverage.

## Remaining acceptance checks

- Reproduce the stale-output control with the fixed runner/adapter and require refusal or a fresh disabled result, never the old successor.
- Re-execute the four V01 baseline/repaired directional runs in fresh directories; preserve source/model hashes and initial failures.
- Preserve message multiplicity, ordered log/entry sequences, mapped input checks and pre-state checks.
- Report overlapping input domains and local constructed states explicitly; 138 executions are not necessarily 138 distinct reachable protocol scenarios.
- Retain operator/Action-level testing status; no known-bug discovery, invariant correctness or global model conformance has yet been established by this stage.

## Completed successor integrity control

`agent-runs/framework-uniqueness-02` injects two TLC successors for one input: one agrees with source and one changes the term. The old single-file export overwrote one and reported `match`. The append-only journal records both and returns `unsupported`; the deterministic control still matches. The earlier `framework-uniqueness` attempt had an invalid nonconstant argument to a parameterized model instance and is not evidence of this defect. Its failure logs are retained.

The accepted complete adapter is now `agent-runs/action-framework-final/out/framework`. Final six-direction replay: 479 code plus 174 generated instances on each V01/V02/V03, all matched; exact original source files are verified unchanged. Initial V01/V02 reruns had a duplicate old test fixture, which was archived before fresh rerun and counted only as setup failure. See `out/final-results.json`.
