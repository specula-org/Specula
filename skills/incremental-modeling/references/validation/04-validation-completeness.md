# Validation 4: Completeness and Handoff

Finish incremental trace validation only when all of the following hold.

## Harness and Provenance

- The prior harness was reused or minimally rebased; every replacement has an explicit incompatibility rationale.
- `harness/run.sh` applies to the new source and reproducibly builds, runs, and collects traces.
- Updated instrumentation points cite real source symbols and agree with `instrumentation-spec.md` and `Trace.tla`.

## Update Coverage

- Instrumentation around the update observes its producer/setup, branch or pre-state, committed effect, and first high-risk unchanged consumer/fault boundary; any omitted layer has an evidence-backed reason.
- Every `AffectedAction` is observed in a fresh trace or has a cited environment limitation.
- Every selected high-risk Interaction Scenario has a fresh trace with the required producer/consumer/fault evidence.
- Required identity and result fields are emitted and compared by active Trace predicates at source-faithful observation points, following [Validation 1's comparison rule](01-reuse-prior-harness.md#4-close-instrumentation-semantics).
- Category B trace quality includes real overlap, contention, and per-thread order.

Report coverage for the selected scenarios and observed effects, not exhaustive interaction coverage. Unobserved interactions and effects whose results were not compared remain explicit gaps; a bounded coverage limitation is distinct from an unresolved replay mismatch.

## Regression and Conformance

- Compatible prior scenarios were rerun on the new implementation rather than represented only by archived traces.
- Every archived trace has a retained, superseded, or environment-limited disposition.
- The complete retained new-version trace suite passes against the stable candidate under [Validation 3's final regression gate](03-trace-validation-loop.md#4-full-regression-on-the-stable-candidate); local checks alone do not satisfy this gate.
- Each trace has [category-appropriate completion evidence](03-trace-validation-loop.md#completion-evidence): a completed temporal-property check for linear replay or a full-consumption witness for timebox replay. In either case, post-state checks are active and silent Actions are constrained; property names alone do not satisfy the gate.
- The changelog records every fix and the final fresh trace inventory.

Write a concise validation handoff containing the current source SHA, harness command, fresh trace paths, affected/interaction coverage, archived-trace dispositions, and whether validation changed semantic spec files. Initial model-checking campaigns require this gate to pass. Later semantic repairs use Validation 3's local-feedback loop; final workflow convergence still requires full trace regression and applicable model checking on the final artifacts.
