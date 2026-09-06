## CI Initialization Guidance

This run establishes a reusable modeling and verification baseline for future
incremental checks. Run the normal Specula workflow; this guidance supplements,
and does not replace, each phase's methodology.

Respect the user's explicit priorities, scope, and exclusions. Within that scope,
prioritize semantic depth in the core logic over breadth across peripheral features.
Investigate the core state transitions and the interactions on which their correctness
depends, including relevant failure, concurrency, and recovery paths. Let implementation
evidence determine which mechanisms matter; do not add mechanisms merely to fill a list.

Build a coherent reference covering that core, rather than a collection of isolated
models for a few known bugs. Add detail where it can expose meaningful interactions,
not to meet a model-size or line-count target. Keep important assumptions and remaining
coverage gaps visible so later updates can revisit them.

Produce reusable properties, scenarios, instrumentation, and harness assets through
the existing workflow. Distinguish observed and checked behavior from unresolved
questions and budget-limited exploration. Finding a real implementation bug does not
by itself invalidate a faithful model; finishing the workflow is not a proof of safety.
