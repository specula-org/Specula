# Example: SONiC linkmgrd Modeling Guidance

## Required

### Goal

- Assess correctness risks across Dual-ToR link and failover state management in `sonic-net/sonic-linkmgrd`.

### Scope

- In scope: both active-standby and active-active per-port control paths, from configuration, database, route, link, probe, and mux inputs through local and peer forwarding-state decisions and acknowledgements.
- Boundaries/exclusions: read code outside linkmgrd only to establish caller and component contracts. Exclude packet encoding, Redis/SAI internals, physical mux implementation, and performance unless needed to establish a linkmgrd safety or recovery precondition.

### Priority Questions

1. Can a delayed, duplicated, reordered, or missing input or timeout leave a decision that no longer matches the current mode, health, route, or observed hardware state?
   Expected behavior: decisions apply to the current context and converge when current observations persist.
2. Can an accepted event be lost, applied twice, or reflected inconsistently across LinkProber, MuxState, LinkState, and LinkManager?
   Expected behavior: component and composite states remain mutually consistent and required follow-up is not silently skipped.
3. Across active-standby and active-active operation, can fault and recovery sequences cause a traffic blackhole, contradictory forwarding decisions, oscillation, or permanent failure to recover?
   Expected behavior: each mode preserves its documented forwarding rules and recovers after the relevant health conditions recover.
4. Can mode, configuration, default-route, startup, or warm-restart changes race with pending work so that pre-change work mutates post-change state or reconciliation finishes prematurely?
   Expected behavior: lifecycle and configuration boundaries do not admit stale work, and retained state is reconciled before normal operation.
5. Can events, timers, or state for one mux port affect another port's decisions or progress?
   Expected behavior: per-port behavior remains isolated while shared service lifecycle operations remain consistent.

### Must-cover Interactions

- Database and configuration notifications in `src/DbInterface.cpp` ↔ dispatch through `src/MuxManager.cpp` and `src/MuxPort.cpp`.
- Link-prober events in `src/link_prober/LinkProberStateMachineBase.cpp` ↔ active-standby and active-active LinkManager transitions.
- Mux and physical-link state machines ↔ composite LinkManager state and emitted forwarding commands.
- LinkManager timers and callbacks ↔ responses and later state or configuration changes in both operating modes.
- Default-route and warm-restart handling in `doc/default_route.md`, `src/DbInterface.cpp`, and `src/MuxManager.cpp` ↔ ongoing per-port transitions.

### Assumptions

- Treat the checked-out implementation and its actual call graph as ground truth; use `doc/default_route.md` only for its stated intended behavior.

## Optional

### Suggested Starting Points

- `src/DbInterface.cpp`, `src/MuxManager.cpp`, `src/MuxPort.cpp`, `src/link_manager/`, `src/link_prober/`, `src/mux_state/`, and `src/link_state/`.
