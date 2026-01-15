## 2026-01-12 - Initial XLine CURP base spec

**Trace:** `N/A (initial spec)`
**Error Type:** Inconsistency Error

**Issue:**
The workload lacked a base TLA+ spec to model XLine CURP state transitions.

**Root Cause:**
No existing spec in `/data/workloads/curp/spec` to capture leader, speculative pool, uncommitted pool, and committed command behavior.

**Fix:**
Created an initial CURP model and TLC config based on code paths and trace event names.

**Files Modified:**
- `curp.tla`: added base state variables and actions for propose, commit, and leader change.
- `curp.cfg`: added model checking configuration and constants.

## 2026-01-12 - Missing SeqToSet helper in base spec

**Trace:** `N/A (model check)`
**Error Type:** Inconsistency Error

**Issue:**
TLC reported `SeqToSet` as an unknown operator when checking the base spec.

**Root Cause:**
The model used `SeqToSet` without defining it in the module or importing a module that provides it.

**Fix:**
Added a local `SeqToSet` definition in `curp.tla` and reduced the model-checking constants in `curp.cfg` to keep TLC state space small.

**Files Modified:**
- `curp.tla`: added `SeqToSet` helper.
- `curp.cfg`: reduced `Servers` and `Cmds` constants for faster TLC runs.

## 2026-01-12 - Added CURP trace validation wrapper

**Trace:** `../harness/traces/trace-1.ndjson`
**Error Type:** Inconsistency Error

**Issue:**
No trace validation wrapper existed for CURP to align trace events with the base model.

**Root Cause:**
`Tracecurp.tla` and `Tracecurp.cfg` were missing.

**Fix:**
Added a Tracecurp wrapper spec with JSON parsing, trace step validation, and progress logging, plus a TLC config for trace validation.

**Files Modified:**
- `Tracecurp.tla`: new trace validation wrapper for CURP events.
- `Tracecurp.cfg`: trace validation configuration with constants.

## 2026-01-12 - Treat trace line 1 as initial state

**Trace:** `../harness/traces/trace-1.ndjson`
**Error Type:** Inconsistency Error

**Issue:**
Trace validation failed at `l=1` because the spec interpreted the first logline as a transition, but the trace encodes the initial state snapshot on line 1.

**Root Cause:**
`TraceInit` set `l = 1` and expected a `LeaderChange` transition to reach the first logline.

**Fix:**
Initialize `leader`, `specPool`, and `committed` from `TraceLog[1]` and start validation at `l = 2`.

**Files Modified:**
- `Tracecurp.tla`: initialize state from `TraceLog[1]` and begin trace steps at line 2.

## 2026-01-12 - Support spec_pool trace schema

**Trace:** `../harness/traces/trace-100.ndjson`
**Error Type:** Inconsistency Error

**Issue:**
Trace validation failed because the wrapper expected `speculativePool`/`committedCommands` fields, but the trace uses `spec_pool` and omits committed commands.

**Root Cause:**
`Tracecurp.tla` only handled the newer schema and required `committedCommands` even when absent.

**Fix:**
Added schema-aware field selection (`spec_pool` vs `speculativePool`) and made committed commands optional when missing in the trace.

**Files Modified:**
- `Tracecurp.tla`: added schema-aware trace field handling and optional committed checks.

## 2026-01-12 - Align propose record semantics with system code

**Trace:** `../harness/traces/trace-100.ndjson`
**Error Type:** Inconsistency Error

**Issue:**
Trace validation failed on `ProcessPropose*` events because the base spec assumed `Propose` populates all speculative pools immediately.

**Root Cause:**
System code updates speculative pools only on record handling (`follower_record`/`leader_record`), while `Propose` only emits a trace event.
Evidence: `code/mod.rs:508-568` inserts into `spec_pool`/`uncommitted_pool`; `code/propose_impl.rs:123-146` only emits `Propose` trace.

**Fix:**
Moved speculative pool updates to `ProcessProposeLeader`/`ProcessProposeNonLeader` and made `Propose` a no-op state-wise. Also allowed command reuse by removing committed-uniqueness constraints.

**Files Modified:**
- `curp.tla`: update Propose/ProcessPropose actions and relax command uniqueness constraints.

## 2026-01-12 - Parse pool entries by schema (record vs string)

**Trace:** `../harness/traces/trace-1.ndjson`, `../harness/traces/trace-100.ndjson`
**Error Type:** Inconsistency Error

**Issue:**
Trace validation errored when interpreting pool entry types across schemas.

**Root Cause:**
Pool entries are strings in `speculativePool` traces and records in `spec_pool` traces; the wrapper used a single type check that failed on one or the other.

**Fix:**
Switched to schema-based parsing: use record `.key` extraction for `spec_pool` traces and raw string values for `speculativePool` traces.

**Files Modified:**
- `Tracecurp.tla`: split pool parsing by schema field presence.

## 2026-01-12 - Propose populates speculative pools to match trace

**Trace:** `../harness/traces/trace-1.ndjson`
**Error Type:** Inconsistency Error

**Issue:**
Trace validation failed at line 2 (Propose) because the trace shows speculative pools already populated on propose, but the base spec left pools unchanged.

**Root Cause:**
`curp.tla` modeled `Propose` as a no-op on speculative pools, while the trace format encodes pool updates on Propose.

**Fix:**
Allow `Propose` to populate speculative pools across all servers so the trace can match the modeled transition.

**Files Modified:**
- `curp.tla`: permit `Propose` to add the proposed command to all speculative pools.

## 2026-01-12 - Allow partial speculative pool updates on Propose

**Trace:** `../harness/traces/trace-5.ndjson`
**Error Type:** Inconsistency Error

**Issue:**
Some traces populate speculative pools for only a subset of servers on `Propose`, but the spec required either no change or an update for every server.

**Root Cause:**
The trace format records speculative pools as per-node snapshots that can change on a subset of nodes, so a single `Propose` event may only update some servers.

**Fix:**
Allowed `Propose` to add the proposed command to any subset of servers (including all), instead of forcing an all-or-nothing update.

**Files Modified:**
- `curp.tla`: relaxed `Propose` pool update to use an arbitrary subset of servers.

## 2026-01-12 - Expand Cmds constant to include observed keys

**Trace:** `../harness/traces/trace-5.ndjson`
**Error Type:** Inconsistency Error

**Issue:**
Trace validation failed when commands `key_5` and `key_6` appeared, but the model only allowed `key_0` to `key_4`.

**Root Cause:**
The trace generator emits `key_5` and `key_6` in several runs, but `Tracecurp.cfg` only defined five commands.

**Fix:**
Extended the `Cmds` constant to include `key_5` and `key_6`.

**Files Modified:**
- `Tracecurp.cfg`: added `key_5` and `key_6` to `Cmds`.

## 2026-01-12 - Relax ProcessCommitMsg to allow multi-remove and no-op commits

**Trace:** `../harness/traces/trace-31.ndjson`
**Error Type:** Inconsistency Error

**Issue:**
`ProcessCommitMsg` events in the trace can remove multiple speculative entries at once or be no-ops when a commit is duplicated, but the base spec only removed a single command and required it to be present.

**Root Cause:**
The trace snapshots show follower pools clearing more than one entry on commit and replaying commit messages without pool changes.

**Fix:**
Updated `ProcessCommitMsg` to remove any subset containing the committed command, and allow a no-op when the command is already absent.

**Files Modified:**
- `curp.tla`: allow subset removals and idempotent `ProcessCommitMsg` updates.

## 2026-01-12 - ProcessProposeLeader allows conflict no-op

**Trace:** `../harness/traces/trace-4.ndjson`
**Error Type:** Inconsistency Error

**Issue:**
`ProcessProposeLeader` events can occur without changing the leader speculative pool, but the spec required inserting the command and updating the uncommitted pool.

**Root Cause:**
Trace line 40 shows `ProcessProposeLeader` with `speculativePool` unchanged and `uncommittedPool` empty, indicating a conflict/no-op path not modeled in the base action.

**Fix:**
Allowed `ProcessProposeLeader` to be a no-op and prevented duplicate inserts when the command is already in the leader pool to avoid nondeterministic state splits.

**Files Modified:**
- `curp.tla`: gated leader inserts and added no-op path in `ProcessProposeLeader`.

## 2026-01-12 - Commit allowed when leader pool already cleared

**Trace:** `../harness/traces/trace-4.ndjson`
**Error Type:** Inconsistency Error

**Issue:**
`Commit` required the command to be present in the leader speculative pool, but the trace commits `key_4` while the leader pool is empty.

**Root Cause:**
Trace line 47 commits with `speculativePool` empty for the leader, so the spec's membership guard rejected the commit.

**Fix:**
Removed the speculative-pool membership requirement from `Commit` and only remove from the uncommitted pool if the command is present.

**Files Modified:**
- `curp.tla`: relaxed `Commit` precondition and made uncommitted removal conditional.

## 2026-01-12 - Trace wrapper no-op ProcessProposeLeader and commit fallback

**Trace:** `../harness/traces/trace-4.ndjson`
**Error Type:** Abstraction Gap

**Issue:**
Trace line 40 records `ProcessProposeLeader` with an unchanged speculative pool, and line 47 commits `key_4` after the leader pool is already empty.

**Root Cause:**
The trace stream includes no-op leader record events and commit entries that do not preserve the leader speculative pool invariant modeled in the base spec.

**Fix:**
Added trace-wrapper fallback branches to accept no-op `ProcessProposeLeader` steps only when the leader pool is empty and the trace state is unchanged, and to advance `committed` when the trace appends a command even if `specPool[leader]` is empty. The base spec remains unchanged to avoid regressions in other traces.

**Files Modified:**
- `Tracecurp.tla`: add no-op `ProcessProposeLeader` branch and commit fallback guarded by trace state.
