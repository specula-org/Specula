# Confirmation Report — etcd-raft V01

## Final Result

Reproduced bugs: 2
Fixed prior findings: 2
Dropped historical duplicates: 1
Needs more information: 2

| Entry | Finding | Status | Counts as final bug? |
|---|---|---|---|
| 1 | CR-1 | FIXED | no |
| 2 | CR-2 | NEEDS MORE INFO | no |
| 3 | CR-3 | REPRODUCED | yes |
| 4 | CR-4 | DROPPED | no |
| 5 | CR-5 | NEEDS MORE INFO | no |
| 6 | CR-6 | FIXED | no |
| 7 | MC-1 | REPRODUCED | yes |

## Entry 1: Empty-log restart no longer resets durable term and vote

- **Finding ID**: CR-1
- **Status**: FIXED
- **Source**: Prior V00 confirmation, rechecked on V01
- **Location**: `rawnode.go:42-58`, `bootstrap.go:23-80`

V01 separates `NewRawNode` from explicit `Bootstrap`. The constructor loads persisted state and no longer infers bootstrap from an empty log, removing the V00 path that reset a saved term and vote. The focused restart and bootstrap controls passed: `TestNodeRestart`, `TestRawNodeStart`, `TestRawNodeRestart`, and `TestRawNodeRestartFromSnapshot`.

## Entry 2: Transfer during unapplied self-removal

- **Finding ID**: CR-2
- **Status**: NEEDS MORE INFO
- **Source**: Prior V00 confirmation, current source review
- **Location**: `raft.go:859-880`, `raft.go:1264-1272`, `raft.go:1464-1474`

The V00 in-package test demonstrated that `MsgTimeoutNow` could bypass the pending-configuration campaign guard. The V01 source retains distinct Hup and transfer paths plus the removed-leader TODO, but the old test depends on its private network harness and was not a current public-interface reproduction. No fixed or reproduced disposition is inferred from source correspondence alone.

## Entry 3: Advance releases the configuration admission guard before ApplyConfChange

- **Finding ID**: CR-3
- **Status**: REPRODUCED
- **Source**: Code review
- **Location**: `raft.go:1007-1031`, `node.go:145-157`

The public `Node` API accepts a first membership change, lets the caller call `Advance`, and then commits a second membership change before the caller has applied the first one. The expected one-change-at-a-time boundary is therefore based on the released cursor rather than effective membership.

**Reproduction result:** `repro/test_bugCR-3_double_confchange.go` was executed against V01. `repro/results/CR-3-double-confchange-v01.log` records the second configuration change committed at index 4 before the first change at index 3 was applied.

## Entry 4: Snapshot campaign scan duplicate

- **Finding ID**: CR-4
- **Status**: DROPPED
- **Source**: Prior V00 confirmation

This remains the V00 duplicate disposition. It is retained for stable finding identity and is not a current severity-bearing result.

## Entry 5: ReadIndex after leader self-removal

- **Finding ID**: CR-5
- **Status**: NEEDS MORE INFO
- **Source**: Prior V00 confirmation, current source review
- **Location**: `raft.go:1032-1069`, `raft.go:1464-1474`

The V01 code still leaves a self-removed leader in its current role and has no matching read admission check. The V00 delayed-heartbeat reproduction has not yet been adapted to the V01 bootstrap and joint-configuration APIs, so a current external read consequence is not asserted here.

## Entry 6: Configuration proposal handoff under full quota

- **Finding ID**: CR-6
- **Status**: FIXED
- **Source**: Prior V00 confirmation, rechecked on V01
- **Location**: `node.go:416-442`, `raft.go:1007-1031`

The V00 report treated the first post-handoff `Ready` as a lost configuration request. On V01, the request is emitted in the next `Ready` after the first batch advances and releases the quota.

**Reproduction result:** `repro/test_bugCR-6_confchange_handoff.go` was executed against V01. `repro/results/CR-6-confchange-handoff-v01.log` records that the configuration change appears in the next `Ready`; no lost admission result was observed.

## Entry 7: Joint snapshot recovery drops the outgoing quorum

- **Finding ID**: MC-1
- **Status**: REPRODUCED
- **Source**: Trace-validation counterexample and public RawNode reproduction
- **Location**: `raft.go:321-382`, `raft.go:1361-1430`, `rawnode.go:42-58`

A persisted joint `ConfState` carries incoming voters, outgoing voters, staged learners, and auto-leave. V01's construction and restore paths rebuild only `Nodes` and `Learners`, so recovery silently discards the outgoing quorum.

**Reproduction result:** `repro/test_bugMC-1_joint_snapshot_recovery.go` was executed against V01. The program creates a joint state `{1,2,4} && {1,2,3}` through public RawNode operations, snapshots it, and restarts nodes 1 and 4 from that snapshot. `repro/results/MC-1-joint-snapshot-recovery.log` records node 1 becoming leader with votes `{1,4}` while the persisted outgoing set `{1,2,3}` has no majority.

## Validation limits

The eight fresh traces have 4,629 events. All eight matched complete source/caller post-state; the joint-recovery trace then violated `ConfigurationOrigin` after its matching restart event. Standard, full-update, focused, and inherited TLC campaigns were bounded by their configured budgets. Their no-violation budget exits are coverage evidence, not exhaustive safety or liveness proofs.
