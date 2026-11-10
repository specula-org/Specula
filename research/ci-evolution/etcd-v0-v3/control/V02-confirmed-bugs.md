# Confirmation Report — etcd-raft V02

## Final Result

Reproduced bugs: 2
Fixed prior findings: 3
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
| 7 | MC-1 | FIXED | no |
| 8 | MC-2 | REPRODUCED | yes |

## Entry 1: Empty-log restart no longer resets durable term and vote

- **Finding ID**: CR-1
- **Status**: FIXED
- **Source**: Persistent V00 finding, retained V01 recheck
- **Location**: `rawnode.go`, `bootstrap.go`

The explicit RawNode bootstrap API remains separate from restart construction.
The retained V01 evidence established that construction loads persisted state
instead of treating an empty log as a request to reset durable term and vote.
No changed V02 dependency invalidates that conclusion.

## Entry 2: Transfer during unapplied self-removal

- **Finding ID**: CR-2
- **Status**: NEEDS MORE INFO
- **Source**: Persistent V00 finding
- **Location**: `raft.go`

The earlier in-package result depended on a private network harness. The
supplied current evidence does not establish the same consequence through a
current public interface, so the retained disposition remains unchanged.

## Entry 3: Advance releases the configuration admission guard before ApplyConfChange

- **Finding ID**: CR-3
- **Status**: REPRODUCED
- **Source**: Persistent code-review finding, freshly rechecked
- **Location**: `raft.go`, `node.go`

The public asynchronous `Node` API commits a first membership entry, permits
the caller to acknowledge the Ready before applying that entry, and then
commits a second membership entry before the first call to `ApplyConfChange`.
The one-change-at-a-time admission boundary is therefore released before the
first membership transition becomes effective.

**Reproduction result:** `repro/CR-3/result.log` records the first membership
entry at index 3 and the second at index 4 before index 3 is applied. The
current public-interface control remains deterministic.

## Entry 4: Snapshot campaign scan duplicate

- **Finding ID**: CR-4
- **Status**: DROPPED
- **Source**: Persistent V00 disposition

This is the retained duplicate disposition. It is preserved for stable finding
identity and is not a current bug result.

## Entry 5: ReadIndex after leader self-removal

- **Finding ID**: CR-5
- **Status**: NEEDS MORE INFO
- **Source**: Persistent V00 finding
- **Location**: `raft.go`

The prior delayed-heartbeat scenario has not been adapted to the current public
bootstrap and joint-configuration APIs. Source correspondence alone is not
enough to assert the earlier external read consequence on this revision.

## Entry 6: Configuration proposal handoff under full quota

- **Finding ID**: CR-6
- **Status**: FIXED
- **Source**: Persistent V00 finding, retained V01 recheck
- **Location**: `node.go`, `raft.go`

The retained public-interface control shows the request in the next Ready once
the preceding batch releases the quota. No changed V02 dependency invalidates
that fixed disposition.

## Entry 7: Joint snapshot recovery drops the outgoing quorum

- **Finding ID**: MC-1
- **Status**: FIXED
- **Source**: Persistent V01 model-checking finding, freshly rechecked
- **Location**: `confchange/restore.go`, `raft.go`

V02 reconstructs incoming voters, outgoing voters, learners, staged learners,
and auto-leave state through `confchange.Restore`. The public RawNode control
restarts the joint state `{1,2,4} && {1,2,3}`, observes progress for all four
members, and leaves node 1 in `StateCandidate` when only the incoming majority
votes.

**Recheck result:** `repro/MC-1-control/result.log` records the complete
restored progress set and confirms that the outgoing majority still constrains
the election. This is an update-related fix of the V01 finding.

## Entry 8: Outgoing-only joint voter rejects a valid recovery snapshot

- **Finding ID**: MC-2
- **Status**: REPRODUCED
- **Source**: Fresh trace-validation counterexample and public RawNode confirmation
- **Location**: `raft.go:restore`

The live snapshot membership guard accepts only incoming voters and current
learners. It omits outgoing voters and staged learners even though they are full
members of a joint configuration. An outgoing-only voter therefore rejects a
newer valid joint snapshot after compaction and stays behind; if that voter is
needed for the outgoing majority, the joint configuration cannot make
quorum-backed progress.

**Reproduction result:** the 299-event source trace matched the complete
reference state and violated only `JointSnapshotMemberAcceptance`. The public
RawNode test in `repro/MC-2/result.log` then sent the valid index-5 snapshot
three times; every attempt was rejected and returned the stale index 4. The
supplied old-source control records the same rejection, so MC-2 is pre-existing
rather than introduced by V02. The durable record is
`spec/persistent-findings/MC-2.json`.

## Validation limits

The eleven fresh traces contain 5,778 events. Ten pass full correspondence and
the normal invariant suite; the eleventh consumes all 299 events under strict
correspondence and exposes MC-2 under its independently stated property. Six
source-backed update witnesses consume their complete queues and reach the
joint-entry, auto-leave, complete-recovery, learner-vote, post-Ready-output, and
outgoing-snapshot scenarios.

Standard, full-update, and focused TLC BFS checks reached their planned
30-minute budgets with nonempty frontiers and no unexpected property
violation. Five dedicated BFS hunts stopped on run-local state-storage
exhaustion after substantial partial exploration; the auto-leave hunt reached
its time budget. All six depth-100 simulations reached their planned budgets
without another violation. These bounded results are not exhaustive safety or
liveness proofs. External issue histories, later revisions, and excluded
system layers were not consulted. CR-2 and CR-5 remain unconfirmed on the
current public APIs for the reasons stated above.
