# Violation Analysis Report

Generated: 2026-01-14

This document contains detailed analysis of 12 TLC violations found during simulation of the etcdraft spec.

## Summary

| # | Violation | Type | Status |
|---|-----------|------|--------|
| 1 | MonotonicTermProp | A: Property Too Strong | **Fixed** |
| 2 | QuorumLogInv | A: Invariant Too Strong | **Fixed** (Record #17) |
| 3 | LearnersVotersDisjointInv | B: Spec Modeling Error | **Fixed** |
| 4 | ConfigNonEmptyInv | B: Spec Modeling Error | **Fixed** (with #3) |
| 5 | MonotonicMatchIndexProp | B: Spec Modeling Error | **Fixed** |
| 6 | JointConfigNonEmptyInv | B: Spec Modeling Error | **Fixed** (with #3) |
| 7 | tlc-exception1.out (SubSeq -16) | B: Spec Modeling Error | **Fixed** |
| 8 | PendingConfIndexValidInv | B: Spec Modeling Error | **Fixed** |
| 9 | DurableStateConsistency | A: Invariant Too Strong | **Fixed** |
| 10 | HistoryLogLengthInv | B: Spec Modeling Error | **Fixed** |
| 11 | LogMatchingInv | B: Spec Modeling Error | **Fixed** |
| 12 | CurrentTermAtLeastLogTerm | B: Spec Modeling Error | **Fixed** |

**Statistics:**
- Type A (Invariant/Property Too Strong): 3
- Type B (Spec Modeling Error): 9
- Type C (Real System Bug): 0

---

## Violation #1: MonotonicTermProp

**File:** `MonotonicTermProp.violated`
**Type:** A - Property Too Strong
**Trace Length:** 4 steps
**Severity:** Low
**Status:** **FIXED**

### Property Definition (Before Fix)

```tla
MonotonicTermProp ==
    [][\A i \in Server :
        currentTerm'[i] >= currentTerm[i]]_mc_vars
```

### Violation Scenario

| State | Action | s3.currentTerm | s3.durableState.currentTerm |
|-------|--------|----------------|------------------------------|
| 1 | MCInit | 1 | 1 |
| 2 | MCTimeout(s3) | 2 | 1 (not persisted) |
| 3 | MCRestart(s4) | 2 | 1 |
| 4 | MCRestart(s3) | **1** | 1 |

### Root Cause

When s3 times out (state 2), it increments `currentTerm` to 2 but hasn't persisted this change yet (`durableState.currentTerm` is still 1). When s3 restarts (state 4), it recovers from `durableState`, so `currentTerm` reverts to 1.

This is **normal Raft behavior** - a node that crashes before persisting a term increment will lose that increment on restart.

### Conclusion

The property is too strong. It expects `currentTerm` to be monotonically increasing, but doesn't account for restart recovery from durable state.

### Fix Applied

Exclude Restart action from the property (MCetcdraft.tla:385-387):
```tla
MonotonicTermProp ==
    [][(~\E i \in Server: Restart(i)) =>
        \A i \in Server : currentTerm'[i] >= currentTerm[i]]_mc_vars
```

### Review Decision

- [x] Fixed - Exclude Restart action from property check

---

## Violation #2: QuorumLogInv

**File:** `QuorumLogInv.violated`
**Type:** A - Invariant Too Strong
**Trace Length:** 101 steps
**Severity:** Low
**Status:** **FIXED** (inv_log.md Record #17)

### Invariant Definition (Before Fix)

```tla
QuorumLogInv ==
    \A i \in Server :
    \A S \in Quorum(GetConfig(i)) :
        \E j \in S :
            IsPrefix(Committed(i), historyLog[j])
```

### Violation Scenario

In joint config with:
- Incoming config: `{s1, s3, s4, s5}`
- Outgoing config: `{s1, s2, s3}`

The incoming quorum `{s3, s4, s5}` doesn't have the committed data, but the outgoing quorum `{s1, s2}` does.

### Root Cause

The invariant only checks the incoming config's quorum, ignoring that in joint consensus, the outgoing config's quorum can also provide safety guarantee (since election requires majority from BOTH configs).

### Fix Applied

```tla
QuorumLogInv ==
    \A i \in Server :
        \/ \A S \in Quorum(GetConfig(i)) :
               \E j \in S : IsPrefix(Committed(i), historyLog[j])
        \/ (IsJointConfig(i) /\
            \A S \in Quorum(GetOutgoingConfig(i)) :
                \E j \in S : IsPrefix(Committed(i), historyLog[j]))
```

### Review Decision

- [x] Fixed

---

## Violation #3: LearnersVotersDisjointInv

**File:** `LearnersVotersDisjointInv.violated`
**Type:** B - Spec Modeling Error
**Trace Length:** 123 steps
**Severity:** Medium
**Status:** **FIXED**

### Invariant Definition

```tla
LearnersVotersDisjointInv ==
    \A i \in Server :
        GetLearners(i) \cap (GetConfig(i) \cup GetOutgoingConfig(i)) = {}
```

This invariant comes from etcd source code (`tracker/tracker.go:37-41`):
> Invariant: Learners and Voters does not intersect, i.e. if a peer is in either half of the joint config, it can't be a learner

### Violation Scenario

Final state shows s2's config:
```
config[s2] = [
    learners: {s3, s5},
    jointConfig: [{s5}, {s1, s2, s3}]
]
```

**Problem:**
- `s5` is in both `learners` AND `jointConfig[0]` (incoming voters)
- `s3` is in both `learners` AND `jointConfig[1]` (outgoing voters)

### Root Cause

The `ChangeConf` action (etcdraft.tla:874) allows arbitrary selection of `newVoters` and `newLearners`:

```tla
\E newVoters \in SUBSET Server, newLearners \in SUBSET Server, enterJoint \in {TRUE, FALSE}:
    ...
```

There is **no constraint** that `newVoters \cap newLearners = {}`.

In etcd, this is enforced by `checkInvariants()` in `confchange/confchange.go:305-316`:
```go
for id := range cfg.Learners {
    if _, ok := outgoing(cfg.Voters)[id]; ok {
        return fmt.Errorf("%d is in Learners and Voters[1]", id)
    }
    if _, ok := incoming(cfg.Voters)[id]; ok {
        return fmt.Errorf("%d is in Learners and Voters[0]", id)
    }
}
```

### Offending Log Entry

```json
{
  "newconf": ["s5"],
  "learners": ["s3", "s5"],
  "enterJoint": true,
  "oldconf": ["s1", "s2", "s3"]
}
```

### Fix Applied

Added constraints to `ChangeConf` and `ChangeConfAndSend` (etcdraft.tla:879-880, 900-901):

```tla
\E newVoters \in SUBSET Server, newLearners \in SUBSET Server, enterJoint \in {TRUE, FALSE}:
    /\ (enterJoint = TRUE) => ~IsJointConfig(i)
    /\ (enterJoint = FALSE) => IsJointConfig(i)
    \* Configuration validity constraints (Reference: confchange/confchange.go)
    /\ newVoters \cap newLearners = {}            \* checkInvariants: Learners and voters must be disjoint
    /\ newVoters /= {}                            \* apply(): "removed all voters" check
    /\ Replicate(...)
```

### Review Decision

- [x] Fixed - Added learners/voters disjoint constraint and non-empty voters constraint

---

## Violation #4: ConfigNonEmptyInv

**File:** `ConfigNonEmptyInv.violated`
**Type:** B - Spec Modeling Error
**Trace Length:** 129 steps
**Severity:** Medium
**Status:** **FIXED** (with Violation #3)

### Invariant Definition

```tla
ConfigNonEmptyInv ==
    \A i \in Server :
        currentTerm[i] > 0 => GetConfig(i) /= {}
```

### Violation Scenario

Final state:
```
currentTerm[s4] = 4
config[s4].jointConfig = [[], []]  \* Empty!
```

s4's `currentTerm` is 4 (initialized), but its config is empty.

### Root Cause

The `ChangeConf` action allowed `newVoters = {}`, which could lead to empty configurations being replicated.

### Fix Applied

This was fixed together with Violation #3. The `newVoters /= {}` constraint was added to `ChangeConf` and `ChangeConfAndSend` (etcdraft.tla:879-880, 900-901):

```tla
/\ newVoters /= {}  \* apply(): "removed all voters" check
```

This prevents configuration changes that would result in empty voter sets, ensuring `GetConfig(i) /= {}` for initialized nodes.

### Review Decision

- [x] Fixed - `newVoters /= {}` constraint prevents empty configurations

---

## Violation #5: MonotonicMatchIndexProp

**File:** `MonotonicMatchIndexProp.violated`
**Type:** B - Spec Modeling Error
**Trace Length:** 139 steps
**Severity:** Medium
**Status:** **FIXED**

### Property Definition

```tla
MonotonicMatchIndexProp ==
    [][(~ \E i \in Server: etcd!BecomeLeader(i)) =>
            (\A i,j \in Server : matchIndex'[i][j] >= matchIndex[i][j])]_mc_vars
```

### Violation Scenario

| State | Action | s3.state | matchIndex[s3][s3] |
|-------|--------|----------|-------------------|
| 137 | MCNextAsync | Leader | 19 |
| 138 | MCNextDynamic | Leader | 19 |
| 139 | MCNextDynamic | Leader | **0** |

s3 remained Leader (no BecomeLeader), but `matchIndex[s3][s3]` dropped from 19 to 0.

### Root Cause

In `ApplySimpleConfChange` (etcdraft.tla:929-942):

```tla
addedNodes == newConfig \ oldConfig
...
matchIndex' = [matchIndex EXCEPT ![i] =
    [j \in Server |-> IF j \in addedNodes THEN 0 ELSE matchIndex[i][j]]]
```

When s3 (Leader) enters joint config, the outgoing config members (including s3 itself) are added to `addedNodes`, causing s3's own matchIndex to be reset to 0.

**Note:** The `progressState` update correctly excludes `j # i`, but `matchIndex` did not!

### etcd Code Reference

In `confchange/confchange.go`, the `makeVoter()` function (lines 178-189):

```go
func (c Changer) makeVoter(cfg *tracker.Config, trk tracker.ProgressMap, id uint64) {
    pr := trk[id]
    if pr == nil {
        c.initProgress(cfg, trk, id, false /* isLearner */)  // Only new nodes get Match=0
        return
    }
    // Existing nodes (including leader) keep their Match value!
    pr.IsLearner = false
    ...
}
```

**Key insight:** etcd only initializes `Match=0` for nodes not already in the ProgressMap (`pr == nil`). The leader is always in the ProgressMap, so its Match is never reset.

### Fix Applied

Added `j # i` constraint to exclude leader from matchIndex reset (etcdraft.tla:946-949):

```tla
\* Reference: confchange/confchange.go makeVoter() - only init Match=0 for truly new nodes
\* Existing nodes (including leader itself) keep their Match value (pr != nil check)
/\ matchIndex' = [matchIndex EXCEPT ![i] =
       [j \in Server |-> IF j \in addedNodes /\ j # i THEN 0 ELSE matchIndex[i][j]]]
```

This is consistent with the `progressState` update which already had `j # i`.

### Review Decision

- [x] Fixed - Added `j # i` constraint to match etcd behavior and progressState handling

---

## Violation #6: JointConfigNonEmptyInv

**File:** `JointConfigNonEmptyInv.violated`
**Type:** B - Spec Modeling Error
**Trace Length:** 105 steps
**Severity:** Medium
**Status:** **FIXED** (with Violation #3)

### Invariant Definition

```tla
JointConfigNonEmptyInv ==
    \A i \in Server :
        IsJointConfig(i) =>
            /\ GetConfig(i) /= {}
            /\ GetOutgoingConfig(i) /= {}
```

### Violation Scenario

Final state shows s2's config:
```
config[s2] = [
    learners: {s1, s2},
    jointConfig: [[], {s1, s2}]  \* incoming is EMPTY!
]
```

s2 is in joint config, but the incoming config (`jointConfig[0]`) is empty.

### Root Cause

The `ChangeConf` action allows `newVoters = {}`:

```tla
\E newVoters \in SUBSET Server, ...
```

### Offending Log Entry

```json
{
  "newconf": [],
  "learners": ["s1", "s2"],
  "enterJoint": true,
  "oldconf": ["s1", "s2"]
}
```

### Fix Applied

This was fixed together with Violation #3. The `newVoters /= {}` constraint was added to `ChangeConf` and `ChangeConfAndSend` (etcdraft.tla:879-880, 900-901):

```tla
\E newVoters \in SUBSET Server, newLearners \in SUBSET Server, enterJoint \in {TRUE, FALSE}:
    /\ (enterJoint = TRUE) => ~IsJointConfig(i)
    /\ (enterJoint = FALSE) => IsJointConfig(i)
    \* Configuration validity constraints (Reference: confchange/confchange.go)
    /\ newVoters \cap newLearners = {}            \* checkInvariants: Learners and voters must be disjoint
    /\ newVoters /= {}                            \* apply(): "removed all voters" check
    /\ Replicate(...)
```

### Review Decision

- [x] Fixed - `newVoters /= {}` constraint prevents empty incoming config in joint state

---

## Violation #7: tlc-exception1.out (SubSeq -16)

**File:** `tlc-exception1.out`
**Type:** B - Spec Modeling Error
**Trace Length:** 143 steps
**Severity:** High (crashes TLC)
**Status:** **FIXED**

### Error Message

```
The second argument of SubSeq must be in the domain of its first argument:
<< ... (8 elements) >>
, but instead it is -16
```

### Detailed Analysis

**State 143 key data:**
- s2 is Leader
- `log[s2].offset = 22`, `entries = 8 elements` → LastIndex = 29
- `nextIndex[s2][s1] = 5`
- `matchIndex[s2][s1] = 4`

**Problem calculation in `AppendEntriesInRangeToPeer` (etcdraft.tla:543):**
```tla
entries == SubSeq(log[i].entries, range[1] - log[i].offset + 1, lastEntry - log[i].offset + 1)
```

When `range[1] = nextIndex[s2][s1] = 5` and `log[s2].offset = 22`:
```
startIndex = 5 - 22 + 1 = -16  ← Invalid!
```

### Root Cause

In `MCetcdraft.tla:275`:
```tla
\/ /\ \E i,j \in Server : \E e \in nextIndex[i][j]..LastIndex(log[i])+1 :
       etcd!AppendEntries(i, j, <<nextIndex[i][j], e>>)
```

**Problem:** No check that `nextIndex[i][j] >= log[i].offset`.

When the leader's log is compacted (e.g., `offset = 22`), but `nextIndex[j] = 5` (follower is far behind), the spec tries to send entries starting from index 5, which no longer exists in the log.

**In real etcd:** When `nextIndex < log.offset`, the leader sends a snapshot instead of AppendEntries. This is correctly modeled in `SendSnapshot`:
```tla
SendSnapshot(i, j) ==
    ...
    \* Trigger: The previous log index required for AppendEntries is NOT available
    /\ LET prevLogIndex == nextIndex[i][j] - 1 IN
       ~IsAvailable(i, prevLogIndex)
```

### Fix Applied

Added precondition to `AppendEntries` call in `MCetcdraft.tla:275`:

```tla
\* NOTE: Entries must be sent starting from nextIndex (per raft.go:638)
\* Implementation always sends from pr.Next, not from arbitrary positions
\* IMPORTANT: Only send AppendEntries if entries are available (not compacted)
\* If nextIndex < log.offset, must send snapshot instead (handled by SendSnapshot)
\/ /\ \E i,j \in Server :
       /\ nextIndex[i][j] >= log[i].offset  \* Entries must be available
       /\ \E e \in nextIndex[i][j]..LastIndex(log[i])+1 :
              etcd!AppendEntries(i, j, <<nextIndex[i][j], e>>)
   /\ UNCHANGED faultVars
```

### Review Decision

- [x] Fixed - Added `nextIndex[i][j] >= log[i].offset` precondition

---

## Violation #8: PendingConfIndexValidInv

**File:** `PendingConfIndexValidInv.violated`
**Type:** B - Spec Modeling Error
**Trace Length:** 86 steps
**Severity:** Medium
**Status:** **FIXED**

### Invariant Definition

```tla
PendingConfIndexValidInv ==
    \A i \in Server :
        (state[i] = Leader /\ pendingConfChangeIndex[i] > 0) =>
            /\ pendingConfChangeIndex[i] <= LastIndex(log[i])
            /\ pendingConfChangeIndex[i] >= log[i].offset
            /\ LogEntry(i, pendingConfChangeIndex[i]).type = ConfigEntry
```

### Violation Scenario

Final state:
```
state[s2] = Leader
pendingConfChangeIndex[s2] = 3
log[s2].offset = 7
```

**Problem:** `pendingConfChangeIndex (3) < log.offset (7)`

The entry at index 3 has been compacted (removed from log), but `pendingConfChangeIndex` still points to it.

### Root Cause

The `CompactLog` action allowed compacting up to `commitIndex + 1`, but in etcd the application layer (etcdserver) is responsible for only compacting applied entries.

From `storage.go:249-250`:
```go
// It is the application's responsibility to not attempt to compact an index
// greater than raftLog.applied.
```

The spec was missing this application-layer constraint.

### Fix Applied

Changed `CompactLog` constraint from `commitIndex` to `durableState.log` (which represents applied/persisted index):

```tla
\* Reference: storage.go:249-250 - "It is the application's responsibility to not
\* attempt to compact an index greater than raftLog.applied."
\* We use durableState.log as applied index (set by PersistState in Ready).
CompactLog(i, newStart) ==
    /\ newStart > log[i].offset
    /\ newStart <= durableState[i].log + 1  \* Changed from commitIndex[i] + 1
    ...
```

This ensures compact only affects applied entries, so `pendingConfChangeIndex` (pointing to un-applied config) is protected.

### Review Decision

- [x] Fixed - Use `durableState.log` (applied) instead of `commitIndex` for compact bound

---

## Violation #9: DurableStateConsistency

**File:** `DurableStateConsistency.violated`
**Type:** A - Invariant Too Strong
**Trace Length:** 112 steps
**Severity:** Low
**Status:** **FIXED**

### Invariant Definition (Before Fix)

```tla
DurableStateConsistency ==
    \A i \in Server :
        /\ durableState[i].currentTerm <= currentTerm[i]
        /\ durableState[i].log <= LastIndex(log[i])  \* This check was too strong
        /\ durableState[i].commitIndex <= commitIndex[i]
```

### Violation Scenario

Final state for s3:
```
durableState[s3].log = 12
LastIndex(log[s3]) = 11  \* (offset=3, entries=9)
```

**Problem:** `durableState.log (12) > LastIndex(log) (11)`

### Root Cause Analysis

When log is truncated (e.g., due to conflict resolution), `durableState.log` temporarily exceeds `LastIndex(log)` until the next Ready/PersistState sync.

However, per review discussion:
- etcd's HardState only contains `Term`, `Vote`, `Commit` - NOT `lastIndex`
- The `durableState.log` in spec is an abstraction, not directly from etcd
- Only `currentTerm` and `commitIndex` consistency matters for correctness
- Log index can temporarily be inconsistent between memory and durable state

### Fix Applied

Removed the `durableState.log <= LastIndex(log)` check from the invariant (etcdraft.tla:2042-2045):

```tla
\* Note: durableState.log check removed - only term and commitIndex need comparison
DurableStateConsistency ==
    \A i \in Server :
        /\ durableState[i].currentTerm <= currentTerm[i]
        /\ durableState[i].commitIndex <= commitIndex[i]
```

### Review Decision

- [x] Fixed - Removed unnecessary log index check (invariant was too strong)

---

## Violation #10: HistoryLogLengthInv

**File:** `HistoryLogLengthInv.violated`
**Type:** B - Spec Modeling Error
**Trace Length:** 124 steps
**Severity:** Medium
**Status:** **FIXED**

### Invariant Definition

```tla
HistoryLogLengthInv ==
    \A i \in Server :
        LastIndex(log[i]) >= 0 =>
            Len(historyLog[i]) = LastIndex(log[i])
```

### Violation Scenario

Final state for s3:
```
LastIndex(log[s3]) = 3  \* (offset=3, entries=1)
Len(historyLog[s3]) = 4
```

**Problem:** `Len(historyLog) (4) > LastIndex(log) (3)`

historyLog[s3] has an extra entry that log[s3] doesn't have.

### Root Cause

`ConflictAppendEntriesRequest` truncates `log` but leaves `historyLog` unchanged:

```tla
\* Before fix:
ConflictAppendEntriesRequest(i, index, m) ==
    ...
    /\ log' = [log EXCEPT ![i].entries = SubSeq(@, 1, Len(@) - 1)]
    /\ UNCHANGED <<..., historyLog>>  \* BUG: historyLog not truncated
```

In etcd, `log.go:138` calls `truncateAndAppend` which removes conflicting entries entirely. The ghost variable `historyLog` should mirror this behavior.

### Fix Applied

Truncate `historyLog` along with `log` in `ConflictAppendEntriesRequest` (etcdraft.tla:1148-1152):

```tla
ConflictAppendEntriesRequest(i, index, m) ==
    ...
    \* Truncate both log and historyLog to keep ghost variable consistent
    \* Reference: log.go:138 truncateAndAppend - conflicting entries are removed
    /\ log' = [log EXCEPT ![i].entries = SubSeq(@, 1, Len(@) - 1)]
    /\ historyLog' = [historyLog EXCEPT ![i] = SubSeq(@, 1, Len(@) - 1)]
    /\ UNCHANGED <<messageVars, serverVars, commitIndex, durableState, progressVars>>
```

### Review Decision

- [x] Fixed - Truncate historyLog along with log in ConflictAppendEntriesRequest

---

## Violation #11: LogMatchingInv

**File:** `LogMatchingInv.violated`
**Type:** B - Spec Modeling Error
**Trace Length:** 138 steps
**Severity:** **HIGH**
**Status:** **FIXED**

### Invariant Definition

```tla
LogMatchingInv ==
    \A i, j \in Server :
        \A n \in (1..Len(historyLog[i])) \cap (1..Len(historyLog[j])) :
            historyLog[i][n].term = historyLog[j][n].term =>
            SubSeq(historyLog[i],1,n) = SubSeq(historyLog[j],1,n)
```

### Violation Scenario

From State 138 trace analysis:

| Server | historyLog[4] | Length |
|--------|---------------|--------|
| s2 | term=5, ConfigEntry {s1,s2,s3,s4} | 37 entries |
| s3 | term=4, ConfigEntry {s1,s2,s3,s5} | 5 entries |

A pending AppendEntriesRequest from s2 to s3:
- `prevLogIndex=3, prevLogTerm=1` (matches s3's log)
- `mentries=[{term:5, ConfigEntry}, {term:5, ValueEntry}, ...]`

When s3 processes this, it detects conflict at index 4 (term 4 vs 5).

### Root Cause

**Problem in `ConflictAppendEntriesRequest`:** The original implementation only truncated ONE entry at a time:

```tla
\* BEFORE (WRONG):
ConflictAppendEntriesRequest(i, index, m) ==
    ...
    /\ log' = [log EXCEPT ![i].entries = SubSeq(@, 1, Len(@) - 1)]  \* Only truncates ONE entry!
    /\ UNCHANGED <<messageVars, ...>>  \* No response sent, message not consumed!
```

**etcd actual behavior** (`log.go:115-128` + `log.go:152-165`):
1. `findConflict()` finds the FIRST conflicting index
2. `truncateAndAppend()` truncates to conflict point AND appends new entries
3. This is an **atomic operation** - truncate + append + respond

The spec's non-atomic approach allowed:
1. Partial truncation (only removing last entry)
2. Message remaining in queue (no response sent)
3. Meanwhile, other operations could modify the log
4. Eventually leading to divergent logs with same term at same index

### Fix Applied

Added `FindFirstConflict` helper and rewrote `ConflictAppendEntriesRequest` to match etcd's atomic behavior (etcdraft.tla:1119-1183):

```tla
\* Reference: log.go:152-165 findConflict
FindFirstConflict(i, index, ents) ==
    LET conflicting == {k \in 1..Len(ents):
            /\ index + k - 1 <= LastIndex(log[i])
            /\ LogTerm(i, index + k - 1) /= ents[k].term}
    IN IF conflicting = {} THEN 0 ELSE index + Min(conflicting) - 1

\* Reference: log.go:115-128 maybeAppend + log_unstable.go:196-218 truncateAndAppend
ConflictAppendEntriesRequest(i, j, index, m) ==
    /\ m.mentries /= << >>
    /\ index > commitIndex[i]
    /\ ~HasNoConflict(i, index, m.mentries)
    /\ LET ci == FindFirstConflict(i, index, m.mentries)
           entsOffset == ci - index + 1
           newEntries == SubSeq(m.mentries, entsOffset, Len(m.mentries))
           truncatePoint == ci - log[i].offset
       IN /\ ci > commitIndex[i]
          \* ATOMIC: truncate to conflict point AND append new entries
          /\ log' = [log EXCEPT ![i].entries = SubSeq(@, 1, truncatePoint - 1) \o newEntries]
          /\ historyLog' = [historyLog EXCEPT ![i] = SubSeq(@, 1, ci - 1) \o newEntries]
    \* Send response (consuming the message)
    /\ CommitTo(i, Min({m.mcommitIndex, m.mprevLogIndex + Len(m.mentries)}))
    /\ Reply([mtype |-> AppendEntriesResponse, msuccess |-> TRUE, ...], m)
    /\ UNCHANGED <<serverVars, durableState, progressVars>>
```

### Key Differences from Original

| Aspect | Original (Wrong) | Fixed (Matches etcd) |
|--------|------------------|----------------------|
| Truncation | Only last entry | To conflict point |
| Append | Not done | Atomic with truncate |
| Response | Not sent | Sent immediately |
| Message | Stays in queue | Consumed |

### Review Decision

- [x] Fixed - Atomic truncate+append matching etcd's `maybeAppend` + `truncateAndAppend`

---

## Violation #12: CurrentTermAtLeastLogTerm

**File:** `CurrentTermAtLeastLogTerm.violated`
**Type:** B - Spec Modeling Error
**Trace Length:** 125 steps
**Severity:** Medium
**Status:** **FIXED**

### Invariant Definition

```tla
CurrentTermAtLeastLogTerm ==
    \A i \in Server :
        \A idx \in 1..LastIndex(log[i]) :
            currentTerm[i] >= LogTerm(i, idx)
```

### Violation Scenario

Final state for s4:
```
currentTerm[s4] = 0
log[s4].offset = 4
log[s4].snapshotIndex = 3
log[s4].snapshotTerm = 1
```

**Problem:** `currentTerm (0) < snapshotTerm (1)`

s4 received a snapshot with term 1, but its currentTerm is still 0.

### Root Cause Analysis

**The bug is in `HandleSnapshotRequest`'s precondition: `m.mterm >= currentTerm[i]`**

This is inconsistent with all other message handlers in the spec:

| Handler | Condition | Correct? |
|---------|-----------|----------|
| HandleRequestVoteRequest | `m.mterm <= currentTerm[i]` | ✓ |
| HandleRequestVoteResponse | `m.mterm = currentTerm[i]` | ✓ |
| HandleAppendEntriesRequest | `m.mterm <= currentTerm[i]` | ✓ |
| HandleAppendEntriesResponse | `m.mterm = currentTerm[i]` | ✓ |
| HandleHeartbeatResponse | `m.mterm = currentTerm[i]` | ✓ |
| **HandleSnapshotRequest** | `m.mterm >= currentTerm[i]` | **✗** |
| HandleSnapshotStatus | `m.mterm = currentTerm[i]` | ✓ |

**etcd's Step() function control flow (raft.go:1085-1179):**

```
Step(m):
├── m.Term > r.Term:
│   ├── MsgPreVote: don't update term, continue
│   ├── MsgPreVoteResp && !Reject: don't update term, continue
│   └── Others (MsgSnap included): becomeFollower(m.Term) → continue processing
│
├── m.Term == r.Term: continue processing directly
│
└── m.Term < r.Term:
    ├── MsgApp/MsgHeartbeat: send MsgAppResp, return (don't process)
    └── Others (MsgSnap included): ignore, return (don't process)

Continue processing → switch m.Type → r.step(m) → handleSnapshot
```

**Key insight:** When `m.Term > r.Term`, etcd first updates term via `becomeFollower()`, then continues to process the message. The spec's `ReceiveDirect` handles this via `UpdateTerm` action, which requires handlers to have `m.mterm <= currentTerm[i]` condition.

**Bug mechanism:**
1. s4 has `currentTerm = 0`
2. Snapshot message arrives with `m.mterm = 1`
3. `HandleSnapshotRequest` condition `m.mterm >= currentTerm[i]` (1 >= 0) is satisfied
4. Snapshot is processed directly **without calling UpdateTerm first**
5. Result: `snapshotTerm = 1` but `currentTerm = 0` → Invariant violated

### Fix Applied

Changed `HandleSnapshotRequest` condition from `>=` to `<=`, and added stale term handling (etcdraft.tla:1377-1383):

```tla
HandleSnapshotRequest(i, j, m) ==
    /\ m.mterm <= currentTerm[i]  \* Changed from >= to <=
    /\ IF m.mterm < currentTerm[i] THEN
           \* Stale term: ignore snapshot message entirely
           \* Reference: raft.go:1173-1177 - "ignored a %s message with lower term"
           /\ Discard(m)
           /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, ...>>
       ELSE IF m.msnapshotIndex <= commitIndex[i] THEN
           \* Case 1: Stale snapshot...
       ELSE IF LogTerm(i, m.msnapshotIndex) = m.msnapshotTerm THEN
           \* Case 2: Fast-forward...
       ELSE
           \* Case 3: Actual Restore...
```

**Now the flow is correct:**
1. s4 has `currentTerm = 0`
2. Snapshot message arrives with `m.mterm = 1`
3. `HandleSnapshotRequest` condition `m.mterm <= currentTerm[i]` (1 <= 0) is **NOT** satisfied
4. `UpdateTerm` condition `m.mterm > currentTerm[i]` (1 > 0) is satisfied → updates `currentTerm = 1`
5. Message stays in queue
6. Next step: `HandleSnapshotRequest` condition (1 <= 1) is satisfied → process snapshot
7. Result: Both `snapshotTerm = 1` and `currentTerm = 1` → Invariant satisfied

### Review Decision

- [x] Fixed - Changed condition from `>=` to `<=`, matching other handlers and etcd's Step() control flow

---

## Appendix: Related Files

- Spec files: `etcdraft.tla`, `MCetcdraft.tla`, `MCetcdraft.cfg`
- Previous fixes: `inv_log.md` (Record #17 for QuorumLogInv)
- Violation files: All in `violations/` directory

## Next Steps

1. ~~Review each violation decision~~ ✓ All 12 violations analyzed
2. ~~Implement accepted fixes~~ ✓ All fixes implemented
3. Re-run simulation to verify fixes
4. ~~**Priority:** Investigate LogMatchingInv violation (#11)~~ ✓ Fixed

**All 12 violations have been fixed!**
