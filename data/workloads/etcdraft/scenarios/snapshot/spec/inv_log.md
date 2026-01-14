# Invariant Modification Log

## Record #1 - 2026-01-12

### Counterexample Summary
TLC found that `ConfigNonEmptyInv` was violated in the initial state. Servers s4 and s5 (not in InitServer) had empty configurations `<<{}, {}>>`, while s1, s2, s3 (in InitServer) had valid configurations `<<{s1, s2, s3}, {}>>`.

### Analysis Conclusion
- **Type**: A: Invariant Too Strong
- **Violated Property**: ConfigNonEmptyInv
- **Root Cause**: The invariant required ALL servers in the Server set to have non-empty configurations. However, servers that have not yet joined the cluster (s4, s5) are intentionally initialized with empty configurations. This is correct behavior - new servers start with empty config and only get a valid config when they join the cluster via snapshot or configuration change.

### Evidence from Implementation
- `tracker/tracker.go:129-137`: `MakeProgressTracker` initializes with empty Voters
- `MCetcdraft.tla:91`: `etcdInitConfigVars` correctly sets empty config for non-InitServer members

### Modifications Made
- **File**: etcdraft.tla
- **Before**:
```tla
\* Invariant: ConfigNonEmptyInv
\* At least one voter must exist (cluster must have quorum)
\* Reference: A Raft cluster cannot function without voters
ConfigNonEmptyInv ==
    \A i \in Server :
        GetConfig(i) /= {}
```
- **After**:
```tla
\* Invariant: ConfigNonEmptyInv
\* At least one voter must exist for initialized servers (cluster must have quorum)
\* Reference: A Raft cluster cannot function without voters
\* Note: Only applies to servers with currentTerm > 0 (initialized servers)
\*       Uninitialized servers (not yet joined) may have empty config
ConfigNonEmptyInv ==
    \A i \in Server :
        currentTerm[i] > 0 => GetConfig(i) /= {}
```

### User Confirmation
- Confirmation Time: 2026-01-12
- User Feedback: Approved

---

## Record #2 - 2026-01-12

### Counterexample Summary
Execution path:
1. State 1: Initial state, all s1-s3 logs have `offset=1, snapshotIndex=0`
2. State 2: s2 executes `CompactLog(s2, 3)`, log becomes `offset=3, snapshotIndex=2`, but **durableState not updated** (still `snapshotIndex=0`)
3. State 3: s3 restarts
4. State 4: s2 restarts, recovers from durableState. s2's log becomes:
   - `offset = 3` (retained from pre-crash)
   - `snapshotIndex = 0` (recovered from durableState)
   - **Violates invariant**: `snapshotIndex (0) ≠ offset (3) - 1`

### Analysis Conclusion
- **Type**: B: Spec Modeling Issue
- **Violated Property**: SnapshotOffsetConsistencyInv
- **Root Cause**: The `Restart` action had inconsistent modeling: `offset` retained the pre-crash value while `snapshotIndex` was recovered from durableState, causing a mismatch.

### Evidence from Implementation
- `storage.go:193-194`: `firstIndex()` returns `ms.ents[0].Index + 1`, which means firstIndex (offset in spec) is always `snapshotIndex + 1`

### Modifications Made
- **File**: etcdraft.tla
- **Before**:
```tla
/\ log' = [log EXCEPT ![i] = [
                offset |-> @.offset,
                entries |-> SubSeq(@.entries, 1, durableState[i].log - @.offset + 1),
                snapshotIndex |-> durableState[i].snapshotIndex,
                snapshotTerm |-> durableState[i].snapshotTerm
   ]]
```
- **After**:
```tla
\* Restore log from durableState: offset must equal snapshotIndex + 1
\* Entries are restored from historyLog since in-memory log may have been compacted
/\ log' = [log EXCEPT ![i] = [
                offset |-> durableState[i].snapshotIndex + 1,
                entries |-> SubSeq(historyLog[i], durableState[i].snapshotIndex + 1, durableState[i].log),
                snapshotIndex |-> durableState[i].snapshotIndex,
                snapshotTerm |-> durableState[i].snapshotTerm
   ]]
```

### User Confirmation
- Confirmation Time: 2026-01-12
- User Feedback: Approved

---

## Record #3 - 2026-01-12

### Counterexample Summary
s3 became Leader and executed `ClientRequest`, adding a new entry:
- s3's `LastIndex(log[s3]) = 4` (offset=3, 2 entries)
- s3's `matchIndex[s3][s3] = 3` (value set during `BecomeLeader`)

`ClientRequest` does not update `matchIndex[s3][s3]`, causing the invariant violation.

### Analysis Conclusion
- **Type**: A: Invariant Too Strong
- **Violated Property**: LeaderMatchSelfInv
- **Root Cause**: In etcd implementation, when Leader appends new entries, `matchIndex` is not updated immediately. Instead, the leader sends a self-reply message (MsgAppResp), and matchIndex is updated when that message is processed later.

### Evidence from Implementation
- `raft.go:836-845`: Leader sends `MsgAppResp` to itself after appending, and `matchIndex` is updated when this message is handled via `MaybeUpdate()`
- This means `matchIndex[leader][leader]` may temporarily lag behind `lastIndex` - this is normal behavior

### Modifications Made
- **File**: etcdraft.tla
- **Before**:
```tla
\* Invariant: LeaderMatchSelfInv
\* Leader's matchIndex for itself should equal its LastIndex
\* Reference: Leader always has all its own entries
LeaderMatchSelfInv ==
    \A i \in Server :
        state[i] = Leader => matchIndex[i][i] = LastIndex(log[i])
```
- **After**:
```tla
\* Invariant: LeaderMatchSelfInv
\* Leader's matchIndex for itself should not exceed its LastIndex
\* Note: matchIndex may temporarily lag behind lastIndex until MsgAppResp is processed
\* Reference: raft.go:836-845 - leader sends MsgAppResp to itself after appending
LeaderMatchSelfInv ==
    \A i \in Server :
        state[i] = Leader => matchIndex[i][i] <= LastIndex(log[i])
```

### User Confirmation
- Confirmation Time: 2026-01-12
- User Feedback: Approved

---

## Record #4 - 2026-01-12

### Counterexample Summary
s1 became Leader and executed `ClientRequest`, adding a new entry:
- s1's `LastIndex(log[s1]) = 4` (offset=3, 2 entries)
- s1's `nextIndex[s1][s1] = 4` (value set during `BecomeLeader`)
- Invariant required `nextIndex[s1][s1] = LastIndex + 1 = 5`

### Analysis Conclusion
- **Type**: A: Invariant Too Strong
- **Violated Property**: LeaderNextSelfInv
- **Root Cause**: Same as LeaderMatchSelfInv - `ClientRequest` does not update `nextIndex`, which is normal behavior since it's updated when MsgAppResp is processed.

### Modifications Made
- **File**: etcdraft.tla
- **Before**:
```tla
LeaderNextSelfInv ==
    \A i \in Server :
        state[i] = Leader => nextIndex[i][i] = LastIndex(log[i]) + 1
```
- **After**:
```tla
\* Note: nextIndex may temporarily lag behind until MsgAppResp is processed
LeaderNextSelfInv ==
    \A i \in Server :
        state[i] = Leader => nextIndex[i][i] <= LastIndex(log[i]) + 1
```

### User Confirmation
- Confirmation Time: 2026-01-12
- User Feedback: Approved

---

## Record #5 - 2026-01-12

### Counterexample Summary
`SendSnapshotWithCompaction(s1, s2, 1)` was executed when s1's log had already been compacted:
- s1's `log.snapshotIndex = 2` (entries up to index 2 already compacted)
- snapshoti = 1 (trying to send snapshot at index 1)
- `LogTerm(log[s1], 1)` returned 0 because index 1 is already compacted
- Message sent with `msnapshotTerm = 0`, violating `SnapshotMsgTermValidInv`

### Analysis Conclusion
- **Type**: B: Spec Modeling Issue
- **Violated Property**: SnapshotMsgTermValidInv
- **Root Cause**: `SendSnapshotWithCompaction` lacked a precondition to prevent sending snapshots for already-compacted entries. The action allowed `snapshoti < log[i].snapshotIndex`, which means the requested snapshot index was already compacted and `LogTerm` would return 0.

### Evidence from Implementation
- `raft.go:664-689`: `maybeSendSnapshot` checks `if sn.IsEmptySnap()` and returns early if true
- `node.go:126-129`: `IsEmptySnap` returns true when `sp.Metadata.Index == 0`
- The implementation ensures that snapshots with invalid (empty) metadata are never sent
- This implies the system should never try to send a snapshot for an index that has already been compacted

### Modifications Made
- **File**: etcdraft.tla
- **Before**:
```tla
SendSnapshotWithCompaction(i, j, snapshoti) ==
    /\ i /= j
    /\ state[i] = Leader
    /\ j \in GetConfig(i) \union GetLearners(i)
    /\ snapshoti <= commitIndex[i]  \* Can only snapshot committed entries
```
- **After**:
```tla
SendSnapshotWithCompaction(i, j, snapshoti) ==
    /\ i /= j
    /\ state[i] = Leader
    /\ j \in GetConfig(i) \union GetLearners(i)
    /\ snapshoti <= commitIndex[i]  \* Can only snapshot committed entries
    /\ snapshoti >= log[i].snapshotIndex  \* Must be >= current snapshotIndex (can't send compacted entries)
```

### User Confirmation
- Confirmation Time: 2026-01-12
- User Feedback: Approved

---

## Record #6 - 2026-01-12

### Counterexample Summary
TLC reported: "Successor state is not completely specified by action MCNextAsync. The following variable is not defined: messages."

The error occurred when `SendSnapshot` was executed. The action uses `Send(m)` which equals `SendDirect(m)`, and `SendDirect` only sets `pendingMessages'` without specifying `messages'`. The `UNCHANGED` clause was missing `messages`.

### Analysis Conclusion
- **Type**: B: Spec Modeling Issue
- **Violated Property**: N/A (TLC runtime error - variable not defined)
- **Root Cause**: `SendSnapshot` called `Send(m)` (which modifies `pendingMessages'`) but did not include `messages` in its `UNCHANGED` clause, leaving `messages'` undefined.

### Evidence from Implementation
- `Send(m) == SendDirect(m)` (etcdraft.tla:313)
- `SendDirect(m) == pendingMessages' = WithMessage(m, pendingMessages)` (etcdraft.tla:281-282)
- `SendDirect` only specifies `pendingMessages'`, not `messages'`

### Modifications Made
- **File**: etcdraft.tla
- **Before**:
```tla
    /\ ResetInflights(i, j)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, configVars, durableState>>
```
- **After**:
```tla
    /\ ResetInflights(i, j)
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, logVars, configVars, durableState, historyLog>>
```

### User Confirmation
- Confirmation Time: 2026-01-12
- User Feedback: Approved (implicit - part of batch fix)

---

## Record #7 - 2026-01-12

### Counterexample Summary
`HistoryLogLengthInv` was violated after s1 (follower) received new entries via AppendEntries from s2 (leader):
- s1's `log`: offset=3, 2 entries → `LastIndex = 4`
- s1's `historyLog`: length = 3
- Invariant requires: `Len(historyLog[i]) = LastIndex(log[i])`

### Analysis Conclusion
- **Type**: B: Spec Modeling Issue
- **Violated Property**: HistoryLogLengthInv
- **Root Cause**: `NoConflictAppendEntriesRequest` updates `log` when follower receives new entries, but does not update `historyLog` (ghost variable). The ghost variable must be kept consistent with the log to track full entry history.

### Evidence from Implementation
- `historyLog` is defined as "Ghost variable for verification: keeps the full history of entries" (etcdraft.tla:102)
- In real system, `raft.go:1797` calls `r.raftLog.maybeAppend()` which appends entries to the log
- `log.go:125` calls `l.append(a.entries[ci-offset:]...)` to store entries
- The ghost variable `historyLog` must mirror the log growth to maintain the invariant

### Modifications Made
- **File**: etcdraft.tla
- **Before**:
```tla
NoConflictAppendEntriesRequest(i, j, index, m) ==
    ...
    /\ log' = [log EXCEPT ![i].entries = @ \o SubSeq(m.mentries, LastIndex(log[i])-index+2, Len(m.mentries))]
    ...
    /\ UNCHANGED <<serverVars, durableState, progressVars, historyLog>>
```
- **After**:
```tla
NoConflictAppendEntriesRequest(i, j, index, m) ==
    ...
    \* Update both log and historyLog to keep ghost variable consistent
    /\ LET newEntries == SubSeq(m.mentries, LastIndex(log[i])-index+2, Len(m.mentries))
       IN /\ log' = [log EXCEPT ![i].entries = @ \o newEntries]
          /\ historyLog' = [historyLog EXCEPT ![i] = @ \o newEntries]
    ...
    /\ UNCHANGED <<serverVars, durableState, progressVars>>
```

Also updated `HandleAppendEntriesRequest` to remove `historyLog` from UNCHANGED (since sub-actions now manage it individually).

### User Confirmation
- Confirmation Time: 2026-01-12
- User Feedback: Approved

---

## Record #8 - 2026-01-12

### Counterexample Summary
TLC found `QuorumLogInv` violated with warnings: "The variable historyLog was changed while it is specified as UNCHANGED at line 837" and "line 761". The invariant violation was a false positive caused by TLC state corruption due to these spec inconsistencies.

### Analysis Conclusion
- **Type**: B: Spec Modeling Issue
- **Violated Property**: QuorumLogInv (false positive)
- **Root Cause**: Multiple actions call `Replicate(i, v, t)` which updates `historyLog` at line 740:
  ```tla
  /\ historyLog' = [historyLog EXCEPT ![i] = Append(@, entry)]
  ```
  However, these actions incorrectly include `historyLog` in their UNCHANGED clauses, creating contradictory state transitions.

### Evidence from Implementation
N/A - Pure spec modeling error. The `Replicate` helper explicitly modifies `historyLog`, but calling actions incorrectly declare it UNCHANGED.

### Modifications Made
- **File**: etcdraft.tla
- **Changes**: Removed `historyLog` from UNCHANGED in 5 actions that call `Replicate`:

1. **Line 761** (`ClientRequestAndSend`):
```tla
\* Before:
/\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, commitIndex, configVars, durableState, progressVars, historyLog>>
\* After:
/\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, commitIndex, configVars, durableState, progressVars>>
```

2. **Line 837** (`AddNewServer`):
```tla
\* Before:
/\ UNCHANGED <<messageVars, serverVars, candidateVars, matchIndex, commitIndex, configVars, durableState, progressVars, historyLog>>
\* After:
/\ UNCHANGED <<messageVars, serverVars, candidateVars, matchIndex, commitIndex, configVars, durableState, progressVars>>
```

3. **Line 850** (`AddLearner`):
```tla
\* Before:
/\ UNCHANGED <<messageVars, serverVars, candidateVars, matchIndex, commitIndex, configVars, durableState, progressVars, historyLog>>
\* After:
/\ UNCHANGED <<messageVars, serverVars, candidateVars, matchIndex, commitIndex, configVars, durableState, progressVars>>
```

4. **Line 863** (`DeleteServer`):
```tla
\* Before:
/\ UNCHANGED <<messageVars, serverVars, candidateVars, matchIndex, commitIndex, configVars, durableState, progressVars, historyLog>>
\* After:
/\ UNCHANGED <<messageVars, serverVars, candidateVars, matchIndex, commitIndex, configVars, durableState, progressVars>>
```

5. **Line 907** (`ChangeConfAndSend`):
```tla
\* Before:
/\ UNCHANGED <<messages, serverVars, candidateVars, matchIndex, commitIndex, configVars, durableState, progressVars, historyLog>>
\* After:
/\ UNCHANGED <<messages, serverVars, candidateVars, matchIndex, commitIndex, configVars, durableState, progressVars>>
```

### User Confirmation
- Confirmation Time: 2026-01-12
- User Feedback: Approved

---

## Record #9 - 2026-01-12

### Counterexample Summary
s2 became Leader in term 3 with `votedFor[s2] = s2`. Then s2 executed `DeleteServer(s2, s2)` to remove itself from the cluster. After `ApplySimpleConfChange`, s2's config became `{s1, s3}` (excluding s2). The invariant `VotedForInConfigInv` was violated because `votedFor[s2] = s2` but `s2 ∉ GetConfig(s2)`.

### Analysis Conclusion
- **Type**: A: Invariant Too Strong (removed as meaningless)
- **Violated Property**: VotedForInConfigInv
- **Root Cause**: The invariant assumed `votedFor` must always be in the current config. However, `votedFor` is term-specific - it records who the server voted for in the current term. Config changes can remove the voted-for server from the cluster without invalidating the vote.

### Evidence from Implementation
- `raft.go:784-788`: `Vote` is only reset when term changes, not on config changes
- Config changes do NOT reset `Vote` - the vote remains valid for the entire term

### Modifications Made
- **File**: MCetcdraft.cfg
- **Change**: Removed `VotedForInConfigInv` from INVARIANTS section (invariant is meaningless)

### User Confirmation
- Confirmation Time: 2026-01-12
- User Feedback: Approved - remove the invariant entirely

---

## Record #10 - 2026-01-12

### Counterexample Summary
s2 was Leader with config `{s1, s3}` (had removed itself via DeleteServer). Then `ApplySimpleConfChange` applied a config entry that re-added s2, changing config to `{s1, s2, s3}`. Since `addedNodes = {s2}`, the code set `progressState[s2][s2] = StateProbe`, but s2 is the Leader, violating `LeaderSelfReplicateInv`.

### Analysis Conclusion
- **Type**: B: Spec Modeling Issue
- **Violated Property**: LeaderSelfReplicateInv
- **Root Cause**: In `ApplySimpleConfChange`, when initializing progress for newly added nodes, the spec incorrectly includes the leader itself. A leader should never reset its own progress state to StateProbe.

### Evidence from Implementation
In `tracker/tracker.go`, when progress is initialized for new nodes, the leader never resets its own progress state. The leader's self-progress is always StateReplicate.

### Modifications Made
- **File**: etcdraft.tla
- **Change**: Exclude the leader itself from addedNodes when setting progressState in `ApplySimpleConfChange`:
```tla
\* Before (line 931-932):
/\ progressState' = [progressState EXCEPT ![i] =
       [j \in Server |-> IF j \in addedNodes THEN StateProbe ELSE progressState[i][j]]]

\* After:
/\ progressState' = [progressState EXCEPT ![i] =
       [j \in Server |-> IF j \in addedNodes /\ j # i THEN StateProbe ELSE progressState[i][j]]]
```

### User Confirmation
- Confirmation Time: 2026-01-12
- User Feedback: Approved

---

## Record #11 - 2026-01-12

### Counterexample Summary
61-step counterexample:
1. s3 became Leader in term 3, appended entries to its log (indices 4-12)
2. s3 applied config change entry, updating its config to `{s1, s2, s3, s5}`
3. s3 stepped down to Follower (currentTerm = 4)
4. `FollowerAdvanceCommitIndex` action advanced s3's commitIndex from 3 to 4
5. Entry at index 4 was NEVER replicated to a quorum - only s3 has it
6. QuorumLogInv failed because for quorum `{s1, s2, s5}`, none have entry 4 in their historyLog

### Analysis Conclusion
- **Type**: B: Spec Modeling Issue
- **Violated Property**: QuorumLogInv
- **Root Cause**: The `FollowerAdvanceCommitIndex` action is too permissive. It allows any non-leader to advance its commitIndex to any log entry without verifying that the entry has been quorum-committed. In real Raft, a follower only advances commitIndex based on `m.Commit` from leader messages.

### Evidence from Implementation
From `raft.go:1832-1834`:
```go
func (r *raft) handleHeartbeat(m pb.Message) {
	r.raftLog.commitTo(m.Commit)  // Only advances to what leader says
	r.send(pb.Message{To: m.From, Type: pb.MsgHeartbeatResp, Context: m.Context})
}
```

From `log.go:320-328`:
```go
func (l *raftLog) commitTo(tocommit uint64) {
	if l.committed < tocommit {
		if l.lastIndex() < tocommit {
			l.logger.Panicf(...)
		}
		l.committed = tocommit
	}
}
```

A follower NEVER independently decides to advance its commitIndex - it only responds to leader messages.

### Modifications Made
- **File**: MCetcdraft.tla
- **Change**: Removed the `FollowerAdvanceCommitIndex` action from `MCNextAsync`:
```tla
\* Before (lines 285-288):
    \* FollowerAdvanceCommitIndex: Follower advances commit (e.g., from test harness)
    \/ /\ \E i \in Server : \E c \in commitIndex[i]+1..LastIndex(log[i]) :
           etcd!FollowerAdvanceCommitIndex(i, c)
       /\ UNCHANGED faultVars

\* After:
    \* NOTE: FollowerAdvanceCommitIndex removed - it allows invalid states where
    \* a follower advances commitIndex beyond what has been quorum-committed.
    \* In real Raft, followers only advance commitIndex based on leader messages.
```

### User Confirmation
- Confirmation Time: 2026-01-12
- User Feedback: Approved

---

## Record #12 - 2026-01-12

### Counterexample Summary
36-step counterexample:
1. s2 became Leader in term 4, appended a joint config entry at index 4 (changing to `{s4}` with old config `{s1, s2, s3}`)
2. s2's `commitIndex = 3` (the joint config entry at index 4 is NOT committed)
3. `ApplySnapshotConfChange` action applied the uncommitted config entry from `historyLog[s2]`
4. s2's config changed to joint config `<<{s4}, {s1, s2, s3}>>`
5. `QuorumLogInv` failed because `GetConfig(s2) = {s4}`, but `historyLog[s4]` is empty

### Analysis Conclusion
- **Type**: B: Spec Modeling Issue
- **Violated Property**: QuorumLogInv
- **Root Cause**: The `ApplySnapshotConfChange` action in MCetcdraft.tla (lines 335-344) applies config from `historyLog` without checking if the config entry is committed. This allows uncommitted config entries to be applied, which is incorrect.

### Evidence from Implementation
From `node.go:179-183`:
```go
// ApplyConfChange applies a config change (previously passed to
// ProposeConfChange) to the node. This must be called whenever a config
// change is observed in Ready.CommittedEntries, except when the app decides
// to reject the configuration change (i.e. treats it as a noop instead), in
// which case it must not be called.
```

In the real implementation, `ApplyConfChange` is only called when a config change appears in `Ready.CommittedEntries` - i.e., only after the entry is committed.

### Modifications Made
- **File**: MCetcdraft.tla
- **Change**: Added constraint to ensure only committed config entries are applied:
```tla
\* Before (lines 341-343):
           IN /\ newVoters /= {}
              /\ newVoters /= GetConfig(i)  \* Only apply if config differs
              /\ etcd!ApplySnapshotConfChange(i, newVoters)

\* After:
           IN /\ newVoters /= {}
              /\ newVoters /= GetConfig(i)  \* Only apply if config differs
              /\ lastConfigIdx <= commitIndex[i]  \* Only apply committed configs
              /\ etcd!ApplySnapshotConfChange(i, newVoters)
```

### User Confirmation
- Confirmation Time: 2026-01-12
- User Feedback: Approved

---

## Record #13 - 2026-01-12

### Counterexample Summary
55-step counterexample:
1. s2 is Leader with `nextIndex[s2][s3] = 4`, `matchIndex[s2][s3] = 3`
2. `AppendEntries(s2, s3, <<5, 6>>)` action sends entry at index 5 (skipping index 4)
3. After action: `inflights[s2][s3] = {5}`, `nextIndex[s2][s3] = 5`
4. `InflightsBelowNextInv` violated because `5 < 5` is FALSE

### Analysis Conclusion
- **Type**: B: Spec Modeling Issue
- **Violated Property**: InflightsBelowNextInv
- **Root Cause**: MCetcdraft.tla allows `AppendEntries` to send entries from arbitrary ranges starting at `matchIndex+1`, but the real implementation always sends from `nextIndex`. When the spec sends entries from a higher index (skipping entries), the nextIndex update becomes inconsistent with inflights.

### Evidence from Implementation
From `raft.go:616-638`:
```go
func (r *raft) maybeSendAppend(to uint64, sendIfEmpty bool) bool {
    pr := r.trk.Progress[to]
    ...
    prevIndex := pr.Next - 1  // Always uses pr.Next
    ...
    ents, err = r.raftLog.entries(pr.Next, r.maxMsgSize)  // Always from pr.Next
```

From `tracker/progress.go:165-171`:
```go
func (pr *Progress) SentEntries(entries int, bytes uint64) {
    case StateReplicate:
        if entries > 0 {
            pr.Next += uint64(entries)        // Update Next first
            pr.Inflights.Add(pr.Next-1, bytes) // Then add inflight = Next-1
        }
```

The implementation guarantees `inflight = Next-1 < Next`, but only when entries are sent from `pr.Next`.

### Modifications Made
- **File**: MCetcdraft.tla
- **Change**: Constrain AppendEntries to only send from nextIndex:
```tla
\* Before (line 267-268):
    \* NOTE: Range must start at max(matchIndex+1, log.offset) to handle compacted logs
    \/ /\ \E i,j \in Server : \E b,e \in Max({matchIndex[i][j]+1, log[i].offset})..LastIndex(log[i])+1 : etcd!AppendEntries(i, j, <<b,e>>)

\* After:
    \* NOTE: Entries must be sent starting from nextIndex (per raft.go:638)
    \* Implementation always sends from pr.Next, not from arbitrary positions
    \/ /\ \E i,j \in Server : \E e \in nextIndex[i][j]..LastIndex(log[i])+1 : etcd!AppendEntries(i, j, <<nextIndex[i][j], e>>)
```

### User Confirmation
- Confirmation Time: 2026-01-12
- User Feedback: Approved

---

## Record #14 - 2026-01-12

### Counterexample Summary
66-step counterexample:
1. s1 is Leader with `progressState[s1][s3] = "StateReplicate"`, `inflights[s1][s3] = {4}`
2. `ReportUnreachable(s1, s3)` action transitions s3 to StateProbe
3. After action: `progressState[s1][s3] = "StateProbe"` but `inflights[s1][s3] = {4}` (not cleared)
4. `InflightsOnlyInReplicateInv` violated: non-Replicate state has non-empty inflights

### Analysis Conclusion
- **Type**: B: Spec Modeling Issue
- **Violated Property**: InflightsOnlyInReplicateInv
- **Root Cause**: `ReportUnreachable` in etcdraft.tla did not clear inflights when transitioning to StateProbe, but the real implementation's `BecomeProbe()` calls `ResetState()` which clears `pr.Inflights`.

### Evidence from Implementation
From `tracker/progress.go:121-126`:
```go
func (pr *Progress) ResetState(state StateType) {
    pr.MsgAppFlowPaused = false
    pr.PendingSnapshot = 0
    pr.State = state
    pr.Inflights.reset()  // Clears inflights on any state transition
}
```

From `tracker/progress.go:130-142`:
```go
func (pr *Progress) BecomeProbe() {
    ...
    pr.ResetState(StateProbe)  // Calls ResetState which clears inflights
    ...
}
```

### Modifications Made
- **File**: etcdraft.tla
- **Change**: Clear inflights when ReportUnreachable transitions to StateProbe:
```tla
\* Before (line 1403-1411):
ReportUnreachable(i, j) ==
    /\ state[i] = Leader
    /\ i # j
    /\ IF progressState[i][j] = StateReplicate
       THEN progressState' = [progressState EXCEPT ![i][j] = StateProbe]
       ELSE UNCHANGED progressState
    /\ UNCHANGED <<... inflights ...>>

\* After:
ReportUnreachable(i, j) ==
    /\ state[i] = Leader
    /\ i # j
    /\ IF progressState[i][j] = StateReplicate
       THEN /\ progressState' = [progressState EXCEPT ![i][j] = StateProbe]
            /\ inflights' = [inflights EXCEPT ![i][j] = {}]
       ELSE UNCHANGED <<progressState, inflights>>
    /\ UNCHANGED <<serverVars, candidateVars, messageVars, logVars, configVars,
                   durableState, leaderVars, nextIndex, pendingSnapshot,
                   msgAppFlowPaused, historyLog>>
```

### User Confirmation
- Confirmation Time: 2026-01-12
- User Feedback: Approved

---

## Record #15 - 2026-01-12

### Counterexample Summary
70-step counterexample:
1. s2 is Leader with `pendingConfChangeIndex[s2] = 4`, `commitIndex[s2] = 3`
2. `AdvanceCommitIndex(s2)` action advances commitIndex to 4
3. After action: `pendingConfChangeIndex[s2] = 4`, `commitIndex[s2] = 4`
4. `PendingConfIndexAboveCommitInv` violated: `4 > 4` is FALSE

### Analysis Conclusion
- **Type**: A: Invariant Too Strong
- **Violated Property**: PendingConfIndexAboveCommitInv
- **Root Cause**: The invariant uses `commitIndex` but the implementation (`raft.go:1318`) compares against `applied`. Since `applied` can lag behind `committed`, there can be valid states where `commitIndex >= pendingConfIndex > applied`. The TLA+ spec doesn't model `applied`, making this invariant incompatible with the abstraction.

### Evidence from Implementation
From `raft.go:1318`:
```go
alreadyPending := r.pendingConfIndex > r.raftLog.applied
```
The implementation compares against `applied`, not `committed`. These two indices have different semantics - entries can be committed but not yet applied.

### Modifications Made
- **File**: etcdraft.tla
- **Change**: Removed `PendingConfIndexAboveCommitInv` invariant completely
- Lines 2228-2234 (invariant definition) removed
- Reference in `AdditionalConfigInv` removed

### User Confirmation
- Confirmation Time: 2026-01-12
- User Feedback: Remove the invariant

---

## Record #16 - 2026-01-13

### Counterexample Summary
79-step counterexample:
1. s1 became Leader in term 3 with config `{s1, s2, s3}` (simple config, NOT joint)
2. `ChangeConf(s1)` appended a config entry at index 4 with `enterJoint = FALSE` and `newconf = {s1, s2, s4}`
3. s1 committed index 4 using old config's quorum `{s1, s3}` (both had matchIndex >= 4)
4. `ApplySnapshotConfChange` applied the committed config, changing s1's config to `{s1, s2, s4}`
5. `QuorumLogInv` failed: for quorum `{s2, s4}` in the new config, neither has index 4 in historyLog
   - historyLog[s2] has only 3 entries
   - historyLog[s4] is empty

### Analysis Conclusion
- **Type**: B: Spec Modeling Issue
- **Violated Property**: QuorumLogInv
- **Root Cause**: The `ChangeConf` and `ChangeConfAndSend` actions allowed arbitrary `enterJoint` values without checking the current config state. This violated the joint consensus protocol:
  - `enterJoint = TRUE` (enter joint) should only be allowed when NOT in joint config
  - `enterJoint = FALSE` (leave joint) should only be allowed when IN joint config

  By allowing `enterJoint = FALSE` in a non-joint config, the spec skipped the joint consensus phase entirely, committing a config change using only the old config's quorum without requiring the new config's nodes to participate.

### Evidence from Implementation
From `confchange/confchange.go`:
```go
func (c Changer) LeaveJoint() (tracker.Config, tracker.ProgressMap, error) {
    if !joint(c.Tracker.Config) {
        return c.err(errors.New("can't leave a non-joint config"))
    }
    ...
}
```

The implementation explicitly checks that LeaveJoint can only be called when currently in a joint config. The spec was missing this constraint.

### Modifications Made
- **File**: etcdraft.tla
- **Changes**: Added joint consensus constraints to `ChangeConf` and `ChangeConfAndSend`:

1. **ChangeConf (lines 873-876)**:
```tla
\* Before:
\E newVoters \in SUBSET Server, newLearners \in SUBSET Server, enterJoint \in {TRUE, FALSE}:
    /\ Replicate(i, [newconf |-> newVoters, ...], ConfigEntry)

\* After:
\E newVoters \in SUBSET Server, newLearners \in SUBSET Server, enterJoint \in {TRUE, FALSE}:
    \* Joint consensus constraint: must follow proper sequencing
    /\ (enterJoint = TRUE) => ~IsJointConfig(i)   \* Can only enter joint if not already in joint
    /\ (enterJoint = FALSE) => IsJointConfig(i)   \* Can only leave joint if currently in joint
    /\ Replicate(i, [newconf |-> newVoters, ...], ConfigEntry)
```

2. **ChangeConfAndSend (lines 891-894)**: Same constraint added.

### User Confirmation
- Confirmation Time: 2026-01-13
- User Feedback: Approved

---
