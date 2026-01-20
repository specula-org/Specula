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

## Record #17 - 2026-01-14

### Counterexample Summary
76-step counterexample:
1. s1 became Leader in term 2 with config `{s1, s2, s3}`
2. `ChangeConf(s1)` appended a joint config entry at index 4 with `enterJoint = TRUE`, changing to `{s1, s3, s4, s5}` with old config `{s1, s2, s3}`
3. s1 committed index 4 using old config's quorum `{s1, s2}` (both had matchIndex >= 4)
4. `ApplySimpleConfChange` applied the committed config, s1 entered joint config `<<{s1, s3, s4, s5}, {s1, s2, s3}>>`
5. `QuorumLogInv` failed: for quorum `{s3, s4, s5}` in the new (incoming) config, none have index 4 in historyLog
   - s3, s4, s5 have empty or shorter historyLog
   - But old config's quorum `{s1, s2}` DOES have index 4

### Analysis Conclusion
- **Type**: A: Invariant Too Strong
- **Violated Property**: QuorumLogInv
- **Root Cause**: The invariant only checked the incoming config (`GetConfig(i)` = `jointConfig[1]`), ignoring the outgoing config in joint consensus. However, in joint consensus, safety is guaranteed as long as EITHER the incoming OR outgoing quorum holds the committed data, because:
  - Election requires majority from BOTH configs simultaneously
  - If the outgoing quorum blocks (has data), no candidate without data can win
  - The committed entry will eventually propagate to incoming quorum nodes

### Evidence from Implementation
From `quorum/joint.go:27-41`:
```go
func (c JointConfig) CommittedIndex(l AckedIndexer) Index {
    idx0 := c[0].CommittedIndex(l)  // incoming
    idx1 := c[1].CommittedIndex(l)  // outgoing
    if idx0 < idx1 {
        return idx0
    }
    return idx1
}
```

Election in joint config requires both quorums. From `quorum/joint.go:45-55`:
```go
func (c JointConfig) VoteResult(votes map[uint64]bool) VoteResult {
    r0 := c[0].VoteResult(votes)  // incoming must agree
    r1 := c[1].VoteResult(votes)  // outgoing must agree
    // Both must succeed for election to win
}
```

This means: if outgoing quorum has the data, any candidate without data cannot get votes from outgoing quorum, so cannot become leader.

### Modifications Made
- **File**: etcdraft.tla
- **Before (lines 1665-1669)**:
```tla
\* All committed entries are contained in the log
\* of at least one server in every quorum
QuorumLogInv ==
    \A i \in Server :
    \A S \in Quorum(GetConfig(i)) :
        \E j \in S :
            IsPrefix(Committed(i), historyLog[j])
```
- **After**:
```tla
\* All committed entries are contained in the log
\* of at least one server in every quorum.
\* In joint config, it's safe if EITHER incoming OR outgoing quorums hold the data,
\* because election requires both quorums, so one blocking is enough.
QuorumLogInv ==
    \A i \in Server :
        \/ \A S \in Quorum(GetConfig(i)) :
               \E j \in S : IsPrefix(Committed(i), historyLog[j])
        \/ (IsJointConfig(i) /\
            \A S \in Quorum(GetOutgoingConfig(i)) :
                \E j \in S : IsPrefix(Committed(i), historyLog[j]))
```

### User Confirmation
- Confirmation Time: 2026-01-14
- User Feedback: Approved

---

## Record #18 - 2026-01-14

### Counterexample Summary
4-step counterexample:
1. State 1: MCInit - s3.currentTerm = 1, s3.durableState.currentTerm = 1
2. State 2: MCTimeout(s3) - s3.currentTerm = 2, but durableState.currentTerm = 1 (not persisted yet)
3. State 3: MCRestart(s4)
4. State 4: MCRestart(s3) - s3 recovers from durableState, currentTerm reverts to 1

### Analysis Conclusion
- **Type**: A: Property Too Strong
- **Violated Property**: MonotonicTermProp
- **Root Cause**: The property expected `currentTerm` to be monotonically increasing, but didn't account for restart recovery from durable state. When a node crashes before persisting a term increment, it loses that increment on restart. This is normal Raft behavior.

### Evidence from Implementation
When s3 times out (state 2), it increments `currentTerm` to 2 but hasn't persisted this change yet (`durableState.currentTerm` is still 1). When s3 restarts (state 4), it recovers from `durableState`, so `currentTerm` reverts to 1.

### Modifications Made
- **File**: MCetcdraft.tla
- **Before**:
```tla
MonotonicTermProp ==
    [][\A i \in Server :
        currentTerm'[i] >= currentTerm[i]]_mc_vars
```
- **After**:
```tla
MonotonicTermProp ==
    [][(~\E i \in Server: Restart(i)) =>
        \A i \in Server : currentTerm'[i] >= currentTerm[i]]_mc_vars
```

### User Confirmation
- Confirmation Time: 2026-01-14
- User Feedback: Approved

---

## Record #19 - 2026-01-14

### Counterexample Summary
123-step counterexample: s2's config showed:
```
config[s2] = [
    learners: {s3, s5},
    jointConfig: [{s5}, {s1, s2, s3}]
]
```
- s5 is in both `learners` AND `jointConfig[0]` (incoming voters)
- s3 is in both `learners` AND `jointConfig[1]` (outgoing voters)

### Analysis Conclusion
- **Type**: B: Spec Modeling Error
- **Violated Property**: LearnersVotersDisjointInv
- **Root Cause**: The `ChangeConf` action (etcdraft.tla:874) allowed arbitrary selection of `newVoters` and `newLearners` without the constraint `newVoters \cap newLearners = {}`.

### Evidence from Implementation
From `tracker/tracker.go:37-41`:
> Invariant: Learners and Voters does not intersect, i.e. if a peer is in either half of the joint config, it can't be a learner

From `confchange/confchange.go:305-316`, `checkInvariants()` enforces this:
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

### Modifications Made
- **File**: etcdraft.tla
- **Changes**: Added constraints to `ChangeConf` and `ChangeConfAndSend` (lines 879-880, 900-901):
```tla
\E newVoters \in SUBSET Server, newLearners \in SUBSET Server, enterJoint \in {TRUE, FALSE}:
    /\ (enterJoint = TRUE) => ~IsJointConfig(i)
    /\ (enterJoint = FALSE) => IsJointConfig(i)
    \* Configuration validity constraints (Reference: confchange/confchange.go)
    /\ newVoters \cap newLearners = {}            \* checkInvariants: Learners and voters must be disjoint
    /\ newVoters /= {}                            \* apply(): "removed all voters" check
    /\ Replicate(...)
```

**Note**: This fix also resolves Violations #4 (ConfigNonEmptyInv) and #6 (JointConfigNonEmptyInv) via the `newVoters /= {}` constraint.

### User Confirmation
- Confirmation Time: 2026-01-14
- User Feedback: Approved

---

## Record #20 - 2026-01-14

### Counterexample Summary
139-step counterexample:
1. State 137: s3 is Leader, `matchIndex[s3][s3] = 19`
2. State 138: s3 remains Leader
3. State 139: `matchIndex[s3][s3] = 0` (dropped from 19 to 0!)

s3 remained Leader (no BecomeLeader), but its own matchIndex was reset.

### Analysis Conclusion
- **Type**: B: Spec Modeling Error
- **Violated Property**: MonotonicMatchIndexProp
- **Root Cause**: In `ApplySimpleConfChange`, when s3 (Leader) enters joint config, the outgoing config members (including s3 itself) are added to `addedNodes`, causing s3's own matchIndex to be reset to 0. The `progressState` update correctly excluded `j # i`, but `matchIndex` did not.

### Evidence from Implementation
From `confchange/confchange.go`, the `makeVoter()` function (lines 178-189):
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
etcd only initializes `Match=0` for nodes not already in the ProgressMap (`pr == nil`). The leader is always in the ProgressMap, so its Match is never reset.

### Modifications Made
- **File**: etcdraft.tla
- **Before**:
```tla
/\ matchIndex' = [matchIndex EXCEPT ![i] =
       [j \in Server |-> IF j \in addedNodes THEN 0 ELSE matchIndex[i][j]]]
```
- **After** (lines 946-949):
```tla
\* Reference: confchange/confchange.go makeVoter() - only init Match=0 for truly new nodes
\* Existing nodes (including leader itself) keep their Match value (pr != nil check)
/\ matchIndex' = [matchIndex EXCEPT ![i] =
       [j \in Server |-> IF j \in addedNodes /\ j # i THEN 0 ELSE matchIndex[i][j]]]
```

### User Confirmation
- Confirmation Time: 2026-01-14
- User Feedback: Approved

---

## Record #21 - 2026-01-14

### Counterexample Summary
143-step counterexample causing TLC crash:
```
The second argument of SubSeq must be in the domain of its first argument:
<< ... (8 elements) >>
, but instead it is -16
```

State 143 key data:
- s2 is Leader with `log[s2].offset = 22`, entries = 8 elements → LastIndex = 29
- `nextIndex[s2][s1] = 5`, `matchIndex[s2][s1] = 4`

When calculating `SubSeq` in `AppendEntriesInRangeToPeer`:
- `startIndex = 5 - 22 + 1 = -16` (Invalid!)

### Analysis Conclusion
- **Type**: B: Spec Modeling Error
- **Violated Property**: N/A (TLC runtime error - SubSeq domain violation)
- **Root Cause**: `MCetcdraft.tla:275` had no check that `nextIndex[i][j] >= log[i].offset`. When the leader's log is compacted (`offset = 22`) but `nextIndex[j] = 5`, the spec tried to send entries starting from index 5, which no longer exists. In real etcd, when `nextIndex < log.offset`, the leader sends a snapshot instead.

### Evidence from Implementation
The `SendSnapshot` action correctly models this:
```tla
SendSnapshot(i, j) ==
    ...
    \* Trigger: The previous log index required for AppendEntries is NOT available
    /\ LET prevLogIndex == nextIndex[i][j] - 1 IN
       ~IsAvailable(i, prevLogIndex)
```

### Modifications Made
- **File**: MCetcdraft.tla
- **Before**:
```tla
\/ /\ \E i,j \in Server : \E e \in nextIndex[i][j]..LastIndex(log[i])+1 :
       etcd!AppendEntries(i, j, <<nextIndex[i][j], e>>)
```
- **After** (line 275):
```tla
\* NOTE: Entries must be sent starting from nextIndex (per raft.go:638)
\* IMPORTANT: Only send AppendEntries if entries are available (not compacted)
\* If nextIndex < log.offset, must send snapshot instead (handled by SendSnapshot)
\/ /\ \E i,j \in Server :
       /\ nextIndex[i][j] >= log[i].offset  \* Entries must be available
       /\ \E e \in nextIndex[i][j]..LastIndex(log[i])+1 :
              etcd!AppendEntries(i, j, <<nextIndex[i][j], e>>)
   /\ UNCHANGED faultVars
```

### User Confirmation
- Confirmation Time: 2026-01-14
- User Feedback: Approved

---

## Record #22 - 2026-01-14

### Counterexample Summary
86-step counterexample:
- s2 is Leader with `pendingConfChangeIndex[s2] = 3`
- `log[s2].offset = 7`
- Invariant requires `pendingConfChangeIndex >= log.offset`
- But `3 < 7` - the entry at index 3 has been compacted!

### Analysis Conclusion
- **Type**: B: Spec Modeling Error
- **Violated Property**: PendingConfIndexValidInv
- **Root Cause**: The `CompactLog` action allowed compacting up to `commitIndex + 1`, but etcd's application layer (etcdserver) only compacts applied entries.

### Evidence from Implementation
From `storage.go:249-250`:
```go
// It is the application's responsibility to not attempt to compact an index
// greater than raftLog.applied.
```

### Modifications Made
- **File**: etcdraft.tla
- **Before**:
```tla
CompactLog(i, newStart) ==
    /\ newStart > log[i].offset
    /\ newStart <= commitIndex[i] + 1
    ...
```
- **After**:
```tla
\* Reference: storage.go:249-250 - "It is the application's responsibility to not
\* attempt to compact an index greater than raftLog.applied."
\* We use durableState.log as applied index (set by PersistState in Ready).
CompactLog(i, newStart) ==
    /\ newStart > log[i].offset
    /\ newStart <= durableState[i].log + 1  \* Changed from commitIndex[i] + 1
    ...
```

### User Confirmation
- Confirmation Time: 2026-01-14
- User Feedback: Approved

---

## Record #23 - 2026-01-14

### Counterexample Summary
112-step counterexample:
- s3: `durableState[s3].log = 12`
- s3: `LastIndex(log[s3]) = 11` (offset=3, entries=9)
- Invariant required `durableState.log <= LastIndex(log)`
- But `12 > 11`

### Analysis Conclusion
- **Type**: A: Invariant Too Strong
- **Violated Property**: DurableStateConsistency
- **Root Cause**: When log is truncated (e.g., due to conflict resolution), `durableState.log` temporarily exceeds `LastIndex(log)` until the next Ready/PersistState sync. Per review:
  - etcd's HardState only contains `Term`, `Vote`, `Commit` - NOT `lastIndex`
  - The `durableState.log` in spec is an abstraction
  - Only `currentTerm` and `commitIndex` consistency matters for correctness

### Modifications Made
- **File**: etcdraft.tla
- **Before**:
```tla
DurableStateConsistency ==
    \A i \in Server :
        /\ durableState[i].currentTerm <= currentTerm[i]
        /\ durableState[i].log <= LastIndex(log[i])
        /\ durableState[i].commitIndex <= commitIndex[i]
```
- **After** (lines 2042-2045):
```tla
\* Note: durableState.log check removed - only term and commitIndex need comparison
DurableStateConsistency ==
    \A i \in Server :
        /\ durableState[i].currentTerm <= currentTerm[i]
        /\ durableState[i].commitIndex <= commitIndex[i]
```

### User Confirmation
- Confirmation Time: 2026-01-14
- User Feedback: Approved

---

## Record #24 - 2026-01-14

### Counterexample Summary
124-step counterexample:
- s3: `LastIndex(log[s3]) = 3` (offset=3, entries=1)
- s3: `Len(historyLog[s3]) = 4`
- Invariant requires `Len(historyLog) = LastIndex(log)`
- But `4 > 3` - historyLog has an extra entry

### Analysis Conclusion
- **Type**: B: Spec Modeling Error
- **Violated Property**: HistoryLogLengthInv
- **Root Cause**: `ConflictAppendEntriesRequest` truncated `log` but left `historyLog` unchanged. In etcd, `log.go:138` calls `truncateAndAppend` which removes conflicting entries entirely. The ghost variable `historyLog` must mirror this.

### Modifications Made
- **File**: etcdraft.tla
- **Before**:
```tla
ConflictAppendEntriesRequest(i, index, m) ==
    ...
    /\ log' = [log EXCEPT ![i].entries = SubSeq(@, 1, Len(@) - 1)]
    /\ UNCHANGED <<..., historyLog>>
```
- **After** (lines 1148-1152):
```tla
ConflictAppendEntriesRequest(i, index, m) ==
    ...
    \* Truncate both log and historyLog to keep ghost variable consistent
    \* Reference: log.go:138 truncateAndAppend - conflicting entries are removed
    /\ log' = [log EXCEPT ![i].entries = SubSeq(@, 1, Len(@) - 1)]
    /\ historyLog' = [historyLog EXCEPT ![i] = SubSeq(@, 1, Len(@) - 1)]
    /\ UNCHANGED <<messageVars, serverVars, commitIndex, durableState, progressVars>>
```

### User Confirmation
- Confirmation Time: 2026-01-14
- User Feedback: Approved

---

## Record #25 - 2026-01-14

### Counterexample Summary
138-step counterexample causing `LogMatchingInv` violation:
- s2 and s3 have same term at index 4, but different entries
- s2: `historyLog[4] = term=5, ConfigEntry {s1,s2,s3,s4}`
- s3: `historyLog[4] = term=4, ConfigEntry {s1,s2,s3,s5}`

### Analysis Conclusion
- **Type**: B: Spec Modeling Error
- **Violated Property**: LogMatchingInv (CRITICAL - core Raft safety property)
- **Root Cause**: The original `ConflictAppendEntriesRequest` only truncated ONE entry at a time and didn't consume the message. etcd's `maybeAppend` + `truncateAndAppend` performs an atomic truncate-to-conflict-point AND append operation.

### Evidence from Implementation
From `log.go:115-128` + `log.go:152-165`:
1. `findConflict()` finds the FIRST conflicting index
2. `truncateAndAppend()` truncates to conflict point AND appends new entries
3. This is an atomic operation - truncate + append + respond

### Modifications Made
- **File**: etcdraft.tla
- **Changes**: Added `FindFirstConflict` helper and rewrote `ConflictAppendEntriesRequest` (lines 1119-1183):

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
```

| Aspect | Original (Wrong) | Fixed (Matches etcd) |
|--------|------------------|----------------------|
| Truncation | Only last entry | To conflict point |
| Append | Not done | Atomic with truncate |
| Response | Not sent | Sent immediately |
| Message | Stays in queue | Consumed |

### User Confirmation
- Confirmation Time: 2026-01-14
- User Feedback: Approved

---

## Record #26 - 2026-01-14

### Counterexample Summary
125-step counterexample:
- s4: `currentTerm[s4] = 0`
- s4: `log[s4].snapshotTerm = 1`
- Invariant requires `currentTerm >= snapshotTerm`
- But `0 < 1`

s4 received a snapshot with term 1, but its currentTerm is still 0.

### Analysis Conclusion
- **Type**: B: Spec Modeling Error
- **Violated Property**: CurrentTermAtLeastLogTerm
- **Root Cause**: `HandleSnapshotRequest` had condition `m.mterm >= currentTerm[i]`, which is inconsistent with all other handlers that use `m.mterm <= currentTerm[i]`. This allowed processing a higher-term snapshot without first calling `UpdateTerm`.

### Evidence from Implementation
etcd's `Step()` function control flow (raft.go:1085-1179):
```
Step(m):
├── m.Term > r.Term:
│   └── Others (MsgSnap included): becomeFollower(m.Term) → continue processing
├── m.Term == r.Term: continue processing directly
└── m.Term < r.Term:
    └── Others (MsgSnap included): ignore, return
```

When `m.Term > r.Term`, etcd first updates term via `becomeFollower()`, then continues. The spec's `ReceiveDirect` handles this via `UpdateTerm` action, which requires handlers to have `m.mterm <= currentTerm[i]`.

### Modifications Made
- **File**: etcdraft.tla
- **Before**:
```tla
HandleSnapshotRequest(i, j, m) ==
    /\ m.mterm >= currentTerm[i]  \* WRONG
    ...
```
- **After** (lines 1377-1383):
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

**Correct flow after fix:**
1. s4 has `currentTerm = 0`
2. Snapshot message arrives with `m.mterm = 1`
3. `HandleSnapshotRequest` condition `1 <= 0` is NOT satisfied
4. `UpdateTerm` condition `1 > 0` is satisfied → updates `currentTerm = 1`
5. Next step: `HandleSnapshotRequest` condition `1 <= 1` is satisfied → process snapshot
6. Result: Both `snapshotTerm = 1` and `currentTerm = 1` → Invariant satisfied

### User Confirmation
- Confirmation Time: 2026-01-14
- User Feedback: Approved

---

## Record #27 - 2026-01-15

### Counterexample Summary
135-step counterexample:
1. s1 became Leader in term 5 with config `{s1, s2, s3}` (simple config)
2. `ChangeConf(s1)` executed with `enterJoint = TRUE`:
   - `newVoters = {s5}` (incoming config)
   - `newLearners = {s2, s3}`
   - `oldconf = {s1, s2, s3}` (becomes outgoing config)
3. s1's config changed to joint config `<<{s5}, {s1, s2, s3}>>` with `learners = {s2, s3}`
4. `LearnersVotersDisjointInv` violated: s2 and s3 are in both learners and outgoing voters (`jointConfig[1]`)

### Analysis Conclusion
- **Type**: B: Spec Modeling Issue
- **Violated Property**: LearnersVotersDisjointInv
- **Root Cause**: The previous fix (ANALYSIS_REPORT.md Violation #3) only added `newVoters \cap newLearners = {}`, which checks learners against **incoming** voters. However, when entering joint config (`enterJoint = TRUE`), the old config becomes the **outgoing** voters, and learners must also not intersect with those.

### Evidence from Implementation
From `confchange/confchange.go:305-312`:
```go
// Conversely Learners and Voters doesn't intersect at all.
for id := range cfg.Learners {
    if _, ok := outgoing(cfg.Voters)[id]; ok {
        return fmt.Errorf("%d is in Learners and Voters[1]", id)  // OUTGOING check
    }
    if _, ok := incoming(cfg.Voters)[id]; ok {
        return fmt.Errorf("%d is in Learners and Voters[0]", id)  // INCOMING check
    }
}
```

The implementation checks learners against BOTH incoming AND outgoing voters. The spec was missing the outgoing check.

### Modifications Made
- **File**: etcdraft.tla
- **Before** (lines 881-882):
```tla
\* Configuration validity constraints (Reference: confchange/confchange.go)
/\ newVoters \cap newLearners = {}            \* checkInvariants: Learners and voters must be disjoint
```
- **After** (lines 881-883):
```tla
\* Configuration validity constraints (Reference: confchange/confchange.go:305-312)
/\ newVoters \cap newLearners = {}            \* checkInvariants: Learners disjoint from incoming voters
/\ (enterJoint = TRUE) => (GetConfig(i) \cap newLearners = {})  \* checkInvariants: Learners disjoint from outgoing voters
```

Same change applied to `ChangeConfAndSend` (lines 907-909).

### User Confirmation
- Confirmation Time: 2026-01-15
- User Feedback: Approved

---

## Record #28 - 2026-01-15

### Counterexample Summary
80-step counterexample:
1. s4 is a new node (not in InitServer), starts with `currentTerm = 0` and empty config
2. Leader s2 has config `{s1, s2, s4}` (s4 was added via config change)
3. s2 sends heartbeat to s4 (mterm=4, mentries=empty)
4. s4 receives the heartbeat via `MCNextAsyncWithReady(s4)`
5. s4's `currentTerm` updated from 0 to 4 via `UpdateTerm`
6. s4 still has empty config and empty log (no entries received yet)
7. `ConfigNonEmptyInv` violated: `currentTerm[s4] = 4 > 0` but `GetConfig(s4) = {}`

### Analysis Conclusion
- **Type**: A: Invariant Too Strong
- **Violated Property**: ConfigNonEmptyInv
- **Root Cause**: The invariant `currentTerm > 0 => GetConfig /= {}` is too strong. A new node joining a cluster can have its term updated via `UpdateTerm` (from receiving messages) before it receives any log entries. This is valid behavior in the actual system.

### Evidence from Implementation
From `raft.go:1085-1122` (Step function):
```go
func (r *raft) Step(m pb.Message) error {
    // ...
    case m.Term > r.Term:
        // ...
        default:
            if m.Type == pb.MsgApp || m.Type == pb.MsgHeartbeat || m.Type == pb.MsgSnap {
                r.becomeFollower(m.Term, m.From)  // Updates term, no config check
            }
    // ...
}
```

From `confchange/restore.go:119-131`:
- When a node starts with empty ConfState, `Restore` returns empty config
- The node can receive messages and update term before receiving log entries

Scenario in actual system:
1. New node created (not bootstrapped) → empty config
2. Leader (who has new node in config) sends heartbeat
3. New node receives heartbeat, updates term
4. New node still has no log entries or config

### Modifications Made
- **File**: etcdraft.tla
- **Before** (lines 2181-2183):
```tla
\* Note: Only applies to servers with currentTerm > 0 (initialized servers)
\*       Uninitialized servers (not yet joined) may have empty config
ConfigNonEmptyInv ==
    \A i \in Server :
        currentTerm[i] > 0 => GetConfig(i) /= {}
```
- **After**:
```tla
\* Note: Only applies to servers with log entries (has received data)
\*       A new node can have term updated via UpdateTerm before receiving log entries
\*       Reference: raft.go:Step - no config check before processing messages
ConfigNonEmptyInv ==
    \A i \in Server :
        LastIndex(log[i]) > 0 => GetConfig(i) /= {}
```

### User Confirmation
- Confirmation Time: 2026-01-15
- User Feedback: Approved

---

## Record #29 - 2026-01-15

### Counterexample Summary
75-step counterexample:
1. State 74: s2 是 Leader，配置为 `<<{s2}, {}>>`（只有 s2 在配置中）
2. `matchIndex[s2][s1] = 4`（s1 之前在配置中时的遗留值）
3. State 75: s2 执行 ApplySimpleConfChange，进入 joint config
4. s2 的配置变为 `<<{s2}, {s1, s2}>>, learners |-> {s1}]`（s1 被重新添加）
5. 因为 s1 不在旧配置中，被识别为 `addedNodes`
6. `matchIndex[s2][s1]` 被重置为 0
7. MonotonicMatchIndexProp 违反：matchIndex 从 4 降到 0

### Analysis Conclusion
- **Type**: A: Property Too Strong
- **Violated Property**: MonotonicMatchIndexProp
- **Root Cause**: 原性质要求 matchIndex 永远不能下降（除了 BecomeLeader），但当节点被移除后重新加入配置时，其 matchIndex 重置为 0 是 etcd 的正常行为。

### Evidence from Implementation
From `confchange/confchange.go:231-243` (remove function):
```go
func (c Changer) remove(cfg *tracker.Config, trk tracker.ProgressMap, id uint64) {
    if _, ok := trk[id]; !ok {
        return
    }
    delete(incoming(cfg.Voters), id)
    nilAwareDelete(&cfg.Learners, id)
    nilAwareDelete(&cfg.LearnersNext, id)
    // If the peer is still a voter in the outgoing config, keep the Progress.
    if _, onRight := outgoing(cfg.Voters)[id]; !onRight {
        delete(trk, id)  // Progress entry is deleted when node is removed
    }
}
```

From `confchange/confchange.go:204-207` (makeLearner function):
```go
func (c Changer) makeLearner(cfg *tracker.Config, trk tracker.ProgressMap, id uint64) {
    pr := trk[id]
    if pr == nil {
        c.initProgress(cfg, trk, id, true /* isLearner */)  // New Progress with Match=0
        return
    }
    ...
}
```

From `confchange/confchange.go:262` (initProgress function):
```go
trk[id] = &tracker.Progress{
    Match: 0,  // Always initialized to 0 for new/re-added nodes
    ...
}
```

When a node is removed and later re-added:
1. `remove()` deletes the Progress entry (if not in outgoing config)
2. `makeLearner()`/`makeVoter()` sees `pr == nil` and calls `initProgress`
3. `initProgress` creates new Progress with `Match=0`

This is intentional - the leader cannot assume the returning node still has its previous logs.

### Modifications Made
- **File**: MCetcdraft.tla
- **Before** (lines 498-500):
```tla
MonotonicMatchIndexProp ==
    [][(~ \E i \in Server: etcd!BecomeLeader(i)) =>
            (\A i,j \in Server : matchIndex'[i][j] >= matchIndex[i][j])]_mc_vars
```
- **After** (lines 504-515):
```tla
MonotonicMatchIndexProp ==
    [][(~ \E i \in Server: etcd!BecomeLeader(i)) =>
            (\A i,j \in Server :
                LET
                    \* Pre-state: nodes tracked by leader i
                    preConfig == config[i].jointConfig[1] \cup config[i].jointConfig[2] \cup config[i].learners
                    \* Post-state: nodes tracked by leader i after transition
                    postConfig == config'[i].jointConfig[1] \cup config'[i].jointConfig[2] \cup config'[i].learners
                IN
                \* Only check monotonicity for nodes that are continuously tracked
                \* (in config in both pre and post states)
                (j \in preConfig /\ j \in postConfig) => matchIndex'[i][j] >= matchIndex[i][j])]_mc_vars
```

### User Confirmation
- Confirmation Time: 2026-01-15
- User Feedback: Approved

---

## Record #30 - 2026-01-15

### Counterexample Summary
TLC simulation found `QuorumLogInv` violated. In the final state:
- s1's config was `{s3}` (single-node config after LeaveJoint)
- s1's commitIndex was 7
- s3's historyLog was empty

The violation occurred because LeaveJoint executed directly without requiring a log entry to be committed with joint quorum.

### Analysis Conclusion
- **Type**: B: Spec Modeling Issue
- **Violated Property**: QuorumLogInv
- **Root Cause**: Two issues identified:

**Issue 1: LeaveJoint bypasses log commitment**
The spec's `LeaveJoint` action directly modified config without requiring a log entry:
```tla
LeaveJoint(i) ==
    /\ IsJointConfig(i)
    /\ LET newVoters == GetConfig(i)
       IN config' = [config EXCEPT ![i] = [learners |-> {}, jointConfig |-> <<newVoters, {}>>]]
```

In etcd's actual implementation (raft.go:745-760), LeaveJoint requires:
1. Leader proposes an empty ConfChangeV2 when `autoLeave=TRUE`
2. This empty config change must be committed with joint quorum (both incoming and outgoing)
3. Only after commitment can LeaveJoint be applied

**Issue 2: AddNewServer/AddLearner/DeleteServer bypass ChangeConf constraints**
These legacy actions from the original etcd spec allowed configuration changes without proper joint consensus constraints, potentially adding multiple nodes consecutively before they sync logs.

### Evidence from Implementation
From `raft.go:745-760` (AutoLeave mechanism):
```go
if r.trk.Config.AutoLeave && newApplied >= r.pendingConfIndex && r.state == StateLeader {
    // Propose an empty ConfChangeV2 to leave joint config
    m, err := confChangeToMsg(nil)
    // ... submit for replication and commitment
}
```

From `confchange/confchange.go:51-76`:
```go
func (c Changer) EnterJoint(autoLeave bool, ccs ...pb.ConfChangeSingle) {
    cfg.AutoLeave = autoLeave  // Set autoLeave flag
}

func (c Changer) LeaveJoint() {
    *outgoingPtr(&cfg.Voters) = nil  // Clear outgoing config
    cfg.AutoLeave = false
}
```

### Modifications Made

**1. Added `autoLeave` field to config structure**
- **Files**: etcdraft.tla (line 426), MCetcdraft.tla (lines 105, 117), Traceetcdraft.tla (line 120)
- Config structure changed from:
```tla
[jointConfig |-> <<voters, {}>>, learners |-> {}]
```
- To:
```tla
[jointConfig |-> <<voters, {}>>, learners |-> {}, autoLeave |-> FALSE]
```

**2. Modified `ApplyConfigUpdate` to handle autoLeave**
- **File**: etcdraft.tla (lines 336-346)
- Added detection of `leaveJoint` flag and `autoLeave` management:
```tla
ApplyConfigUpdate(i, k) ==
    LET entry == LogEntry(i, k)
        isLeaveJoint == "leaveJoint" \in DOMAIN entry.value /\ entry.value.leaveJoint = TRUE
        newVoters == IF isLeaveJoint THEN GetConfig(i) ELSE entry.value.newconf
        newLearners == IF isLeaveJoint THEN {} ELSE entry.value.learners
        enterJoint == IF "enterJoint" \in DOMAIN entry.value THEN entry.value.enterJoint ELSE FALSE
        outgoing == IF enterJoint THEN entry.value.oldconf ELSE {}
        newAutoLeave == IF isLeaveJoint THEN FALSE ELSE enterJoint
    IN
    [config EXCEPT ![i]= [jointConfig |-> <<newVoters, outgoing>>, learners |-> newLearners, autoLeave |-> newAutoLeave]]
```

**3. Added `ProposeLeaveJoint` action**
- **File**: etcdraft.tla (lines 989-1003)
```tla
ProposeLeaveJoint(i) ==
    /\ state[i] = Leader
    /\ IsJointConfig(i)
    /\ config[i].autoLeave = TRUE
    /\ pendingConfChangeIndex[i] = 0  \* Previous config change has been applied
    /\ Replicate(i, [leaveJoint |-> TRUE, newconf |-> GetConfig(i), learners |-> {}], ConfigEntry)
    /\ pendingConfChangeIndex' = [pendingConfChangeIndex EXCEPT ![i] = LastIndex(log'[i])]
    /\ UNCHANGED <<messageVars, serverVars, candidateVars, matchIndex, commitIndex, configVars, ...>>
```

**4. Replaced direct LeaveJoint with ProposeLeaveJoint in MCNextDynamic**
- **File**: MCetcdraft.tla (lines 372-396, 398-418)
- Changed from `etcd!LeaveJoint(i)` to `etcd!ProposeLeaveJoint(i)`

**5. Removed redundant configuration change actions**
- **Files**: etcdraft.tla (lines 1643-1651), MCetcdraft.tla (lines 372-396, 398-418)
- Removed `AddNewServer`, `AddLearner`, `DeleteServer` from `NextDynamic`
- These actions bypassed `ChangeConf` constraints and could cause QuorumLogInv violations
- `ChangeConf` with `enterJoint` parameter provides complete functionality with proper constraints

### User Confirmation
- Confirmation Time: 2026-01-15 (In Progress)
- User Feedback: Modifications approved, debugging additional violations in progress
- Debug Log: violations/debug_ConfigNonEmptyInv.log

---

## Record #31 - 2026-01-15

### Counterexample Summary
TLC simulation found `ConfigNonEmptyInv` violated. In the final state:
- s3 received a snapshot: `log[s3] = [offset |-> 2, entries |-> <<>>, snapshotIndex |-> 1, snapshotTerm |-> 1]`
- s3's historyLog contained config entry: `historyLog[s3] = << [value |-> [newconf |-> {s1}, learners |-> {}], term |-> 1, type |-> ConfigEntry] >>`
- But s3's config was empty: `config[s3] = [learners |-> {}, jointConfig |-> <<{}, {}>>, autoLeave |-> FALSE]`

s3 received and processed a snapshot, updating its log and historyLog, but its config remained empty.

### Analysis Conclusion
- **Type**: B: Spec Modeling Issue
- **Violated Property**: ConfigNonEmptyInv
- **Root Cause**: `HandleSnapshotRequest` Case 3 (Actual Restore) only updated `log`, `historyLog`, and `commitIndex`, but did NOT update `config`. The original code had `configVars` in its UNCHANGED clause:

```tla
\* Original (line 1470):
/\ UNCHANGED <<serverVars, candidateVars, leaderVars, configVars, durableState, progressVars>>
```

In etcd's actual implementation, when a follower restores from a snapshot, it also restores the config from the snapshot metadata.

### Evidence from Implementation
From `raft.go:1846-1880` (restore function):
```go
func (r *raft) restore(s pb.Snapshot) bool {
    // ...
    r.raftLog.restore(s)  // Restore log

    // Restore config from snapshot metadata
    r.trk = tracker.MakeProgressTracker(r.trk.MaxInflight, r.trk.MaxInflightBytes)
    cfg, trk, err := confchange.Restore(confchange.Changer{
        Tracker:   r.trk,
        LastIndex: r.raftLog.lastIndex(),
    }, cs)
    // ...
    r.trk.Config = cfg    // Config is restored from snapshot!
    r.trk.Progress = trk
}
```

From `confchange/restore.go:27-131` (Restore function):
- Parses ConfState from snapshot metadata
- Reconstructs the Config (Voters, Learners, AutoLeave) from ConfState
- This is called during snapshot restoration

### Modifications Made

**File**: etcdraft.tla (lines 1449-1486)

**Before**:
```tla
ELSE
    \* Case 3: Actual Restore. Wipe log.
    \* Reference: raft.go:1846 restore() returns true
    /\ log' = [log EXCEPT ![i] = [
          offset  |-> m.msnapshotIndex + 1,
          entries |-> <<>>,
          snapshotIndex |-> m.msnapshotIndex,
          snapshotTerm  |-> m.msnapshotTerm
       ]]
    /\ historyLog' = [historyLog EXCEPT ![i] = m.mhistory]
    /\ commitIndex' = [commitIndex EXCEPT ![i] = m.msnapshotIndex]
    /\ Reply([...], m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, configVars, durableState, progressVars>>
```

**After**:
```tla
ELSE
    \* Case 3: Actual Restore. Wipe log.
    \* Reference: raft.go:1846 restore() returns true
    \* Must also restore config from snapshot metadata
    LET \* Find the last config entry in snapshot's history
        configIndices == {k \in 1..Len(m.mhistory) : m.mhistory[k].type = ConfigEntry}
        lastConfigIdx == IF configIndices /= {} THEN Max(configIndices) ELSE 0
        \* Extract config from last config entry
        lastConfigEntry == IF lastConfigIdx > 0 THEN m.mhistory[lastConfigIdx]
                           ELSE [value |-> [newconf |-> {}, learners |-> {}]]
        hasEnterJoint == lastConfigIdx > 0 /\ "enterJoint" \in DOMAIN lastConfigEntry.value
        enterJoint == IF hasEnterJoint THEN lastConfigEntry.value.enterJoint ELSE FALSE
        hasOldconf == enterJoint /\ "oldconf" \in DOMAIN lastConfigEntry.value
        oldconf == IF hasOldconf THEN lastConfigEntry.value.oldconf ELSE {}
        newVoters == lastConfigEntry.value.newconf
        newLearners == IF "learners" \in DOMAIN lastConfigEntry.value
                       THEN lastConfigEntry.value.learners ELSE {}
        \* AutoLeave is TRUE when in joint config
        newAutoLeave == enterJoint /\ oldconf /= {}
    IN
    /\ log' = [log EXCEPT ![i] = [
          offset  |-> m.msnapshotIndex + 1,
          entries |-> <<>>,
          snapshotIndex |-> m.msnapshotIndex,
          snapshotTerm  |-> m.msnapshotTerm
       ]]
    /\ historyLog' = [historyLog EXCEPT ![i] = m.mhistory]
    /\ commitIndex' = [commitIndex EXCEPT ![i] = m.msnapshotIndex]
    \* NEW: Restore config from snapshot history
    /\ config' = [config EXCEPT ![i] = [
           learners |-> newLearners,
           jointConfig |-> <<newVoters, oldconf>>,
           autoLeave |-> newAutoLeave]]
    /\ Reply([...], m)
    \* Changed: removed configVars from UNCHANGED, added specific config-related vars
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars,
                   reconfigCount, pendingConfChangeIndex,
                   durableState, progressVars>>
```

### Key Changes Summary

| Aspect | Before | After |
|--------|--------|-------|
| Config update | Not updated (in UNCHANGED) | Extracted from snapshot history |
| Config source | N/A | Last ConfigEntry in m.mhistory |
| Joint config | N/A | Correctly handles enterJoint/oldconf |
| AutoLeave | N/A | Set based on joint config state |

### User Confirmation
- Confirmation Time: 2026-01-15 (Pending verification)
- User Feedback: Pending simulation verification

---

## Record #32 - 2026-01-15

### Counterexample Summary
TLC simulation found `SnapshotNextInv` violated. In the final state (State 59):
- `progressState[s1][s4] = StateSnapshot`
- `pendingSnapshot[s1][s4] = 2`
- `nextIndex[s1][s4] = 1` (violated: should be >= 3)

The invariant required `nextIndex >= pendingSnapshot + 1` when in StateSnapshot, but nextIndex was decreased from 3 to 1.

### Analysis Conclusion
- **Type**: C: Invariant Issue (Invariant too strong)
- **Violated Property**: SnapshotNextInv
- **Root Cause**: The invariant was incorrect. In etcd's actual implementation, `MaybeDecrTo` can decrease `Next` when processing a stale `AppendEntriesResponse` rejection, even in `StateSnapshot`.

### Evidence from Implementation

**MaybeDecrTo in progress.go:226-254:**
```go
func (pr *Progress) MaybeDecrTo(rejected, matchHint uint64) bool {
    if pr.State == StateReplicate {
        // ...
    }
    // StateProbe or StateSnapshot - NO special handling for StateSnapshot!
    if pr.Next-1 != rejected {
        return false
    }
    pr.Next = max(min(rejected, matchHint+1), pr.Match+1)
    // ...
    return true
}
```

**IsPaused in progress.go:262-269:**
```go
func (pr *Progress) IsPaused() bool {
    switch pr.State {
    case StateSnapshot:
        return true  // Always paused in StateSnapshot!
    // ...
    }
}
```

**Key insight**: In StateSnapshot, `Next` CAN be decreased by `MaybeDecrTo`, but this is safe because `IsPaused()` returns `true`, preventing any message sends via `maybeSendAppend` (raft.go:618-620).

### Scenario Analysis
1. Leader s1 sends AppendEntries to s4 (prevIndex=2)
2. Leader s1 sends Snapshot to s4 (snapshotIndex=2), enters StateSnapshot
   - Sets `pendingSnapshot = 2`, `nextIndex = 3`
3. s4 rejects the AppendEntries (sent before snapshot)
4. s1 receives the rejection and calls `MaybeDecrTo`:
   - `rejected = 2`, `matchHint = 0`, `Match = 0`
   - `newNext = max(min(2, 1), 1) = 1`
5. `nextIndex` becomes 1, violating `nextIndex >= pendingSnapshot + 1`

But this is **safe** because:
- `IsPaused()` returns `true` for StateSnapshot
- `sendAppend` immediately returns without sending anything
- The leader waits for SnapshotResponse to leave StateSnapshot

### Modifications Made

**File**: etcdraft.tla

**Removed**: `SnapshotNextInv` definition (lines 1969-1977)

**Added comment**:
```tla
\* Invariant: SnapshotNextInv - REMOVED
\* This invariant was incorrect. In etcd, MaybeDecrTo (progress.go:226-254) can decrease
\* Next in StateSnapshot when processing a stale AppendEntriesResponse rejection.
\* This is safe because IsPaused() (progress.go:262-269) returns true for StateSnapshot,
\* preventing any message sends. Next can become as low as Match+1 (possibly 1),
\* regardless of PendingSnapshot value.
```

**File**: MCetcdraft.cfg

**Disabled**: `SnapshotNextInv` with explanation comment:
```
\* SnapshotNextInv - DISABLED: In etcd, MaybeDecrTo can decrease Next in StateSnapshot.
\* This is safe because IsPaused() returns true for StateSnapshot, preventing any sends.
\* Reference: progress.go:262-269 IsPaused(), progress.go:226-254 MaybeDecrTo()
```

**File**: etcdraft.tla (HandleAppendEntriesResponse)

**Added comment** at line 1357-1361 explaining StateSnapshot behavior:
```tla
ELSE \* Valid rejection: use leader-side findConflictByTerm optimization
     \* Note: This applies to both StateProbe and StateSnapshot.
     \* In StateSnapshot, Next may be decreased below PendingSnapshot+1,
     \* but IsPaused() prevents sending any messages, so it's safe.
     \* Reference: progress.go:IsPaused() returns true for StateSnapshot
```

### User Confirmation
- Confirmation Time: 2026-01-15
- User Feedback: Confirmed after reviewing etcd implementation

---

## Record #33 - 2026-01-15

### Counterexample Summary
TLC simulation found `QuorumLogInv` violated. Key state transitions:
- State 111 → 112: s1 is Leader with config `{s1}`, `commitIndex[s1]` jumped from 5 to 19
- State 112 → 113: s1's config changed from `{s1}` to `{s1, s2, s4}` via `ApplySimpleConfChange`
- After config change: Quorum `{s2, s4}` didn't have all committed entries
  - s2 only had 8 entries in historyLog
  - s4 had 0 entries in historyLog
  - But s1 had committed up to index 19!

### Analysis Conclusion
- **Type**: B: Spec Modeling Issue
- **Violated Property**: QuorumLogInv
- **Root Cause**: Two related issues in the spec:

**Issue 1: ApplySimpleConfChange used Max instead of Min**
The spec's `ApplySimpleConfChange` used `Max(validIndices)` to jump to the last config entry, but etcd processes committed entries sequentially, applying each config as encountered.

**Issue 2: AdvanceCommitIndex could advance past unapplied configs**
The spec allowed `commitIndex` to advance past config entries that hadn't been applied yet. In etcd, configs are applied as part of processing `Ready.CommittedEntries`, so a leader cannot commit past an unapplied config entry.

### Evidence from Implementation
From `doc.go:133-140` (Ready processing pattern):
```go
for _, entry := range rd.CommittedEntries {
    switch entry.Type {
    case raftpb.EntryNormal:
        // process normal entry
    case raftpb.EntryConfChange:
        // MUST apply config change here, one at a time
        cc := raftpb.ConfChange{}
        cc.Unmarshal(entry.Data)
        n.ApplyConfChange(cc)  // Apply each config as encountered
    }
}
```

This shows that:
1. Entries are processed sequentially via `for _, entry := range`
2. Config changes are applied immediately when encountered via `ApplyConfChange`
3. A config cannot be skipped - each must be applied in order

From `quorum/joint.go:49-56` (JointConfig.CommittedIndex):
```go
func (c JointConfig) CommittedIndex(l AckedIndexer) Index {
    idx0 := c[0].CommittedIndex(l)  // incoming
    idx1 := c[1].CommittedIndex(l)  // outgoing
    if idx0 < idx1 {
        return idx0
    }
    return idx1
}
```

Joint config requires min of both quorums - once config is applied, the new quorum constraints take effect.

### Modifications Made

**1. Added `appliedConfigIndex` variable**
- **File**: etcdraft.tla (lines 142-149)
```tla
\* Track the index of the last applied config entry per server
\* Reference: etcd processes CommittedEntries sequentially, applying configs as encountered
\* This ensures config is applied before commit can advance past it
VARIABLE
    \* @type: Int -> Int;
    appliedConfigIndex

configVars == <<config, reconfigCount, appliedConfigIndex>>
```

**2. Updated InitConfigVars**
- **File**: etcdraft.tla (line 439)
```tla
InitConfigVars == /\ config = [i \in Server |-> [ jointConfig |-> <<InitServer, {}>>, learners |-> {}, autoLeave |-> FALSE]]
                  /\ reconfigCount = 0
                  /\ appliedConfigIndex = [i \in Server |-> 0]
```

**3. Modified AdvanceCommitIndex to respect config application order**
- **File**: etcdraft.tla (lines 810-848)
```tla
AdvanceCommitIndex(i) ==
    /\ state[i] = Leader
    /\ LET AllVoters == GetConfig(i) \union GetOutgoingConfig(i)
           Agree(index) == {k \in AllVoters : matchIndex[i][k] >= index}
           logSize == LastIndex(log[i])
           IsCommitted(index) ==
               IF IsJointConfig(i) THEN
                   /\ (Agree(index) \cap GetConfig(i)) \in Quorum(GetConfig(i))
                   /\ (Agree(index) \cap GetOutgoingConfig(i)) \in Quorum(GetOutgoingConfig(i))
               ELSE
                   Agree(index) \in Quorum(GetConfig(i))

           \* Find the next unapplied config entry (if any)
           \* Cannot commit past a config entry until it's applied
           nextUnappliedConfigIndices == {x \in Max({log[i].offset, appliedConfigIndex[i]+1})..logSize :
                                           LogEntry(i, x).type = ConfigEntry}
           maxCommitBound == IF nextUnappliedConfigIndices = {}
                            THEN logSize
                            ELSE Min(nextUnappliedConfigIndices)

           agreeIndexes == {index \in (commitIndex[i]+1)..maxCommitBound : IsCommitted(index)}
           newCommitIndex ==
              IF /\ agreeIndexes /= {}
                 /\ LogTerm(i, Max(agreeIndexes)) = currentTerm[i]
              THEN Max(agreeIndexes)
              ELSE commitIndex[i]
       IN
        /\ newCommitIndex > commitIndex[i]
        /\ CommitTo(i, newCommitIndex)
    /\ UNCHANGED <<messageVars, serverVars, candidateVars, leaderVars, log, configVars, durableState, progressVars, historyLog>>
```

**4. Modified ApplySimpleConfChange to apply configs sequentially**
- **File**: etcdraft.tla (lines 960-1003)
```tla
ApplySimpleConfChange(i) ==
    \* Find config entries that are committed but not yet applied
    LET validIndices == {x \in Max({log[i].offset, appliedConfigIndex[i]+1})..commitIndex[i] :
                          LogEntry(i, x).type = ConfigEntry}
    IN
    /\ validIndices /= {}
    /\ LET k == Min(validIndices)  \* Apply the NEXT config entry, not MAX
           ...
       IN
        /\ k > 0
        /\ k <= commitIndex[i]
        /\ config' = newConfigFn
        /\ appliedConfigIndex' = [appliedConfigIndex EXCEPT ![i] = k]  \* Track applied config
        ...
```

**5. Updated Restart to restore appliedConfigIndex**
- **File**: etcdraft.tla (lines 494-496)
```tla
/\ config' = [config EXCEPT ![i] = durableState[i].config]
\* After restart, consider all committed configs as applied (durableState.config reflects this)
/\ appliedConfigIndex' = [appliedConfigIndex EXCEPT ![i] = durableState[i].commitIndex]
```

**6. Updated HandleSnapshotRequest to set appliedConfigIndex**
- **File**: etcdraft.tla (lines 1508-1510)
```tla
/\ config' = [config EXCEPT ![i] = [learners |-> newLearners, jointConfig |-> <<newVoters, oldconf>>, autoLeave |-> newAutoLeave]]
\* All config entries up to snapshot index are considered applied
/\ appliedConfigIndex' = [appliedConfigIndex EXCEPT ![i] = m.msnapshotIndex]
```

**7. Updated MCetcdraft.tla etcdInitConfigVars**
- **File**: MCetcdraft.tla (lines 105-108)
```tla
etcdInitConfigVars == /\ config = [i \in Server |-> [ jointConfig |-> IF i \in InitServer THEN <<InitServer, {}>> ELSE <<{}, {}>>, learners |-> {}, autoLeave |-> FALSE]]
                      /\ reconfigCount = 0 \* the bootstrap configurations are not counted
                      \* Bootstrap config entries are already applied (committed at Cardinality(InitServer))
                      /\ appliedConfigIndex = [i \in Server |-> IF i \in InitServer THEN Cardinality(InitServer) ELSE 0]
```

### Key Behavior Changes

| Aspect | Before | After |
|--------|--------|-------|
| Config application | Jump to MAX config entry | Apply MIN (next) config entry |
| Commit advancement | No config boundary check | Uses current applied config's quorum |
| Config tracking | None | `appliedConfigIndex` variable |
| Sequential order | Not enforced | Enforced via Min in ApplySimpleConfChange |

### User Confirmation
- Confirmation Time: 2026-01-15
- User Feedback: Approved ("同意，请严格按照代码逻辑修复 spec")

### Correction (2026-01-15)

The initial fix was **too restrictive**. It prevented `commitIndex` from advancing past unapplied config entries via `maxCommitBound`. However, etcd's actual behavior is:

1. `maybeCommit()` uses the **current applied config's quorum** (via `r.trk.Committed()`)
2. `commitIndex` CAN advance past config entries using the old config's quorum
3. Config entries are applied later when processing `CommittedEntries`

**Safety mechanism in etcd:**
- EnterJoint entry is committed using old config's quorum
- After EnterJoint is applied, we're in joint config requiring BOTH quorums
- LeaveJoint can only be committed when BOTH quorums agree
- So by the time we leave joint, the new config's quorum has all entries

**Corrected AdvanceCommitIndex** (removed `maxCommitBound` constraint):
```tla
AdvanceCommitIndex(i) ==
    /\ state[i] = Leader
    /\ LET AllVoters == GetConfig(i) \union GetOutgoingConfig(i)
           Agree(index) == {k \in AllVoters : matchIndex[i][k] >= index}
           logSize == LastIndex(log[i])
           \* Uses the CURRENT APPLIED config (config[i]) for quorum calculation
           IsCommitted(index) ==
               IF IsJointConfig(i) THEN
                   /\ (Agree(index) \cap GetConfig(i)) \in Quorum(GetConfig(i))
                   /\ (Agree(index) \cap GetOutgoingConfig(i)) \in Quorum(GetOutgoingConfig(i))
               ELSE
                   Agree(index) \in Quorum(GetConfig(i))

           \* commitIndex can advance to any index that the current applied config's
           \* quorum agrees on. No maxCommitBound constraint needed.
           agreeIndexes == {index \in (commitIndex[i]+1)..logSize : IsCommitted(index)}
           newCommitIndex == ...
       IN ...
```

**What remains:**
- `appliedConfigIndex` variable - still needed to track applied configs
- `ApplySimpleConfChange` using `Min(validIndices)` - ensures sequential config application
- `pendingConfChangeIndex` constraint - prevents proposing multiple config changes

| Aspect | Initial Fix | Corrected Fix |
|--------|-------------|---------------|
| commitIndex advancement | Bounded by unapplied configs | No bound, uses applied config's quorum |
| Matches etcd behavior | No (too restrictive) | Yes |

---

## Record #20 - 2026-01-15

### Counterexample Summary
77-step counterexample:
1. s2 is Leader with commitIndex = 8, config `jointConfig = [[s2], []]` (only s2 is voter)
2. s2 sends AppendEntries to s3 with entries 2-6 (including config entry at index 3) and `mcommitIndex = 6`
3. s3 receives message, appends entries 2-6, sets `commitIndex = 6`
4. But s3's `appliedConfigIndex = 1` (hasn't applied config entry at index 3 yet)
5. s3's config is still the OLD config: `jointConfig = [[s1], []]` (only s1 is voter)
6. QuorumLogInv fails: from s3's old config view, quorum is `{{s1}}`, but s1 only has 3 entries in historyLog
7. `IsPrefix(Committed(s3), historyLog[s1])` = `IsPrefix(6 entries, 3 entries)` = FALSE

### Analysis Conclusion
- **Type**: A: Invariant Too Strong
- **Violated Property**: QuorumLogInv
- **Root Cause**: QuorumLogInv checks from each server's perspective using that server's current config. During config changes:
  1. Follower receives AppendEntries and updates commitIndex
  2. Config entries are applied later in `ApplySimpleConfChange`
  3. **Between these two steps**, follower has stale config but updated commitIndex
  
  In this case:
  - Leader (s2) committed using NEW config (only s2 as voter)
  - Follower (s3) accepted leader's commitIndex but still has OLD config
  - From s3's old config view, s1 should have all committed entries, but doesn't
  
  **This is NOT a safety issue** because:
  - Leader committed using the correct (new) config
  - Leader has all committed entries
  - Follower's stale config view is temporary

### Evidence from Implementation
etcd's actual behavior:
```go
// raft.go: Follower receives AppendEntries
// 1. Append entries to log
// 2. Update commitIndex from leaderCommit
// 3. Config entries applied later when processing CommittedEntries

// The follower trusts the leader's commitIndex without verifying
// against its own (possibly stale) config
```

### Modifications Made
- **File**: etcdraft.tla
- **Before (lines 1803-1813)**:
```tla
\* All committed entries are contained in the log
\* of at least one server in every quorum.
\* In joint config, it's safe if EITHER incoming OR outgoing quorums hold the data,
\* because election requires both quorums, so one blocking is enough.
QuorumLogInv ==
    \A i \in Server :
        \/ \A S \in Quorum(GetConfig(i)) :
               \E j \in S : IsPrefix(Committed(i), historyLog[j])
        \/ (IsJointConfig(i) /\
            \A S \in Quorum(GetOutgoingConfig(i)) :
                \E j \in S : IsPrefix(Committed(i), historyLog[j]))
```
- **After**:
```tla
\* All committed entries are contained in the log
\* of at least one server in every quorum.
\* In joint config, it's safe if EITHER incoming OR outgoing quorums hold the data,
\* because election requires both quorums, so one blocking is enough.
\*
\* Note: Only check servers whose config is up-to-date (applied all committed config entries).
\* A follower may have a stale config while having received committed entries from the leader.
\* This is normal behavior during config change processing - the follower trusts the leader's
\* commitIndex but hasn't applied the config entries yet.
QuorumLogInv ==
    \A i \in Server :
        \* Find config entries within the committed range
        LET configIndicesInCommitted == {k \in 1..commitIndex[i] :
                k <= Len(historyLog[i]) /\ historyLog[i][k].type = ConfigEntry}
            \* Check if server's config is up-to-date (applied all committed config entries)
            configUpToDate == configIndicesInCommitted = {} \/
                              appliedConfigIndex[i] >= Max(configIndicesInCommitted)
        IN
        \* Only check servers with up-to-date config
        configUpToDate =>
            (\/ \A S \in Quorum(GetConfig(i)) :
                   \E j \in S : IsPrefix(Committed(i), historyLog[j])
             \/ (IsJointConfig(i) /\
                 \A S \in Quorum(GetOutgoingConfig(i)) :
                     \E j \in S : IsPrefix(Committed(i), historyLog[j])))
```

### User Confirmation
- Confirmation Time: 2026-01-15
- User Feedback: Approved

---

## Record #21 - 2026-01-16 (Supplementary fix to Record #22)

### Counterexample Summary
73-step counterexample:
1. s1 is Leader with `pendingConfChangeIndex[s1] = 3`, `appliedConfigIndex[s1] = 2`
2. s1 has log entries up to index 12, `durableState[s1].log = 12`, commitIndex = 4
3. `CompactLog(s1, 4)` is executed, setting `log.offset = 4`, `snapshotIndex = 3`
4. After compaction: `pendingConfChangeIndex[s1] = 3` but `log[s1].offset = 4`
5. `PendingConfIndexValidInv` violated: `pendingConfChangeIndex[s1] >= log[s1].offset` (3 >= 4) is FALSE

### Analysis Conclusion
- **Type**: B: Spec Modeling Issue
- **Violated Property**: PendingConfIndexValidInv
- **Root Cause**: Record #22 fixed `CompactLog` by changing constraint from `commitIndex + 1` to `durableState.log + 1`. However, this is insufficient because:
  - `durableState.log` tracks **persisted** log index (= 12)
  - `appliedConfigIndex` tracks **applied** config index (= 2)
  - `pendingConfChangeIndex` (= 3) points to a config entry that is persisted but **not yet applied**
  - The constraint `newStart <= 13` allowed compacting index 3, but that config entry hasn't been applied yet

### Why Record #22's Fix Was Incomplete

| Variable | Meaning | Value in Counterexample |
|----------|---------|------------------------|
| `durableState[s1].log` | Persisted log index | 12 |
| `appliedConfigIndex[s1]` | Applied config index | 2 |
| `pendingConfChangeIndex[s1]` | Pending config index | 3 |
| `commitIndex[s1]` | Committed index | 4 |

Record #22's constraint `newStart <= durableState.log + 1 = 13` allows compacting up to index 12, but the config entry at index 3 hasn't been applied yet!

### Evidence from Implementation
From `storage.go:249-250`:
```go
// Compact discards all log entries prior to compactIndex.
// It is the application's responsibility to not attempt to compact an index
// greater than raftLog.applied.
```

From `raft.go:1318`:
```go
alreadyPending := r.pendingConfIndex > r.raftLog.applied
```

The implementation logic:
1. Compaction should only go up to `applied`, not past it
2. `pendingConfIndex > applied` means the config change is pending (not yet applied)
3. Therefore, if `pendingConfChangeIndex > 0`, compaction cannot include that index
4. Note: `storage.go` comment is a **soft constraint** (documentation), not enforced by code

### Modifications Made
- **File**: etcdraft.tla
- **Before (after Record #22's fix)**:
```tla
CompactLog(i, newStart) ==
    /\ newStart > log[i].offset
    /\ newStart <= durableState[i].log + 1  \* Record #22's fix
    /\ log' = [log EXCEPT ![i] = [
          offset  |-> newStart,
          ...
       ]]
    /\ UNCHANGED <<...>>
```
- **After (supplementary constraint)**:
```tla
\* Additional constraint: Cannot compact past pendingConfChangeIndex.
\* Reference: raft.go:1318 - pendingConfIndex > applied means config change is pending.
\* Since compaction should only go up to applied, we cannot compact past pendingConfChangeIndex.
CompactLog(i, newStart) ==
    /\ newStart > log[i].offset
    /\ newStart <= durableState[i].log + 1  \* Record #22's fix (persisted constraint)
    \* NEW: Cannot compact past pending config entry that hasn't been applied
    \* If pendingConfChangeIndex > 0, the entry at that index must remain in the log
    /\ (state[i] = Leader /\ pendingConfChangeIndex[i] > 0) =>
           newStart <= pendingConfChangeIndex[i]
    /\ log' = [log EXCEPT ![i] = [
          offset  |-> newStart,
          entries |-> SubSeq(@.entries, newStart - @.offset + 1, Len(@.entries)),
          snapshotIndex |-> newStart - 1,
          snapshotTerm  |-> LogTerm(i, newStart - 1)
       ]]
    /\ UNCHANGED <<...>>
```

### Relationship to Record #22
- **Record #22**: Changed `commitIndex + 1` → `durableState.log + 1` (persisted constraint)
- **Record #21**: Added `pendingConfChangeIndex` constraint (applied constraint for config entries)
- Both constraints are needed together to correctly model the implementation's behavior

### User Confirmation
- Confirmation Time: 2026-01-16
- User Feedback: Approved (补充 Record #22 的修复)

---

## Record #34 - 2026-01-16

### Counterexample Summary
62-step counterexample:
1. s4 is a new node that received log via snapshot (`historyLog[s4]` contains 2 ConfigEntry entries)
2. `HandleSnapshotRequest` updated s4's `log`, `historyLog`, `commitIndex`
3. But `config[s4]` is still empty `<<{}, {}>>` (requires separate `ApplySnapshotConfChange` call)
4. Before `ApplySnapshotConfChange` executes, invariant check finds: `LastIndex(log[s4]) = 2 > 0` but `GetConfig(s4) = {}`
5. `ConfigNonEmptyInv` violated

### Analysis Conclusion
- **Type**: B: Spec Modeling Issue
- **Violated Property**: ConfigNonEmptyInv
- **Root Cause**: `ApplySnapshotConfChange` updates `config` but did not update `appliedConfigIndex`. This prevents invariants like `QuorumLogInv` that depend on `appliedConfigIndex` from correctly determining whether config has been applied.

In the actual system, config application state is tracked via `applied` index (`pendingConfIndex > applied` determines if config is pending). `ApplySimpleConfChange` already correctly updates `appliedConfigIndex`, but `ApplySnapshotConfChange` was missing this update.

### Evidence from Implementation
From `raft.go:1318`:
```go
alreadyPending := r.pendingConfIndex > r.raftLog.applied
```

This shows that config application state is tracked by comparing indices. In our Spec, `appliedConfigIndex` serves the same purpose.

### Modifications Made
- **File**: etcdraft.tla (lines 1050-1053)
- **Before**:
```tla
    IN
    /\ config' = [config EXCEPT ![i] = [learners |-> {}, jointConfig |-> <<newVoters, oldconf>>, autoLeave |-> newAutoLeave]]
    /\ UNCHANGED <<messageVars, serverVars, candidateVars, leaderVars, logVars, durableState, progressVars, reconfigCount, pendingConfChangeIndex, appliedConfigIndex>>
```
- **After**:
```tla
    IN
    /\ config' = [config EXCEPT ![i] = [learners |-> {}, jointConfig |-> <<newVoters, oldconf>>, autoLeave |-> newAutoLeave]]
    /\ appliedConfigIndex' = [appliedConfigIndex EXCEPT ![i] = lastConfigIdx]
    /\ UNCHANGED <<messageVars, serverVars, candidateVars, leaderVars, logVars, durableState, progressVars, reconfigCount, pendingConfChangeIndex>>
```

### Key Change
`ApplySnapshotConfChange` now also updates `appliedConfigIndex` to `lastConfigIdx` (the index of the last ConfigEntry in historyLog). This ensures consistency with `ApplySimpleConfChange` and correctly tracks config application state.

### User Confirmation
- Confirmation Time: 2026-01-16
- User Feedback: Approved

---

## Record #35 - 2026-01-16 (Continuation of Record #34)

### Counterexample Summary
52-step counterexample (same root cause as Record #34):
1. s4 received snapshot (`snapshotIndex = 1`, `historyLog[s4]` has 1 ConfigEntry with `newconf = {s1}`)
2. `HandleSnapshotRequest` updated s4's log: `offset = 2`, so `LastIndex = 1`
3. `config[s4]` is still empty (waiting for `ApplySnapshotConfChange`)
4. `appliedConfigIndex[s4] = 0` (config not yet applied)
5. `ConfigNonEmptyInv` violated: `LastIndex > 0` but `GetConfig = {}`

### Analysis Conclusion
- **Type**: A: Invariant Too Strong
- **Violated Property**: ConfigNonEmptyInv
- **Root Cause**: Record #34 fixed `ApplySnapshotConfChange` to update `appliedConfigIndex`, but `ConfigNonEmptyInv` still didn't account for the intermediate state between `HandleSnapshotRequest` and `ApplySnapshotConfChange`.

The invariant needs to check whether config has been applied before asserting that config is non-empty.

### Modifications Made
- **File**: etcdraft.tla (lines 2248-2262)
- **Before**:
```tla
ConfigNonEmptyInv ==
    \A i \in Server :
        LastIndex(log[i]) > 0 => GetConfig(i) /= {}
```
- **After**:
```tla
ConfigNonEmptyInv ==
    \A i \in Server :
        LET configIndices == {k \in 1..Len(historyLog[i]) : historyLog[i][k].type = ConfigEntry}
            lastConfigIdx == IF configIndices /= {} THEN Max(configIndices) ELSE 0
            \* Config is considered applied if no config entries exist or appliedConfigIndex >= last config
            configApplied == lastConfigIdx = 0 \/ appliedConfigIndex[i] >= lastConfigIdx
        IN
        (LastIndex(log[i]) > 0 /\ configApplied) => GetConfig(i) /= {}
```

### Key Change
`ConfigNonEmptyInv` now only checks config non-emptiness when:
1. `LastIndex(log[i]) > 0` (server has log entries), AND
2. `configApplied` is TRUE (all config entries in historyLog have been applied)

This accounts for the intermediate state where a server has received log/snapshot but hasn't yet applied the config via `ApplySnapshotConfChange`.

### User Confirmation
- Confirmation Time: 2026-01-16
- User Feedback: Pending

---

## Record #36 - 2026-01-16

### Counterexample Summary
`confchange_disable_validation.ndjson` trace validation failed at line 35. The trace shows:
1. Line 26: `SendAppendEntriesResponse` - A ValueEntry was created at log index 6 (before EnterJoint was applied at line 28)
2. Line 28: `ApplyConfChange` - EnterJoint applied, creating joint config `[[\"1\"],[\"1\"]]`
3. Line 35: `ApplyConfChange` - Attempted to apply LeaveJoint, but there was no LeaveJoint ConfigEntry in the log

**Root Cause**: At line 26, log index 6 already held a ValueEntry (implicit entry created before EnterJoint). When the system tried to leave joint config at line 35, the spec expected a LeaveJoint ConfigEntry at that index, but found only the ValueEntry.

### Analysis Conclusion
- **Type**: B: Spec Modeling Issue
- **Violated Property**: Trace validation - missing action for implicit LeaveJoint
- **Root Cause**: The spec did not model the edge case where `autoLeave=TRUE` but no LeaveJoint log entry exists. In etcd raft's autoLeave mechanism, when an implicit entry (ValueEntry) is created before the EnterJoint config is applied, the next log index gets a ValueEntry instead of a LeaveJoint ConfigEntry. The system must still leave the joint config, but without a dedicated log entry.

### Evidence from Implementation
From `state_trace.go:299-316` (traceConfChangeEvent):
```go
func traceConfChangeEvent(cfg tracker.Config, r *raft) {
    // Detect LeaveJoint: old config is joint (Voters[1] non-empty), new config is not joint (Voters[1] empty)
    isLeaveJoint := len(r.trk.Config.Voters[1]) > 0 && len(cfg.Voters[1]) == 0

    cc := &TracingConfChange{
        Changes:    []SingleConfChange{},
        NewConf:    formatConf(cfg.Voters[0].Slice()),
        Learners:   formatLearners(cfg.Learners),
        LeaveJoint: isLeaveJoint,
    }
    ...
}
```
This shows that LeaveJoint can occur even without a dedicated log entry - it's detected by configuration state change (joint → non-joint).

### Modifications Made

#### File 1: etcdraft.tla (lines 1020-1037) - Added ImplicitLeaveJoint action
```tla
\* Implicit LeaveJoint - leave joint config when autoLeave=TRUE but no LeaveJoint log entry exists
\* This can happen when an implicit entry was created before EnterJoint was applied,
\* resulting in a ValueEntry at the next log index instead of a LeaveJoint ConfigEntry.
\* In this case, the system leaves joint config without a dedicated log entry.
\* Reference: This is an edge case in etcd raft's autoLeave mechanism.
ImplicitLeaveJoint(i, newVoters, newLearners) ==
    /\ IsJointConfig(i)
    /\ config[i].autoLeave = TRUE
    \* No unapplied config entries exist
    /\ LET validIndices == {x \in Max({log[i].offset, appliedConfigIndex[i]+1})..commitIndex[i] :
                              LogEntry(i, x).type = ConfigEntry}
       IN validIndices = {}
    /\ config' = [config EXCEPT ![i] = [learners |-> newLearners, jointConfig |-> <<newVoters, {}>>, autoLeave |-> FALSE]]
    /\ IF state[i] = Leader /\ pendingConfChangeIndex[i] > 0 THEN
        /\ reconfigCount' = reconfigCount + 1
        /\ pendingConfChangeIndex' = [pendingConfChangeIndex EXCEPT ![i] = 0]
       ELSE UNCHANGED <<reconfigCount, pendingConfChangeIndex>>
    /\ UNCHANGED <<messageVars, serverVars, candidateVars, matchIndex, logVars, durableState, progressVars, appliedConfigIndex>>
```

#### File 2: etcdraft.tla (lines 1715-1722) - Added to NextDynamic
- **Before**:
```tla
NextDynamic ==
    \/ Next
    \/ \E i \in Server : ChangeConf(i)
    \/ \E i \in Server : ChangeConfAndSend(i)
    \/ \E i \in Server : ApplySimpleConfChange(i)
    \/ \E i \in Server : ProposeLeaveJoint(i)
```
- **After**:
```tla
NextDynamic ==
    \/ Next
    \/ \E i \in Server : ChangeConf(i)
    \/ \E i \in Server : ChangeConfAndSend(i)
    \/ \E i \in Server : ApplySimpleConfChange(i)
    \/ \E i \in Server : ProposeLeaveJoint(i)
    \/ \E i \in Server, newVoters \in SUBSET Server, newLearners \in SUBSET Server :
        ImplicitLeaveJoint(i, newVoters, newLearners)
```

#### File 3: Traceetcdraft.tla (lines 482-492) - Added routing action
```tla
\* Implicit LeaveJoint - for cases where autoLeave=TRUE but no LeaveJoint log entry exists
\* This happens when the implicit entry was created before EnterJoint was applied
\* Routes to ImplicitLeaveJoint action in etcdraft.tla
ImplicitLeaveJointIfLogged(i) ==
    /\ LoglineIsNodeEvent("ApplyConfChange", i)
    /\ "newconf" \in DOMAIN logline.event.prop.cc
    /\ LET newVoters == ToSet(logline.event.prop.cc.newconf)
           newLearners == IF "learners" \in DOMAIN logline.event.prop.cc
                          THEN ToSet(logline.event.prop.cc.learners)
                          ELSE GetLearners(i)
       IN ImplicitLeaveJoint(i, newVoters, newLearners)
```

#### File 4: Traceetcdraft.tla (lines 586-590) - Added to ApplyConfChange handling
- **Before**:
```tla
   \/ /\ LoglineIsEvent("ApplyConfChange")
      /\ \E i \in Server: \/ ApplySimpleConfChangeIfLogged(i)
                          \/ ApplySnapshotConfChangeIfLogged(i)
                          \/ LeaveJointIfLogged(i)
```
- **After**:
```tla
   \/ /\ LoglineIsEvent("ApplyConfChange")
      /\ \E i \in Server: \/ ApplySimpleConfChangeIfLogged(i)
                          \/ ApplySnapshotConfChangeIfLogged(i)
                          \/ LeaveJointIfLogged(i)
                          \/ ImplicitLeaveJointIfLogged(i)
```

### Key Design Decision
Per user feedback, the logic was placed in:
1. **etcdraft.tla** (spec): Defines what the system can do (ImplicitLeaveJoint action)
2. **Traceetcdraft.tla** (trace spec): Handles event routing (ImplicitLeaveJointIfLogged calls the spec action)

This separation ensures:
- Model checking can explore the ImplicitLeaveJoint behavior via NextDynamic
- Trace validation correctly routes ApplyConfChange events to the appropriate action

### User Confirmation
- Confirmation Time: 2026-01-16
- User Feedback: Pending

---

## Record #NEW - 2026-01-18

### Counterexample Summary
TLC simulation found a violation of `AppendEntriesCommitSafeInv` after checking ~49,000 states. The violating message was a heartbeat with:
- `mprevLogIndex = 0`
- `mprevLogTerm = 0`
- `mentries = <<>>`
- `mcommitIndex = 2`

The invariant check `mcommitIndex (2) <= mprevLogIndex (0) + Len(mentries) (0)` failed.

### Analysis Conclusion
- **Type**: A: Invariant Too Strong
- **Violated Property**: `AppendEntriesCommitSafeInv`
- **Root Cause**: The invariant was incorrectly designed. It checked that `mcommitIndex <= mprevLogIndex + Len(mentries)`, but this is not a valid constraint because:
  1. **Heartbeat messages** don't include entries, and their `commitIndex` can be any valid value
  2. **Normal MsgApp messages** can also have `Commit > Index + len(Entries)` due to `maxMsgSize` limiting the number of entries sent
  
  In the implementation (`raft.go:638`), entries are limited by `maxMsgSize`, so a leader might send only partial entries while advertising a higher `commitIndex`. The receiver handles this correctly by setting `commitIndex = min(leaderCommit, lastNewEntry)`.

  The correct invariant for detecting Bug 76f1249 is `AppendEntriesPrevLogTermValidInv`, which checks that `prevLogTerm > 0` when `prevLogIndex > 0`.

### Modifications Made
- **File**: `etcdraft.tla`
- **Change**: Removed `AppendEntriesCommitSafeInv` definition and removed it from `BugDetectionInv` aggregate

- **File**: `MCetcdraft.cfg`
- **Change**: Removed `AppendEntriesCommitSafeInv` from INVARIANTS section

### User Confirmation
- Confirmation Time: 2026-01-18
- User Feedback: Agreed to delete the invariant

---

## Record #NEW2 - 2026-01-18

### Summary
Comprehensive review of bug detection invariants. Removed invalid invariants and fixed spec modeling issues.

### Analysis of Bug Detection Invariants

#### 1. `UncommittedEntriesBoundInv` (Bug a370b6f) - **DELETED**
- **Reason**: Bug a370b6f is about **byte counter** tracking, not entry count
- **Problem**: Spec doesn't model byte counting, only entry count
- **Conclusion**: Cannot detect the real bug, removed

#### 2. `InflightsCountConsistentInv` (Bug e419ba5) - **DELETED**
- **Reason**: Invariant is **trivially true**
- **Code**:
```tla
InflightsCount(i, j) == Cardinality(inflights[i][j])  \* Definition

InflightsCountConsistentInv ==
    Cardinality(inflights[i][j]) = InflightsCount(i, j)  \* Always true!
```
- **Conclusion**: Meaningless check, removed

#### 3. `ReplicateImplicitEntry` - **FIXED**
- **Problem**: Missing preconditions for auto-leave in joint config
- **Implementation** (raft.go:745):
```go
if r.trk.Config.AutoLeave && newApplied >= r.pendingConfIndex && r.state == StateLeader {
    // initiate auto-leave
}
```
- **Old Spec**: Only checked `state[i] = Leader`
- **New Spec**: Added check `(isJoint => (config[i].autoLeave = TRUE /\ pendingConfChangeIndex[i] = 0))`

### Modifications Made

#### File 1: etcdraft.tla
- **Deleted**: `UncommittedEntriesBoundInv` definition (lines 2833-2850)
- **Deleted**: `InflightsCountConsistentInv` definition (lines 2853-2863)
- **Modified**: `BugDetectionInv` aggregate to remove deleted invariants
- **Modified**: `ReplicateImplicitEntry` to add auto-leave preconditions

#### File 2: MCetcdraft.cfg
- **Removed**: `UncommittedEntriesBoundInv` from INVARIANTS section
- **Removed**: `InflightsCountConsistentInv` from INVARIANTS section

### Code Reference for ReplicateImplicitEntry Fix

**Implementation (raft.go:745)**:
```go
if r.trk.Config.AutoLeave && newApplied >= r.pendingConfIndex && r.state == StateLeader {
```

**Fixed Spec**:
```tla
ReplicateImplicitEntry(i) ==
    /\ state[i] = Leader
    /\ LET isJoint == IsJointConfig(i)
       IN
       \* FIX: When in joint config, must check auto-leave preconditions per raft.go:745
       /\ (isJoint => (config[i].autoLeave = TRUE /\ pendingConfChangeIndex[i] = 0))
       /\ ...
```

### User Confirmation
- Confirmation Time: 2026-01-18
- User Feedback: Approved deletion of invalid invariants and fix of ReplicateImplicitEntry

---

## Record #NEW3 - 2026-01-18

### Summary
Fixed BecomeLeader action to correctly set `pendingConfChangeIndex` per implementation.

### Analysis

**Problem Identified**: During the review of Bug bd3c759 (auto-transitioning out of joint config), user noticed that the `BecomeLeader` action had `UNCHANGED pendingConfChangeIndex`, but the implementation sets this field.

### Evidence from Implementation

**Implementation (raft.go:955-960)**:
```go
func (r *raft) becomeLeader() {
    // ...
    r.tick = r.tickHeartbeat
    r.lead = r.id
    r.state = StateLeader
    r.pendingConfIndex = r.raftLog.lastIndex()  // <-- Sets pendingConfIndex!
    // ...
}
```

The implementation explicitly sets `pendingConfIndex = lastIndex()` when a node becomes leader. This is critical for the auto-leave mechanism to work correctly because:
1. It prevents auto-leave from firing until at least one entry is applied after becoming leader
2. It ensures `newApplied >= r.pendingConfIndex` check (raft.go:745) works correctly

### Modifications Made

**File**: etcdraft.tla

**Before**:
```tla
BecomeLeader(i) ==
    /\ ...
    /\ UNCHANGED <<messageVars, currentTerm, votedFor, pendingConfChangeIndex, 
                   candidateVars, logVars, configVars, durableState, partitions>>
```

**After**:
```tla
BecomeLeader(i) ==
    /\ ...
    \* FIX: Set pendingConfChangeIndex to lastIndex per raft.go:955-960
    /\ pendingConfChangeIndex' = [pendingConfChangeIndex EXCEPT ![i] = LastIndex(log[i])]
    /\ UNCHANGED <<messageVars, currentTerm, votedFor, candidateVars, logVars, configVars, durableState, partitions>>
```

### Verification
- SANY syntax check passed (only warnings, no errors)

### User Confirmation
- Confirmation Time: 2026-01-18
- User Feedback: Approved after user identified the issue during review

---

## Record #14 - 2026-01-19

### Counterexample Summary
Execution path:
1. State 1 (Init): s2 has `applied = 2`, `durableState.snapshotIndex = 0`, `durableState.log = 2`
2. State 2 (Restart s2): `applied[s2]` is reset to `durableState.snapshotIndex = 0`, but `durableState` unchanged
3. State 3 (Compact s2): `CompactLog(s2, 2)` succeeds because `2 <= durableState.log + 1 = 3`
   - Results in `snapshotIndex = 1`, but `applied = 0`
   - **Invariant `SnapshotAppliedConsistencyInv` violated**: `snapshotIndex > applied`

### Analysis Conclusion
- **Type**: B: Spec Modeling Issue
- **Violated Property**: SnapshotAppliedConsistencyInv
- **Root Cause**: The `CompactLog` action checked `newStart <= durableState[i].log + 1`, but after restart, `applied` is reset to `snapshotIndex` while `durableState.log` retains its pre-restart value. This allowed compaction beyond the actual applied index.

### Evidence from Implementation

**Implementation (storage.go:248-250)**:
```go
// Compact discards all log entries prior to compactIndex.
// It is the application's responsibility to not attempt to compact an index
// greater than raftLog.applied.
```

The implementation clearly states compaction should not exceed `raftLog.applied`. The spec should enforce this constraint using the actual `applied` variable, not `durableState.log`.

### Modifications Made

**File**: etcdraft.tla (lines 1630-1641)

**Before**:
```tla
\* Compacts the log of server i up to newStart (exclusive).
\* newStart becomes the new offset.
\* Reference: storage.go:249-250 - "It is the application's responsibility to not
\* attempt to compact an index greater than raftLog.applied."
\* We use durableState.log as applied index (set by PersistState in Ready).
\*
\* Note: pendingConfChangeIndex does NOT constrain log compaction.
\* Reference: storage.go Compact() only checks offset and lastIndex bounds.
\* pendingConfChangeIndex is only checked when proposing new config changes (raft.go:1318).
CompactLog(i, newStart) ==
    /\ newStart > log[i].offset
    /\ newStart <= durableState[i].log + 1
```

**After**:
```tla
\* Compacts the log of server i up to newStart (exclusive).
\* newStart becomes the new offset.
\* Reference: storage.go:249-250 - "It is the application's responsibility to not
\* attempt to compact an index greater than raftLog.applied."
\* We check against the actual applied index, not durableState.log, because after
\* restart applied is reset to snapshotIndex while durableState.log retains its value.
\*
\* Note: pendingConfChangeIndex does NOT constrain log compaction.
\* Reference: storage.go Compact() only checks offset and lastIndex bounds.
\* pendingConfChangeIndex is only checked when proposing new config changes (raft.go:1318).
CompactLog(i, newStart) ==
    /\ newStart > log[i].offset
    /\ newStart <= applied[i] + 1
```

### Verification
- SANY syntax check passed

### User Confirmation
- Confirmation Time: 2026-01-19
- User Feedback: Approved

---

## Record #15 - 2026-01-19

### Counterexample Summary
Execution path (43 states, showing key states):
- State 43: s1 is Candidate with enough votes
- State 44 (BecomeLeader): s1 becomes Leader
  - `pendingConfChangeIndex[s1] = 2` (set to LastIndex by BecomeLeader)
  - `applied[s1] = 2`
  - **Invariant violated**: `ConfigChangePendingInv` requires `pendingConfChangeIndex > applied`, but `2 > 2` is false

### Analysis Conclusion
- **Type**: A: Invariant Too Strong
- **Violated Property**: ConfigChangePendingInv
- **Root Cause**: The invariant assumed `pendingConfChangeIndex > 0` implies a pending config change. However, `BecomeLeader` conservatively sets `pendingConfChangeIndex = lastIndex` even when all entries have been applied. When `pendingConfChangeIndex == applied`, it means there's NO pending config change (valid state).

### Evidence from Implementation

**Implementation (raft.go:955-960)**:
```go
// Conservatively set the pendingConfIndex to the last index in the
// log. There may or may not be a pending config change, but it's
// safe to delay any future proposals until we commit all our
// pending log entries, and scanning the entire tail of the log
// could be expensive.
r.pendingConfIndex = r.raftLog.lastIndex()
```

**Implementation (raft.go:1320)**:
```go
alreadyPending := r.pendingConfIndex > r.raftLog.applied
```

When `pendingConfIndex == applied`, `alreadyPending = FALSE`, indicating no pending config change. This is a valid state.

### Modifications Made

**File**: MCetcdraft.cfg

**Before**:
```
INVARIANTS
    \* StateSnapshot => Next == PendingSnapshot + 1 (progress.go:40)
    StateSnapshotNextInv
    \* pendingConfIndex > 0 => pendingConfIndex > applied (raft.go:1320)
    ConfigChangePendingInv
```

**After**:
```
INVARIANTS
    \* StateSnapshot => Next == PendingSnapshot + 1 (progress.go:40)
    StateSnapshotNextInv
    \* REMOVED: ConfigChangePendingInv - invariant too strong
    \* pendingConfChangeIndex can equal applied after BecomeLeader when all entries
    \* have been applied. This is valid (no pending config change).
    \* Reference: raft.go:1320 "alreadyPending := r.pendingConfIndex > r.raftLog.applied"
    \* When pendingConfIndex == applied, alreadyPending = FALSE (valid state)
```

### User Confirmation
- Confirmation Time: 2026-01-19
- User Feedback: Approved removal

---

## Record #16 - 2026-01-19

### Counterexample Summary
Execution path (33 states):
- State 33: s2 becomes Leader
  - `commitIndex[s2] = 2`
  - `log[s2].offset = 2` (entry 1 compacted)
  - `log[s2].snapshotIndex = 1` (entry 1 covered by snapshot)
  - **Invariant violated**: `LeaderLogContainsAllCommittedInv` requires `IsAvailable(s2, 1)`, but entry 1 is compacted

### Analysis Conclusion
- **Type**: A: Invariant Too Strong
- **Violated Property**: LeaderLogContainsAllCommittedInv
- **Root Cause**: The invariant required ALL committed entries to be in-memory available. However, entries can be compacted into a snapshot. When a leader needs to send compacted entries, it sends a snapshot instead (valid behavior).

### Evidence from Implementation

**Implementation (raft.go:622-627 maybeSendAppend)**:
```go
prevTerm, err := r.raftLog.term(prevIndex)
if err != nil {
    // The log probably got truncated at >= pr.Next, so we can't catch up the
    // follower log anymore. Send a snapshot instead.
    return r.maybeSendSnapshot(to, pr)
}
```

**Implementation (raft.go:644-645)**:
```go
if err != nil { // send a snapshot if we failed to get the entries
    return r.maybeSendSnapshot(to, pr)
}
```

Leaders handle compacted entries by sending snapshots instead. The invariant should allow entries covered by snapshot.

### Modifications Made

**File**: etcdraft.tla

**Before**:
```tla
LeaderLogContainsAllCommittedInv ==
    \A i \in Server :
        state[i] = Leader =>
            /\ commitIndex[i] <= LastIndex(log[i])
            /\ \A idx \in 1..commitIndex[i] :
                IsAvailable(i, idx)
```

**After**:
```tla
LeaderLogContainsAllCommittedInv ==
    \A i \in Server :
        state[i] = Leader =>
            /\ commitIndex[i] <= LastIndex(log[i])
            \* All entries up to commitIndex should be available or covered by snapshot
            /\ \A idx \in 1..commitIndex[i] :
                idx <= log[i].snapshotIndex \/ IsAvailable(i, idx)
```

### Verification
- SANY syntax check passed

### User Confirmation
- Confirmation Time: 2026-01-19
- User Feedback: Approved after implementation code review

---

## Record #17 - 2026-01-19

### Counterexample Summary
Execution path (117 states):
- State 117: s2 is Leader
  - `nextIndex[s2][s4] = 1`
  - `log[s2].offset = 2` (entry 1 compacted)
  - **Invariant violated**: `LeaderNextIndexValidInv` requires `nextIndex >= offset`, but `1 >= 2` is false

### Analysis Conclusion
- **Type**: A: Invariant Too Strong
- **Violated Property**: LeaderNextIndexValidInv
- **Root Cause**: The invariant was based on old behavior before Bug 76f1249 was fixed. After the fix, when `nextIndex < offset`, the leader gracefully handles this by sending a snapshot instead of panicking. Log compaction doesn't automatically update `nextIndex` - the leader discovers the compaction when trying to send entries and falls back to snapshot.

### Evidence from Implementation

**Implementation (raft.go:622-627 maybeSendAppend)**:
```go
prevIndex := pr.Next - 1
prevTerm, err := r.raftLog.term(prevIndex)
if err != nil {
    // The log probably got truncated at >= pr.Next, so we can't catch up the
    // follower log anymore. Send a snapshot instead.
    return r.maybeSendSnapshot(to, pr)
}
```

**Implementation (raft.go:644-645)**:
```go
if err != nil { // send a snapshot if we failed to get the entries
    return r.maybeSendSnapshot(to, pr)
}
```

The implementation explicitly handles `nextIndex < offset` by sending snapshots. This is the intended behavior.

### Modifications Made

**File**: etcdraft.tla

Commented out `LeaderNextIndexValidInv` definition and removed from `HighPriorityInv` aggregate.

**File**: MCetcdraft.cfg

Removed `LeaderNextIndexValidInv` from INVARIANTS section.

### Verification
- SANY syntax check passed

### User Confirmation
- Confirmation Time: 2026-01-19
- User Feedback: Approved after implementation code review

---

## Record #18 - 2026-01-19

### Error Summary
TLC threw an EvalException during simulation:
```
The second argument of SubSeq must be in the domain of its first argument:
<<...14 entry sequence...>>
, but instead it is
0
```

Execution path:
- State 112: s2 is Leader with compacted log
  - `log[s2].offset = 2` (snapshotIndex = 1)
  - `matchIndex[s2][s1] = 7`, but s1 restarted with `matchIndex` reset
  - TLC tried to evaluate `AppendEntries(s2, s1, <<1, ...>>)`
  - SubSeq calculation: `range[1] - offset + 1 = 1 - 2 + 1 = 0` (invalid index)

### Analysis Conclusion
- **Type**: B: Spec Modeling Issue
- **Root Cause**: `AppendEntriesInRangeToPeer` lacked a guard to ensure entries in the range are available (not compacted). When `range[1] < log[i].offset`, the SubSeq index calculation becomes 0 or negative.

### Evidence from Implementation

**Implementation (raft.go:622-627, 644-645)**:
The implementation checks if entries are available before sending AppendEntries. If entries are compacted (not available), it falls back to sending a snapshot:
```go
prevTerm, err := r.raftLog.term(prevIndex)
if err != nil {
    return r.maybeSendSnapshot(to, pr)
}
// ...
if err != nil { // send a snapshot if we failed to get the entries
    return r.maybeSendSnapshot(to, pr)
}
```

### Modifications Made

**File**: etcdraft.tla

**Before**:
```tla
AppendEntriesInRangeToPeer(subtype, i, j, range) ==
    /\ i /= j
    /\ range[1] <= range[2]
    /\ state[i] = Leader
    /\ j \in GetConfig(i) \union GetOutgoingConfig(i) \union GetLearners(i)
    \* New: Check flow control state; cannot send when paused (except heartbeat)
```

**After**:
```tla
AppendEntriesInRangeToPeer(subtype, i, j, range) ==
    /\ i /= j
    /\ range[1] <= range[2]
    /\ state[i] = Leader
    /\ j \in GetConfig(i) \union GetOutgoingConfig(i) \union GetLearners(i)
    \* Guard: Entries in range must be available (not compacted)
    \* If range[1] > LastIndex, we're sending an empty append (allowed)
    \* Otherwise, the first entry must be in the available range
    /\ (range[1] > LastIndex(log[i]) \/ range[1] >= log[i].offset)
    \* New: Check flow control state; cannot send when paused (except heartbeat)
```

### Verification
- SANY syntax check passed

### User Confirmation
- Confirmation Time: 2026-01-19
- User Feedback: Pending

---

## Record #19 - 2026-01-19

### Error Summary
TLC simulation found `AppendEntriesPrevLogTermValidInv` violation in MC_run5.out:

```
State 171:
log[s3].offset = 4
log[s3].snapshotIndex = 3
nextIndex[s3][s2] = 3

AppendEntriesRequest message with:
  mprevLogIndex = 2
  mprevLogTerm = 0  ← VIOLATION: should not be 0 when mprevLogIndex > 0
```

### Analysis Conclusion
- **Type**: B: Spec Modeling Issue
- **Root Cause**: Leader s3 had compacted log (offset=4, snapshotIndex=3) and tried to send AppendEntries with prevLogIndex=2. Since prevLogIndex=2 is neither 0, nor equal to snapshotIndex(3), nor >= offset(4), the LogTerm function returns 0 (invalid). The spec allowed this message, but the implementation would send a snapshot instead.

### Evidence from Implementation

**Implementation (raft.go:622-628)**:
```go
prevIndex := pr.Next - 1
prevTerm, err := r.raftLog.term(prevIndex)
if err != nil {
    // The log probably got truncated at >= pr.Next, so we can't catch up the
    // follower log anymore. Send a snapshot instead.
    return r.maybeSendSnapshot(to, pr)
}
```

When `term(prevIndex)` fails (returns error), the implementation sends a snapshot instead of AppendEntries. The spec must match this behavior.

**Bug Reference**: Bug 76f1249 - MsgApp after log truncation causes panic when prevLogTerm is 0 but prevLogIndex > 0.

### Modifications Made

**File**: etcdraft.tla

Added new guard to `AppendEntriesInRangeToPeer` to ensure prevLogIndex can have valid term:

**Before**:
```tla
AppendEntriesInRangeToPeer(subtype, i, j, range) ==
    /\ i /= j
    /\ range[1] <= range[2]
    /\ state[i] = Leader
    /\ j \in GetConfig(i) \union GetOutgoingConfig(i) \union GetLearners(i)
    \* Guard: If sending entries (non-empty range), they must be available (not compacted)
    \* Reference: raft.go:623-627 maybeSendAppend() - if term(prevIndex) fails, send snapshot
    \* Heartbeat (range[1] = range[2]) doesn't send entries, so no check needed
    /\ (range[1] = range[2] \/ range[1] >= log[i].offset)
```

**After**:
```tla
AppendEntriesInRangeToPeer(subtype, i, j, range) ==
    /\ i /= j
    /\ range[1] <= range[2]
    /\ state[i] = Leader
    /\ j \in GetConfig(i) \union GetOutgoingConfig(i) \union GetLearners(i)
    \* Guard: If sending entries (non-empty range), they must be available (not compacted)
    \* Reference: raft.go:623-627 maybeSendAppend() - if term(prevIndex) fails, send snapshot
    \* Heartbeat (range[1] = range[2]) doesn't send entries, so no check needed
    /\ (range[1] = range[2] \/ range[1] >= log[i].offset)
    \* NEW Guard (Bug 76f1249 fix): prevLogIndex must have retrievable term
    \* Reference: raft.go:622-628 - if term(prevIndex) fails, send snapshot instead
    \* prevLogIndex = range[1] - 1 can have valid term if:
    \*   (1) prevLogIndex = 0 (empty log case, term = 0 is valid), or
    \*   (2) prevLogIndex = snapshotIndex (term from snapshot metadata), or
    \*   (3) prevLogIndex >= offset (entry is available in log)
    /\ (range[1] = range[2] \/ range[1] = 1 \/ range[1] - 1 = log[i].snapshotIndex \/ range[1] - 1 >= log[i].offset)
```

### Verification
- SANY syntax check passed

### User Confirmation
- Confirmation Time: 2026-01-19
- User Feedback: 确认 (Approved)

---
