# TLA+ Spec Fix Log

## 2026-01-10 - Extract MaxInflightMsgs from trace config line

**Trace:** Multiple traces failed with inflight count mismatches
**Error Type:** Abstraction Gap

**Issue:**
Trace validation failed because the spec used a hardcoded `MaxInflightMsgs = 256`, but actual raft configurations can vary. When the implementation uses a different value, inflight message tracking becomes inconsistent between spec and trace.

**Root Cause:**
The TLA+ spec had `MaxInflightMsgs` as a constant set to 256, but raft's `Config.MaxInflightMsgs` can be configured differently. This caused mismatches when validating traces from systems with different configurations.

**Fix:**
1. Added config line emission to harness:
   - `harness/parser.go`: Added `traceConfig` struct and `WriteConfig()` function
   - `harness/main.go`: Call `WriteConfig(MaxInflightMsgs)` on first node creation

2. Added config extraction to TLA+ trace spec:
   - `Traceetcdraft.tla`: Added `TraceMaxInflightMsgs` definition that reads from trace config line (defaults to 256 if not found)
   - `Traceetcdraft.cfg`: Changed `MaxInflightMsgs = 256` to `MaxInflightMsgs <- TraceMaxInflightMsgs`

**Files Modified:**
- `harness/parser.go`: Added `traceConfig` struct and `WriteConfig` method
- `harness/main.go`: Added config writing on first node creation
- `spec/Traceetcdraft.tla`: Added `TraceMaxInflightMsgs` definition
- `spec/Traceetcdraft.cfg`: Use trace-sourced MaxInflightMsgs

---

## 2026-01-10 - Add ReportUnreachable event instrumentation

**Trace:** `../traces/heartbeat_resp_recovers_from_probing.ndjson`
**Error Type:** Abstraction Gap

**Issue:**
Trace validation failed because the `report-unreachable` command in the test scenario causes a `StateReplicate -> StateProbe` transition that was not recorded in the trace. When validating the subsequent heartbeat send, the trace showed `prop.state = "StateProbe"` but the spec had `progressState[1][2] = StateReplicate`.

**Root Cause:**
The `ReportUnreachable` API call (raft.go:1624-1632) changes progress state but was not instrumented to emit a trace event. The spec couldn't track this state change.

**Fix:**
1. Added `ReportUnreachable` trace event instrumentation to the raft library:
   - `state_trace.go`: Added `rsmReportUnreachable` event type and `traceReportUnreachable()` function
   - `state_trace_nop.go`: Added stub function
   - `raft.go:1630-1631`: Call `traceReportUnreachable()` after state transition

2. Added `ReportUnreachable` action to TLA+ spec:
   - `etcdraft.tla:1309-1317`: New `ReportUnreachable(i, j)` action modeling StateReplicate -> StateProbe
   - `Traceetcdraft.tla:485-492`: New `ReportUnreachableIfLogged(i, j)` trace handler using `ValidateProgressStatePrimed`

**Files Modified:**
- `raft/state_trace.go`: Added event type and tracing function
- `raft/state_trace_nop.go`: Added stub function
- `raft/raft.go`: Added tracing call in MsgUnreachable handler
- `spec/etcdraft.tla`: Added `ReportUnreachable` action
- `spec/Traceetcdraft.tla`: Added `ReportUnreachableIfLogged` handler

---

## 2026-01-11 - Fix LeaveJoint UNCHANGED conflict with pendingConfChangeIndex

**Trace:** `../traces/confchange_v2_add_single_explicit.ndjson`
**Error Type:** Inconsistency Error

**Issue:**
Trace validation failed at line 61 (ApplyConfChange/LeaveJoint). The `LeaveJoint` action appeared to execute correctly (all conditions passed, correct values computed for `config'`), but TLC rejected the state transition.

**Root Cause:**
In `etcdraft.tla:LeaveJoint`, there was a conflict between the IF-ELSE branch and the UNCHANGED clause:
```tla
/\ IF state[i] = Leader /\ pendingConfChangeIndex[i] > 0 THEN
    /\ pendingConfChangeIndex' = [pendingConfChangeIndex EXCEPT ![i] = 0]
   ELSE UNCHANGED <<..., pendingConfChangeIndex>>
/\ UNCHANGED <<..., leaderVars, ...>>  \* leaderVars includes pendingConfChangeIndex!
```

The IF branch sets `pendingConfChangeIndex'` while the UNCHANGED clause includes `leaderVars` (which contains `pendingConfChangeIndex`). This contradiction caused TLC to reject the state.

**Fix:**
Changed line 903 from:
```tla
/\ UNCHANGED <<messageVars, serverVars, candidateVars, leaderVars, logVars, durableState, progressVars>>
```
to:
```tla
/\ UNCHANGED <<messageVars, serverVars, candidateVars, matchIndex, logVars, durableState, progressVars>>
```

Only `matchIndex` is kept from `leaderVars` since `pendingConfChangeIndex` is already handled in the IF-ELSE branch.

**Files Modified:**
- `spec/etcdraft.tla:903`: Fixed UNCHANGED clause in LeaveJoint action

---

## 2026-01-11 - Implement MaybeDecrTo for rejection handling

**Trace:** `../traces/campaign_learner_must_vote.ndjson`
**Error Type:** Inconsistency Error

**Issue:**
Trace validation failed at line 95. The spec had `nextIndex["2"]["3"] = 5`, but the trace expected it to be 4 after processing a rejected AppendEntriesResponse.

**Root Cause:**
The spec's `HandleAppendEntriesResponse` action did not implement the `MaybeDecrTo` logic from `progress.go:226-252`. When a follower rejects an AppendEntries request, the leader should decrease `nextIndex` based on the rejection information (rejected index and matchHint).

**Fix:**
1. Added `mrejectHint` field to `AERESPT` message type alias
2. Updated all `AppendEntriesResponse` message creations to include `mrejectHint |-> 0` (for success) or actual hint (for rejection)
3. Implemented `MaybeDecrTo` logic in `HandleAppendEntriesResponse`:
   - For `StateReplicate`: if rejected > Match, transition to Probe with Next = Match + 1
   - For `StateProbe/StateSnapshot`: if Next-1 = rejected, set Next = max(min(rejected, matchHint+1), Match+1)
   - Otherwise: stale rejection, just unpause
4. Updated `LoglineIsAppendEntriesResponse` in trace spec to map `mrejectHint` from trace

**Files Modified:**
- `spec/etcdraft.tla`: Added `mrejectHint` field, implemented MaybeDecrTo logic in HandleAppendEntriesResponse
- `spec/Traceetcdraft.tla`: Updated LoglineIsAppendEntriesResponse to map mrejectHint

---

## 2026-01-11 - Fix TraceLearners for dynamic learner configuration

**Trace:** `../traces/confchange_disable_validation.ndjson`
**Error Type:** Inconsistency Error

**Issue:**
After the MaybeDecrTo fix, `confchange_disable_validation.ndjson` started failing. The trace began with no learners but added learners dynamically via ChangeConf events. The spec incorrectly initialized learners at startup.

**Root Cause:**
The `TraceLearners` function searched for ANY `ApplyConfChange` event with learners, not just the FIRST one. In traces where learners are added dynamically (not present at bootstrap), this caused learners to be incorrectly initialized at startup based on a later ApplyConfChange event.

**Fix:**
Changed `TraceLearners` to only check the FIRST `ApplyConfChange` event:
```tla
TraceLearners ==
    LET firstApplyConf == SelectSeq(TraceLog, LAMBDA x: x.event.name = "ApplyConfChange")
    IN IF Len(firstApplyConf) > 0 /\
          "learners" \in DOMAIN firstApplyConf[1].event.prop.cc /\
          firstApplyConf[1].event.prop.cc.learners /= <<>>
       THEN ToSet(firstApplyConf[1].event.prop.cc.learners)
       ELSE {}
```

If the first ApplyConfChange doesn't have learners, return {} and let learners be added dynamically through ChangeConf events.

**Files Modified:**
- `spec/Traceetcdraft.tla`: Fixed TraceLearners to only look at first ApplyConfChange

---

## 2026-01-11 - Implement ManualSendSnapshot for send-snapshot test command

**Trace:** `../traces/snapshot_succeed_via_app_resp_behind.ndjson`
**Error Type:** Abstraction Gap

**Issue:**
Trace validation failed at line 45 (ManualSendSnapshot event). The test harness's `send-snapshot` command bypasses the normal raft send path and directly injects a `MsgSnap` message without modifying progress state.

**Root Cause:**
The existing `SendSnapshot` action in the spec always transitions `progressState[i][j]` to `StateSnapshot`, but the manual send-snapshot command doesn't modify progress state at all. This is a fundamentally different code path that needed separate modeling.

**Fix:**
1. Added `ManualSendSnapshot(i, j)` action to etcdraft.tla:
   - Uses `commitIndex[i]` as precondition (not snapshotIndex) since test creates snapshot from committed state
   - Sends SnapshotRequest message with committed history
   - Does NOT modify progress state (key difference from regular SendSnapshot)

2. Added TraceLogger support to InteractionOpts:
   - Modified `harness/main.go` to pass TraceLogger to InteractionOpts
   - Modified `interaction_env_handler_send_snapshot.go` to emit ManualSendSnapshot trace event

3. Added `ManualSendSnapshotIfLogged(i, j)` handler to Traceetcdraft.tla

**Files Modified:**
- `spec/etcdraft.tla:664-678`: Added ManualSendSnapshot action
- `spec/Traceetcdraft.tla:389-396`: Added ManualSendSnapshotIfLogged handler
- `raft/rafttest/interaction_env_handler_send_snapshot.go`: Added trace event emission
- `harness/main.go`: Added TraceLogger to InteractionOpts

---

## 2026-01-11 - Remove log compaction from SendSnapshotWithCompaction

**Trace:** `../traces/snapshot_succeed_via_app_resp_behind.ndjson`
**Error Type:** Inconsistency Error

**Issue:**
After ManualSendSnapshot fix, trace validation still failed at ~97% completion. The spec tried to send AppendEntries with entry 12, but the log had been compacted (offset=13).

**Root Cause:**
The spec's `SendSnapshotWithCompaction` action compacted the log immediately when sending a snapshot:
```tla
/\ log' = [log EXCEPT ![i].offset = snapshoti,
                      ![i].entries = SubSeq(...)]
```
However, the actual raft implementation compacts the log asynchronously - compaction doesn't happen during snapshot send. This caused the spec to lose log entries that the system still had available.

**Fix:**
Removed log compaction from `SendSnapshotWithCompaction`:
- Changed from modifying `log'` to `UNCHANGED <<logVars>>`
- The action now only:
  1. Sends the SnapshotRequest message
  2. Updates progress state to StateSnapshot
  3. Sets pendingSnapshot and nextIndex
- Compaction should be modeled separately if needed

**Files Modified:**
- `spec/etcdraft.tla:623-640`: Removed log compaction from SendSnapshotWithCompaction

---

## 2026-01-11 - Add pendingSnapshot check for StateSnapshot->StateReplicate transition

**Trace:** `../traces/snapshot_succeed_via_app_resp_behind.ndjson`
**Error Type:** Inconsistency Error

**Issue:**
After fixing ManualSendSnapshot, validation failed because the StateSnapshot -> StateReplicate transition wasn't happening. The spec checked `newMatchIndex + 1 >= log[i].offset` but offset was 13 after compaction, while the system checked `Match+1 >= firstIndex()` where firstIndex was still 11.

**Root Cause:**
The condition for transitioning from StateSnapshot to StateReplicate only checked against `log[i].offset`:
```tla
canResumeFromSnapshot == newMatchIndex + 1 >= log[i].offset
```
But after removing compaction from SendSnapshotWithCompaction, the offset wouldn't change. The system checks against `firstIndex()` which might differ from the spec's log offset.

**Fix:**
Added alternate condition checking `pendingSnapshot`:
```tla
canResumeFromSnapshot == \/ newMatchIndex + 1 >= log[i].offset
                         \/ newMatchIndex + 1 >= pendingSnapshot[i][j]
```
If the match index has caught up to the pending snapshot index, we can transition to StateReplicate.

**Files Modified:**
- `spec/etcdraft.tla:1216-1222`: Added pendingSnapshot check in HandleAppendEntriesResponse

---

## 2026-01-11 - Fix ApplySnapshotConfChange for joint configuration recovery

**Trace:** `../traces/leader_transfer.ndjson`
**Error Type:** Inconsistency Error

**Issue:**
Trace validation failed because node 4's configuration after snapshot restore was `<<{"2","3","4"}, {}>>` but should have been the joint config `<<{"2","3","4"}, {"1","2","3"}>>`.

**Root Cause:**
The `ApplySnapshotConfChange` action only set the new voters from the snapshot message, but didn't check `historyLog` for joint configuration information. When a snapshot is applied, the configuration should be restored from the config entries in the history log, including any `enterJoint` state and `oldconf` values.

**Fix:**
Modified `ApplySnapshotConfChange` to read joint config from `historyLog`:
```tla
ApplySnapshotConfChange(i, newVoters) ==
    LET configIndices == {k \in 1..Len(historyLog[i]) : historyLog[i][k].type = ConfigEntry}
        lastConfigIdx == IF configIndices /= {} THEN Max(configIndices) ELSE 0
        hasEnterJoint == lastConfigIdx > 0 /\ "enterJoint" \in DOMAIN historyLog[i][lastConfigIdx].value
        enterJoint == IF hasEnterJoint THEN historyLog[i][lastConfigIdx].value.enterJoint ELSE FALSE
        hasOldconf == enterJoint /\ "oldconf" \in DOMAIN historyLog[i][lastConfigIdx].value
        oldconf == IF hasOldconf THEN historyLog[i][lastConfigIdx].value.oldconf ELSE {}
    IN
    /\ config' = [config EXCEPT ![i] = [learners |-> {}, jointConfig |-> <<newVoters, oldconf>>]]
```

**Files Modified:**
- `spec/etcdraft.tla:933-949`: Modified ApplySnapshotConfChange to recover joint config from historyLog

---

## 2026-01-11 - Fix commit calculation for empty AppendEntries

**Trace:** `../traces/partition_and_recover.ndjson`
**Error Type:** Inconsistency Error

**Issue:**
Trace validation failed because the commit value in empty appends was wrong. The spec calculated commit=14, but the trace showed commit=17.

**Root Cause:**
The spec's `AppendEntriesInRangeToPeer` action calculated commit as:
```tla
commit == Min({commitIndex[i], lastEntry})
```
For empty appends (no entries being sent), `lastEntry` would be the last entry in the range, which might be less than `commitIndex`. But for empty appends, the commit should simply be `commitIndex` directly (or limited by `matchIndex` for heartbeats).

**Fix:**
Added a CASE condition for empty appends:
```tla
commit == CASE subtype = "heartbeat"  -> Min({commitIndex[i], matchIndex[i][j]})
            [] lastEntry < range[1]   -> commitIndex[i]  \* Empty append
            [] OTHER                  -> Min({commitIndex[i], lastEntry})
```

**Files Modified:**
- `spec/etcdraft.tla:521-528`: Added CASE for empty appends in commit calculation

---

## 2026-01-11 - Separate HandleHeartbeatResponse from HandleAppendEntriesResponse

**Trace:** `../traces/async_storage_writes_append_aba_race.ndjson`
**Error Type:** Inconsistency Error

**Issue:**
Trace validation failed because `progressState` incorrectly transitioned from `StateProbe` to `StateReplicate` after receiving a `MsgHeartbeatResp`. The trace showed the state remaining `StateProbe`, but the spec changed it to `StateReplicate`.

**Root Cause:**
The original `HandleAppendEntriesResponse` action handled both regular `MsgAppResp` and `MsgHeartbeatResp` the same way, including state transition logic. However, in the actual raft implementation (raft.go:1495-1499), heartbeat responses only unpause message flow - they do NOT trigger state transitions.

**Fix:**
1. Added new `HandleHeartbeatResponse` action (lines 1293-1306):
   - Precondition: `m.msubtype = "heartbeat"`
   - Only clears `msgAppFlowPaused`
   - Handles inflight cleanup if in StateReplicate with full inflights
   - Does NOT modify `matchIndex`, `nextIndex`, or `progressState`

2. Modified `HandleAppendEntriesResponse` (line 1208):
   - Added precondition: `m.msubtype /= "heartbeat"`
   - Now only handles regular append responses

3. Updated `ReceiveDirect` (line 1469):
   - Added `HandleHeartbeatResponse` as an alternative for `AppendEntriesResponse` messages

**Reference code (raft.go:1495-1499):**
```go
case pb.MsgHeartbeatResp:
    pr.MsgAppFlowPaused = false
    if pr.State == tracker.StateReplicate && pr.Inflights.Full() {
        pr.Inflights.FreeFirstOne()
    }
    // No state transition!
```

**Files Modified:**
- `spec/etcdraft.tla:1293-1306`: Added HandleHeartbeatResponse action
- `spec/etcdraft.tla:1208`: Added msubtype precondition to HandleAppendEntriesResponse
- `spec/etcdraft.tla:1469`: Added HandleHeartbeatResponse to ReceiveDirect routing

---

## 2026-01-11 - Add Reply to NoConflictAppendEntriesRequest

**Trace:** `../traces/partition_and_recover.ndjson`
**Error Type:** Inconsistency Error

**Issue:**
Trace validation failed because followers were not sending AppendEntriesResponse after accepting entries via the `NoConflictAppendEntriesRequest` branch. The response was being sent elsewhere in trace comparison logic (`SendFollowerResponseIfLogged`), which was incorrect - the response should be part of the base modeling spec.

**Root Cause:**
The `NoConflictAppendEntriesRequest` action in `etcdraft.tla` only handled log appending and commit advancement, but did not include the `Reply()` call to send a response. Only `AppendEntriesAlreadyDone` and `ConflictAppendEntriesRequest` sent responses.

**Fix:**
1. Modified `NoConflictAppendEntriesRequest` signature to include `j` parameter (destination node)
2. Added `CommitTo(i, ...)` call after appending entries
3. Added `Reply([mtype |-> AppendEntriesResponse, ...], m)` call
4. Updated UNCHANGED to exclude `commitIndex` and `pendingMessages` (now modified)
5. Updated `AcceptAppendEntriesRequest` to pass `j` to `NoConflictAppendEntriesRequest`
6. Removed incorrect `SendFollowerResponseIfLogged` from trace comparison logic

**Reference code (raft.go HandleAppendEntries):**
All branches that successfully process entries should send a response back to the leader.

**Files Modified:**
- `spec/etcdraft.tla:416-438`: Added j parameter, CommitTo, and Reply to NoConflictAppendEntriesRequest
- `spec/etcdraft.tla:449`: Updated AcceptAppendEntriesRequest to pass j parameter
- `spec/Traceetcdraft.tla`: Removed SendFollowerResponseIfLogged

---

## 2026-01-11 - Fix HandleHeartbeatResponse inflights condition

**Trace:** `../traces/partition_and_recover.ndjson`
**Error Type:** Inconsistency Error

**Issue:**
Trace validation failed at line 155 with `inflights["1"]["3"] = {13, 14}` but trace expected 3 entries `{12, 13, 14}`. Entry 12 was incorrectly removed from inflights.

**Root Cause:**
In `HandleHeartbeatResponse`, the condition for freeing an inflight entry was `Cardinality(inflights[i][j]) >= MaxInflightMsgs`, which triggered when inflights count was exactly at capacity (3 >= 3). However, the trace showed that after heartbeat response processing, `inflights_count` remained 3, indicating `FreeFirstOne()` should NOT have been called.

The actual raft implementation (raft.go:1497-1499) uses `Full()` check which returns true only when strictly over capacity, not when at capacity.

**Fix:**
Changed condition from `>=` to `>`:
```tla
\* Before:
/\ IF progressState[i][j] = StateReplicate /\ Cardinality(inflights[i][j]) >= MaxInflightMsgs

\* After:
/\ IF progressState[i][j] = StateReplicate /\ Cardinality(inflights[i][j]) > MaxInflightMsgs
```

**Reference code (raft.go:1497-1499):**
```go
if pr.State == tracker.StateReplicate && pr.Inflights.Full() {
    pr.Inflights.FreeFirstOne()
}
```
Note: `Full()` returns true when count > capacity, not >= capacity.

**Files Modified:**
- `spec/etcdraft.tla:1301`: Changed >= to > in inflights capacity check

---

## 2026-01-11 - Add snapshotIndex/snapshotTerm validation and CompactLog support

**Trace:** `../traces/snapshot_and_recovery.ndjson`, `../traces/slow_follower_after_compaction.ndjson`
**Error Type:** Abstraction Gap

**Issue:**
The trace spec did not validate `snapshotIndex` and `snapshotTerm` fields, making trace validation less rigorous. Traces with log compaction (`compact` command) were not properly handled.

**Root Cause:**
1. The `ValidatePostStates` function did not check `log[i].snapshotIndex` and `log[i].snapshotTerm` against trace values
2. The `CompactLog` event from the `compact` command was not instrumented or handled in the trace spec
3. Initial state initialization did not read `snapshotIndex`/`snapshotTerm` from the trace

**Fix:**
1. Added `SnapshotIndex` and `SnapshotTerm` fields to `TracingState` struct in `state_trace.go`
2. Added `CompactLog` trace event emission to `interaction_env_handler_compact.go`
3. Added `CompactLogIfLogged` handler to `Traceetcdraft.tla`
4. Updated `ValidatePostStates` to validate snapshotIndex/snapshotTerm
5. Updated `TraceInitLogVars` to read initial snapshotIndex/snapshotTerm from trace

**Files Modified:**
- `raft/state_trace.go`: Added SnapshotIndex/SnapshotTerm to TracingState, updated makeTracingState
- `raft/rafttest/interaction_env_handler_compact.go`: Added CompactLog trace event emission
- `spec/Traceetcdraft.tla`: Added CompactLogIfLogged handler, updated ValidatePostStates and TraceInitLogVars

---

## 2026-01-11 - Fix CompactLog snapshotIndex calculation to use actual storage state

**Trace:** `../traces/snapshot_and_recovery.ndjson`
**Error Type:** Inconsistency Error

**Issue:**
After adding CompactLog support, validation still failed. The `CompactLog` event showed `snapshotIndex=10`, but subsequent events showed `snapshotIndex=11`, causing a mismatch.

**Root Cause:**
The CompactLog event instrumentation calculated `snapshotIndex` from the command parameter:
```go
snapshotIndex := newFirstIndex - 1  // Assumed: compact 11 → snapshotIndex = 10
```

However, all other trace events use `makeTracingState` which reads from actual storage state:
```go
snapshotIndex := r.raftLog.firstIndex() - 1  // Reads actual state
```

The problem is that `MemoryStorage.Compact(compactIndex)` transforms the entry at `compactIndex-1` into a dummy entry, which can cause `firstIndex()` to return a different value than expected. This led to CompactLog events being inconsistent with other events.

**Principle:** Trace events should reflect the **actual system state**, not assumptions based on command parameters. All events should use the same data source for consistency.

**Fix:**
Changed `interaction_env_handler_compact.go` to read snapshotIndex/snapshotTerm from actual storage state AFTER compaction:
```go
// Before (wrong - based on assumption):
snapshotIndex := newFirstIndex - 1
snapshotTerm, _ := env.Nodes[idx].Storage.Term(snapshotIndex)
env.Nodes[idx].Compact(newFirstIndex)

// After (correct - reads actual state):
env.Nodes[idx].Compact(newFirstIndex)
firstIndex, _ := env.Nodes[idx].Storage.FirstIndex()
snapshotIndex := firstIndex - 1
snapshotTerm, _ := env.Nodes[idx].Storage.Term(snapshotIndex)
```

This ensures CompactLog events are consistent with all other events, as they now use the same state source.

**Files Modified:**
- `raft/rafttest/interaction_env_handler_compact.go`: Read snapshotIndex/snapshotTerm from storage after compaction

---

## 2026-01-15 - Fix ChangeConf joint consensus constraint for V1 simple config changes

**Trace:** `../traces/confchange_v1_add_single.ndjson`, `../traces/confchange_add_remove.ndjson`, etc.
**Error Type:** Incorrect Spec Constraint (introduced by inv checking fix)

**Issue:**
After invariant checking fixes, 6 trace validations failed. The `ChangeConf` action rejected valid V1-style single-node config changes because of incorrect constraints added in inv_log.md Record #16.

**Root Cause:**
Record #16 in inv_log.md incorrectly interpreted the `enterJoint` flag:
- **Wrong interpretation:** `enterJoint=FALSE` means "leave joint" (requires being in joint config)
- **Correct interpretation:** `enterJoint=FALSE` means "Simple() change" (V1-style, single-node change)

According to `confchange/confchange.go`, there are THREE paths for config changes:
1. **EnterJoint()** (line 51): Enter joint config, can change multiple voters. Requires NOT in joint.
2. **LeaveJoint()** (line 94): Leave joint config. Requires IN joint. This is a SEPARATE action (empty ConfChangeV2).
3. **Simple()** (line 128): Simple single-node change. Requires NOT in joint AND `symdiff(old, new) <= 1`.

The constraint added in Record #16:
```tla
/\ (enterJoint = TRUE) => ~IsJointConfig(i)
/\ (enterJoint = FALSE) => IsJointConfig(i)  \* WRONG!
```

This prevented V1 API usage (AddNode, RemoveNode) which uses `enterJoint=FALSE` when NOT in joint config.

**Evidence from confchange/confchange.go:128-144:**
```go
func (c Changer) Simple(ccs ...pb.ConfChangeSingle) (tracker.Config, tracker.ProgressMap, error) {
    if joint(cfg) {
        err := errors.New("can't apply simple config change in joint config")
        return c.err(err)
    }
    // ...
    if n := symdiff(incoming(c.Tracker.Voters), incoming(cfg.Voters)); n > 1 {
        return tracker.Config{}, nil, errors.New("more than one voter changed without entering joint config")
    }
}
```

**Fix:**
Changed constraints in `ChangeConf` and `ChangeConfAndSend`:
```tla
\* Before (Record #16 - WRONG):
/\ (enterJoint = TRUE) => ~IsJointConfig(i)
/\ (enterJoint = FALSE) => IsJointConfig(i)

\* After (CORRECT):
/\ ~IsJointConfig(i)  \* Both EnterJoint and Simple require NOT being in joint
/\ (enterJoint = FALSE) =>
   Cardinality((GetConfig(i) \ newVoters) \union (newVoters \ GetConfig(i))) <= 1
   \* Simple change: symdiff must be <= 1 (only one voter can change)
```

**Files Modified:**
- `spec/etcdraft.tla:866-892`: Fixed ChangeConf constraints
- `spec/etcdraft.tla:894-919`: Fixed ChangeConfAndSend constraints

---

## 2026-01-15 - Fix ConflictAppendEntriesRequest off-by-one error in log truncation

**Trace:** `../traces/probe_and_replicate.ndjson`
**Error Type:** Inconsistency Error

**Issue:**
Trace validation failed at line 497 (ReceiveAppendEntriesResponse from node "1" to node "6"). The spec expected `m.msuccess = FALSE` but the trace showed `reject = false` (meaning success). Tracing back, node 2's log state was incorrect after processing an AppendEntriesRequest with conflict resolution.

**Root Cause:**
At trace line 453-454, node 2 receives an AppendEntries that triggers conflict resolution. The expected behavior is:
- Log should truncate from index 16 to 13 (removing conflicting entries)
- Then append one new entry, resulting in log length 14

However, the spec's `ConflictAppendEntriesRequest` action had an off-by-one error:
```tla
\* WRONG:
truncatePoint == ci - log[i].offset
/\ log' = [log EXCEPT ![i].entries = SubSeq(@, 1, truncatePoint - 1) \o newEntries]
```

For `ci = 14`, `offset = 1`:
- `truncatePoint = 14 - 1 = 13`
- `truncatePoint - 1 = 12`
- Result: `SubSeq(@, 1, 12)` keeps only entries[1..12] (indices offset..12 = 1..12)
- Log goes from 16 → 13 (wrong - should be 14)

The `-1` was incorrect. The truncation should keep entries up to index `ci - 1`, which in local terms is `ci - offset` (not `ci - offset - 1`).

**Evidence from raft/log.go:maybeAppend:**
```go
func (l *raftLog) maybeAppend(a logSliceRange, committed uint64) (lastnewi uint64, ok bool) {
    ci := l.findConflict(a.entries)
    // ci is the first index where log conflicts with entries
    // l.append will truncate from ci and append
    l.append(a.entries[ci-offset:]...)  // truncate + append atomic
}
```

The implementation does `l.append(entries[ci-offset:]...)` which keeps entries[1..ci-1] (local indices) and appends new entries starting at ci.

**Fix:**
Renamed variable for clarity and corrected the index calculation:
```tla
\* CORRECT:
/\ LET ci == FindFirstConflict(i, index, m.mentries)
       entsOffset == ci - index + 1
       newEntries == SubSeq(m.mentries, entsOffset, Len(m.mentries))
       \* Local index for ci-1 (the last entry to keep before appending)
       \* LogEntry(i, idx) = entries[idx - offset + 1], so for idx=ci-1:
       \* local_index = (ci-1) - offset + 1 = ci - offset
       keepUntil == ci - log[i].offset
   IN /\ ci > commitIndex[i]
      /\ log' = [log EXCEPT ![i].entries = SubSeq(@, 1, keepUntil) \o newEntries]
      /\ historyLog' = [historyLog EXCEPT ![i] = SubSeq(@, 1, ci - 1) \o newEntries]
```

**Files Modified:**
- `spec/etcdraft.tla:1169-1181`: Fixed ConflictAppendEntriesRequest truncation calculation

---

## 2026-01-15 - Remove incorrect newCommitIndex > commitIndex precondition

**Trace:** `../traces/basic.ndjson` and 23 other traces
**Error Type:** Incorrect Spec Constraint

**Issue:**
After adding `appliedConfigIndex` tracking for QuorumLogInv fix, 24 of 25 trace validations failed. The `AdvanceCommitIndex` action was rejecting valid Commit events where `commitIndex` didn't need to increase.

**Root Cause:**
An incorrect precondition was added to `AdvanceCommitIndex`:
```tla
/\ newCommitIndex > commitIndex[i]  \* WRONG - too restrictive
/\ CommitTo(i, newCommitIndex)
```

In etcd, `maybeCommit()` can be called even when there are no new entries to commit. The trace records a `Commit` event whenever `maybeCommit()` is called, regardless of whether `commitIndex` actually changes. The `CommitTo` helper already handles this correctly by using `Max({@, c})`, so no explicit guard is needed.

**Evidence from trace:**
```json
{"name":"Commit","nid":"1","state":{"commit":2,...},"log":3,...}
```
The Commit event has `commit=2`, which is the SAME as the current `commitIndex`. This is valid - the leader checked for new commits but found none.

**Fix:**
Removed the incorrect precondition:
```tla
\* Before (WRONG):
       IN
        /\ newCommitIndex > commitIndex[i]
        /\ CommitTo(i, newCommitIndex)

\* After (CORRECT):
       IN
        /\ CommitTo(i, newCommitIndex)
```

**Files Modified:**
- `spec/etcdraft.tla:850-851`: Removed `/\ newCommitIndex > commitIndex[i]` precondition
