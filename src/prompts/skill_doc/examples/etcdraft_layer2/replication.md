# Module: Log Replication

## Responsibility

Replicate log entries from leader to followers. Ensure all nodes eventually have identical logs.

## Actions

### ClientRequest

**Responsibility**: Leader receives client request and appends to log

**Trigger**: Client proposes entry (MsgProp)

**Behavior**:
1. Reject if not leader or leadership transfer in progress
2. Assign term and index to entry
3. Append entry to local log
4. Self-ack the entry (send MsgAppResp to self)
5. Broadcast AppendEntries to all followers

**Code Reference**: `stepLeader()` case MsgProp → `appendEntry()` → `bcastAppend()`

---

### AppendEntries

**Responsibility**: Leader sends log entries to a follower

**Trigger**: Leader has entries to send, or needs to probe

**Behavior**:
1. Get prevLogIndex = nextIndex[follower] - 1
2. Get prevLogTerm = term at prevLogIndex
3. Get entries from nextIndex[follower] onwards
4. Send MsgApp with (prevLogIndex, prevLogTerm, entries, commitIndex)
5. Update progress state if needed

**Code Reference**: `sendAppend()` → `maybeSendAppend()`

---

### HandleAppendEntries

**Responsibility**: Follower processes AppendEntries from leader

**Trigger**: Receive MsgApp

**Behavior**:
1. If msg.term < currentTerm: reject
2. Reset election timeout
3. Update lead to message sender
4. If log doesn't match at prevLogIndex:
   - Reject with hint for faster backtracking
5. If log matches:
   - Delete conflicting entries (if any)
   - Append new entries
   - Update commitIndex to min(leaderCommit, lastNewEntryIndex)
6. Send response (success with lastIndex, or reject with hint)

**Code Reference**: `stepFollower()` case MsgApp → `handleAppendEntries()`

---

### HandleAppendResponse

**Responsibility**: Leader processes AppendEntries response

**Trigger**: Receive MsgAppResp

**Behavior**:
1. Mark follower as recently active
2. If rejected:
   - Decrease nextIndex based on reject hint
   - Change progress state to Probe if was Replicate
   - Retry with new nextIndex
3. If accepted:
   - Update matchIndex to response index
   - Update nextIndex to matchIndex + 1
   - Change progress state to Replicate if was Probe
   - Trigger commit check
   - Send more entries if available

**Code Reference**: `stepLeader()` case MsgAppResp

---

## Action Boundaries

| Spec Action | Code Functions | Notes |
|-------------|----------------|-------|
| `ClientRequest` | `stepLeader` MsgProp → `appendEntry` | Includes self-ack and broadcast |
| `AppendEntries` | `sendAppend` | Single follower |
| `HandleAppendEntries` | `handleAppendEntries` | Includes log update and response |
| `HandleAppendResponse` | `stepLeader` MsgAppResp | Includes retry on reject |

## Progress State Transitions

- **Probe**: Send one entry at a time, wait for response
- **Replicate**: Optimistically send entries, track in-flight
- **Snapshot**: Waiting for snapshot to be applied

Transitions:
- Probe → Replicate: on successful AppendResp
- Replicate → Probe: on rejected AppendResp
- Any → Snapshot: when follower needs snapshot
- Snapshot → Probe: after snapshot applied

## Implicit Operations

- Self-ack: Leader sends MsgAppResp to itself after appending, part of `ClientRequest`
- Broadcast: `bcastAppend()` calls `sendAppend()` for each follower
