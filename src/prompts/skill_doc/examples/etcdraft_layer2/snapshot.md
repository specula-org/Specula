# Module: Snapshot

## Responsibility

Send snapshot to followers that are too far behind to catch up via log entries. Allow log compaction.

## Actions

### SendSnapshot

**Responsibility**: Leader sends snapshot to lagging follower

**Trigger**: Leader cannot send entries (log compacted past nextIndex)

**Behavior**:
1. Check follower is recently active
2. Get snapshot from storage
3. Send MsgSnap with snapshot
4. Set progress state to Snapshot
5. Set pendingSnapshot to snapshot index

**Code Reference**: `maybeSendSnapshot()`

---

### HandleSnapshot

**Responsibility**: Follower applies snapshot from leader

**Trigger**: Receive MsgSnap

**Behavior**:
1. If snapshot is stale (index <= commitIndex): ignore
2. If log already has matching entry: just advance commit
3. Otherwise:
   - Restore log from snapshot (reset to snapshot index/term)
   - Update commitIndex to snapshot index
   - Apply configuration from snapshot metadata
4. Send MsgAppResp with new last index

**Code Reference**: `handleSnapshot()` → `restore()`

---

### SnapshotDone

**Responsibility**: Leader learns snapshot was applied

**Trigger**: Receive MsgAppResp after snapshot, or MsgSnapStatus

**Behavior**:
1. Clear pendingSnapshot
2. Transition progress state from Snapshot to Probe
3. Resume normal replication

**Code Reference**: `stepLeader()` MsgAppResp/MsgSnapStatus handling

---

## Action Boundaries

| Spec Action | Code Functions | Notes |
|-------------|----------------|-------|
| `SendSnapshot` | `maybeSendSnapshot` | Sets progress to Snapshot |
| `HandleSnapshot` | `handleSnapshot` → `restore` | Includes config restore |
| `SnapshotDone` | MsgAppResp/MsgSnapStatus handling | Transitions back to Probe |

## Progress State

When in Snapshot state:
- No AppendEntries sent
- Wait for snapshot application
- pendingSnapshot tracks the snapshot index

## Configuration in Snapshot

Snapshot metadata contains configuration:
- voters, votersOutgoing, learners, learnersNext, autoLeave
- Applied during `restore()` via `switchToConfig()`
