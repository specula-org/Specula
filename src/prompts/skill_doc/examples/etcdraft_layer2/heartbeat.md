# Module: Heartbeat

## Responsibility

Maintain leader liveness. Propagate commit index to followers. Prevent unnecessary elections.

## Actions

### SendHeartbeat

**Responsibility**: Leader broadcasts heartbeat to all followers

**Trigger**: Heartbeat timeout (periodic)

**Behavior**:
1. For each follower:
   - Calculate commit to send: min(matchIndex[follower], commitIndex)
   - Send MsgHeartbeat with commit
2. Reset heartbeat timer

**Code Reference**: `tickHeartbeat()` → `bcastHeartbeat()` → `sendHeartbeat()`

---

### HandleHeartbeat

**Responsibility**: Follower processes heartbeat from leader

**Trigger**: Receive MsgHeartbeat

**Behavior**:
1. Reset election timeout
2. Update lead to message sender
3. Advance commitIndex to min(msg.commit, log length)
4. Send MsgHeartbeatResp

**Code Reference**: `stepFollower()` case MsgHeartbeat → `handleHeartbeat()`

---

### HandleHeartbeatResponse

**Responsibility**: Leader processes heartbeat response

**Trigger**: Receive MsgHeartbeatResp

**Behavior**:
1. Mark follower as recently active
2. Reset flow control pause
3. If follower is behind, send AppendEntries

**Code Reference**: `stepLeader()` case MsgHeartbeatResp

---

## Action Boundaries

| Spec Action | Code Functions | Notes |
|-------------|----------------|-------|
| `SendHeartbeat` | `tickHeartbeat` → `bcastHeartbeat` | Broadcast to all |
| `HandleHeartbeat` | `handleHeartbeat` | Includes commit advance |
| `HandleHeartbeatResponse` | `stepLeader` MsgHeartbeatResp | May trigger AppendEntries |

## Design Notes

- Heartbeat is essentially an empty AppendEntries
- Can be modeled separately or as special case of AppendEntries
- Separate modeling makes timeout behavior clearer
