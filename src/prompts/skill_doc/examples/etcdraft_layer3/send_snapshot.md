# Action: SendSnapshot

**Module**: Snapshot

**Trigger**: `maybeSendSnapshot()` when log truncated past follower's Next

**Parameters**:
- `to`: target node id

**Control Flow**:
```
1. pr = Progress[to]

2. IF NOT pr.RecentActive:
   - Return false (don't send to inactive)

3. snapshot = raftLog.snapshot()
4. IF snapshot unavailable:
   - Return false

5. pr.BecomeSnapshot(snapshot.Index):
   - State = StateSnapshot
   - PendingSnapshot = snapshot.Index

6. Send MsgSnap{To: to, Snapshot: snapshot}
7. Return true
```

**Variable Changes**:
- Progress[to].State: StateSnapshot
- Progress[to].PendingSnapshot: snapshot index
- `msgs`: MsgSnap added
