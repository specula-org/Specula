# Action: SnapshotDone

**Module**: Snapshot

**Trigger**: Leader receives MsgSnapStatus or MsgAppResp after snapshot

**Parameters**:
- `m.From`: follower id
- `m.Reject`: whether snapshot failed (MsgSnapStatus)

**Control Flow**:
```
MsgSnapStatus handling:
1. pr = Progress[m.From]
2. IF pr.State != StateSnapshot: return

3. IF NOT m.Reject (success):
   - pr.BecomeProbe()
4. ELSE (failure):
   - pr.PendingSnapshot = 0
   - pr.BecomeProbe()

5. pr.MsgAppFlowPaused = true

MsgAppResp handling (when in StateSnapshot):
1. IF pr.Match + 1 >= firstIndex:
   - pr.BecomeProbe()
   - pr.BecomeReplicate()
```

**Variable Changes**:
- Progress[m.From].State: StateProbe or StateReplicate
- Progress[m.From].PendingSnapshot: 0
- Progress[m.From].MsgAppFlowPaused: true
