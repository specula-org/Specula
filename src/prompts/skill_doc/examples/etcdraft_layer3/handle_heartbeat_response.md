# Action: HandleHeartbeatResponse

**Module**: Heartbeat

**Trigger**: Leader receives MsgHeartbeatResp

**Parameters**:
- `m.From`: follower id

**Control Flow**:
```
1. pr = Progress[m.From]
2. pr.RecentActive = true
3. pr.MsgAppFlowPaused = false

4. IF pr.Match < lastIndex OR pr.State == StateProbe:
   - sendAppend(m.From)
```

**Variable Changes**:
- Progress[m.From].RecentActive: true
- Progress[m.From].MsgAppFlowPaused: false
