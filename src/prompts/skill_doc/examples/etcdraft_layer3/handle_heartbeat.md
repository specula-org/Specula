# Action: HandleHeartbeat

**Module**: Heartbeat

**Trigger**: Follower receives MsgHeartbeat

**Parameters**:
- `m.From`: leader id
- `m.Commit`: leader's known commit for this follower

**Control Flow**:
```
1. electionElapsed = 0
2. lead = m.From
3. Advance commit:
   IF m.Commit > committed:
      - committed = min(m.Commit, lastIndex)
4. Send MsgHeartbeatResp{To: m.From}
```

**Variable Changes**:
- `electionElapsed`: 0
- `lead`: m.From
- `committed`: may advance
