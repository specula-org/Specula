# Action: SendHeartbeat

**Module**: Heartbeat

**Trigger**: `tickHeartbeat()` when `heartbeatElapsed >= heartbeatTimeout`

**Parameters**: None

**Control Flow**:
```
1. heartbeatElapsed++
2. electionElapsed++

3. IF electionElapsed >= electionTimeout:
   - electionElapsed = 0
   - IF checkQuorum: check quorum activity
   - IF leadTransferee != None: abort transfer

4. IF state != StateLeader: return

5. IF heartbeatElapsed >= heartbeatTimeout:
   a. heartbeatElapsed = 0
   b. FOR each peer (excluding self):
      - commit = min(Progress[peer].Match, committed)
      - Send MsgHeartbeat{To: peer, Commit: commit}
```

**Variable Changes**:
- `heartbeatElapsed`: incremented, then reset
- `electionElapsed`: incremented
- `msgs`: MsgHeartbeat messages added
