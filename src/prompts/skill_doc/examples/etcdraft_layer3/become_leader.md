# Action: BecomeLeader

**Module**: Election

**Trigger**: Candidate wins election (receives quorum of votes)

**Parameters**: None

**Control Flow**:
```
1. Assert state != StateFollower
2. step = stepLeader
3. reset(currentTerm):
   - lead = None
   - electionElapsed = 0
   - heartbeatElapsed = 0
   - Reset randomizedElectionTimeout
   - Reset all Progress: Match=0, Next=lastIndex+1
   - Progress[self].Match = lastIndex
   - pendingConfIndex = 0
   - uncommittedSize = 0
4. tick = tickHeartbeat
5. lead = self
6. state = StateLeader
7. Progress[self].BecomeReplicate()
8. Progress[self].RecentActive = true
9. pendingConfIndex = lastIndex
10. Append empty entry to log
```

**Variable Changes**:
- `state`: StateLeader
- `lead`: self id
- `pendingConfIndex`: lastIndex
- All Progress: reset
- Progress[self]: Match=lastIndex, State=Replicate, RecentActive=true
- Log: empty entry appended
