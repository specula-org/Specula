# Action: HandleVoteRequest

**Module**: Election

**Trigger**: `Step()` receives MsgVote or MsgPreVote

**Parameters**:
- `m.From`: candidate id
- `m.Term`: candidate's term
- `m.Index`: candidate's last log index
- `m.LogTerm`: candidate's last log term

**Control Flow**:
```
1. IF m.Term > currentTerm AND NOT MsgPreVote:
   - becomeFollower(m.Term, None)

2. IF m.Term < currentTerm:
   - Send reject response
   - Return

3. Determine canVote:
   canVote = (Vote == m.From) OR
             (Vote == None AND lead == None) OR
             (MsgPreVote AND m.Term > currentTerm)

4. Check log up-to-date:
   upToDate = (m.LogTerm > lastTerm) OR
              (m.LogTerm == lastTerm AND m.Index >= lastIndex)

5. IF canVote AND upToDate:
   - Send grant response {Reject: false}
   - IF MsgVote: Vote = m.From, electionElapsed = 0
6. ELSE:
   - Send reject response {Reject: true}
```

**Variable Changes (grant vote)**:
- `Vote`: m.From (only for MsgVote)
- `electionElapsed`: 0 (only for MsgVote)

**Variable Changes (reject vote)**:
- None
