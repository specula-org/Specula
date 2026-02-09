# Action: HandleVoteResponse

**Module**: Election

**Trigger**: `stepCandidate()` receives MsgVoteResp or MsgPreVoteResp

**Parameters**:
- `m.From`: voter id
- `m.Reject`: whether vote was rejected

**Control Flow**:
```
1. Record vote: votes[m.From] = !m.Reject

2. Tally votes:
   granted = count(votes == true)
   rejected = count(votes == false)

3. IF granted >= quorum:
   - IF state == StatePreCandidate:
      - becomeCandidate()
      - Send MsgVote to all voters
   - ELSE:
      - becomeLeader()
      - bcastAppend()

4. ELSE IF rejected >= quorum:
   - becomeFollower(currentTerm, None)
```

**Variable Changes (win election)**:
- `state`: StateLeader
- `lead`: self id
- Progress[self]: State = Replicate
- `pendingConfIndex`: lastIndex
- Log: append empty entry

**Variable Changes (lose election)**:
- `state`: StateFollower
- `lead`: None
