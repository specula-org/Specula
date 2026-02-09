# Action: Timeout

**Module**: Election

**Trigger**: `tickElection()` called when `electionElapsed >= randomizedElectionTimeout`

**Parameters**: None

**Control Flow**:
```
1. Increment electionElapsed
2. IF promotable() AND pastElectionTimeout():
   a. Reset electionElapsed = 0
   b. IF preVote enabled:
      - becomePreCandidate()
      - Send MsgPreVote to all voters
   c. ELSE:
      - becomeCandidate()
      - Send MsgVote to all voters
   d. Send vote response to self (self-vote)
```

**Variable Changes**:
- `electionElapsed`: incremented, then reset to 0 if timeout fires
- `state`: StateCandidate or StatePreCandidate
- `Term`: +1 (only for StateCandidate)
- `Vote`: self id (only for StateCandidate)
- `lead`: None
- `votes`: reset
