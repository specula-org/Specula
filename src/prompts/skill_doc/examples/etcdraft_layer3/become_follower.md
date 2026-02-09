# Action: BecomeFollower

**Module**: Election

**Trigger**: Higher term discovered, lost election, or step down

**Parameters**:
- `term`: new term
- `lead`: leader id (or None)

**Control Flow**:
```
1. step = stepFollower
2. reset(term):
   a. IF term != currentTerm:
      - Term = term
      - Vote = None
   b. lead = None
   c. electionElapsed = 0
   d. heartbeatElapsed = 0
   e. Reset randomizedElectionTimeout
   f. leadTransferee = None
   g. Reset votes
   h. Reset all Progress
   i. pendingConfIndex = 0
   j. uncommittedSize = 0
3. tick = tickElection
4. lead = lead parameter
5. state = StateFollower
```

**Variable Changes**:
- `state`: StateFollower
- `Term`: new term (if different)
- `Vote`: None (if term changed)
- `lead`: lead parameter
- `electionElapsed`: 0
- `heartbeatElapsed`: 0
- `leadTransferee`: None
- `pendingConfIndex`: 0
- `uncommittedSize`: 0
