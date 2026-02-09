# Action: AdvanceCommitIndex

**Module**: Commit

**Trigger**: `maybeCommit()` called after Progress.Match updates

**Parameters**: None

**Control Flow**:
```
1. Calculate quorum commit index:
   - Collect Match values from all Progress
   - FOR simple config:
      - Sort Match values
      - committed = Match[quorum position]
   - FOR joint config:
      - incoming_committed = quorum of incoming voters
      - outgoing_committed = quorum of outgoing voters
      - committed = min(incoming, outgoing)

2. IF committed > raftLog.committed:
   a. Get term at committed index
   b. IF term == currentTerm (Figure 8 safety):
      - raftLog.committed = committed
      - Return true

3. Return false
```

**Variable Changes (commit advances)**:
- `raftLog.committed`: new commit index

**Variable Changes (no change)**:
- None
