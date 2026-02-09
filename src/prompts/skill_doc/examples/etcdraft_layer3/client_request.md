# Action: ClientRequest

**Module**: Replication

**Trigger**: `stepLeader()` receives MsgProp

**Parameters**:
- `m.Entries`: entries to propose

**Control Flow**:
```
1. IF entries empty: panic

2. IF Progress[self] == nil:
   - Return ErrProposalDropped (removed from cluster)

3. IF leadTransferee != None:
   - Return ErrProposalDropped (transfer in progress)

4. FOR each entry:
   IF entry is ConfChange:
      - Validate no pending config change
      - Validate joint state constraints
      - IF invalid: replace with empty entry
      - ELSE: pendingConfIndex = entry index

5. Check uncommitted size limit:
   IF exceeds limit:
      - Return ErrProposalDropped

6. Append entries to log:
   - Set Term and Index for each entry
   - raftLog.append(entries)

7. Send MsgAppResp to self (self-ack)

8. bcastAppend() to all followers
```

**Variable Changes**:
- `raftLog`: entries appended
- `pendingConfIndex`: updated if config change
- `uncommittedSize`: increased
