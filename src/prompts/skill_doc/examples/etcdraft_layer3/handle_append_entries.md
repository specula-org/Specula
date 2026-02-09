# Action: HandleAppendEntries

**Module**: Replication

**Trigger**: Follower receives MsgApp

**Parameters**:
- `m.From`: leader id
- `m.Index`: prevLogIndex
- `m.LogTerm`: prevLogTerm
- `m.Entries`: entries to append
- `m.Commit`: leader's commit index

**Control Flow**:
```
1. electionElapsed = 0
2. lead = m.From

3. IF m.Index < committed:
   - Send MsgAppResp{Index: committed}
   - Return

4. IF raftLog.matchTerm(m.Index, m.LogTerm):
   a. Find conflict in entries
   b. IF conflict: truncate log at conflict index
   c. Append new entries
   d. Update committed = min(m.Commit, lastNewIndex)
   e. Send MsgAppResp{Index: lastNewIndex, Reject: false}

5. ELSE (log mismatch):
   a. hintIndex = min(m.Index, lastIndex)
   b. hintIndex, hintTerm = findConflictByTerm(hintIndex, m.LogTerm)
   c. Send MsgAppResp{
        Index: m.Index,
        Reject: true,
        RejectHint: hintIndex,
        LogTerm: hintTerm
      }
```

**Variable Changes (success)**:
- `electionElapsed`: 0
- `lead`: m.From
- `raftLog`: may truncate and append
- `committed`: advanced

**Variable Changes (reject)**:
- `electionElapsed`: 0
- `lead`: m.From
