# Action: AppendEntries

**Module**: Replication

**Trigger**: Leader calls `maybeSendAppend()` to send entries to follower

**Parameters**:
- `to`: target node id

**Control Flow**:
```
1. Get Progress: pr = Progress[to]

2. IF pr.IsPaused():
   - Return false

3. prevIndex = pr.Next - 1
4. prevTerm = raftLog.term(prevIndex)

5. IF error getting prevTerm (log truncated):
   - Call maybeSendSnapshot(to)
   - Return

6. Get entries = raftLog.entries(pr.Next, maxMsgSize)
   - IF StateReplicate AND Inflights.Full():
      - entries = [] (empty)

7. IF no entries AND not sendIfEmpty:
   - Return false

8. Send MsgApp:
   {
     To: to,
     Type: MsgApp,
     Index: prevIndex,
     LogTerm: prevTerm,
     Entries: entries,
     Commit: committed
   }

9. pr.SentEntries(len(entries), size)
10. pr.SentCommit(committed)
```

**Variable Changes**:
- Progress[to].Inflights: entries added
- `msgs`: MsgApp added
