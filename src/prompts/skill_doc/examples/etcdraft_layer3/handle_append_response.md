# Action: HandleAppendResponse

**Module**: Replication

**Trigger**: Leader receives MsgAppResp

**Parameters**:
- `m.From`: follower id
- `m.Index`: follower's last index (or rejected index)
- `m.Reject`: whether append was rejected
- `m.RejectHint`: hint for next probe
- `m.LogTerm`: follower's term at hint

**Control Flow**:
```
1. pr = Progress[m.From]
2. pr.RecentActive = true

3. IF m.Reject:
   a. nextProbeIdx = m.RejectHint
   b. IF m.LogTerm > 0:
      - nextProbeIdx = findConflictByTerm(m.RejectHint, m.LogTerm)
   c. IF pr.MaybeDecrTo(m.Index, nextProbeIdx):
      - IF pr.State == StateReplicate: pr.BecomeProbe()
      - sendAppend(m.From)

4. ELSE (accept):
   a. IF pr.MaybeUpdate(m.Index):
      - IF StateProbe: pr.BecomeReplicate()
      - IF StateSnapshot AND can catch up: pr.BecomeReplicate()
      - IF StateReplicate: pr.Inflights.FreeLE(m.Index)

   b. IF maybeCommit():
      - bcastAppend()

   c. Continue sending if more entries available
```

**Variable Changes (reject)**:
- Progress[m.From].RecentActive: true
- Progress[m.From].Next: decreased
- Progress[m.From].State: may become Probe

**Variable Changes (accept)**:
- Progress[m.From].RecentActive: true
- Progress[m.From].Match: m.Index
- Progress[m.From].Next: m.Index + 1
- Progress[m.From].State: may become Replicate
- `committed`: may advance
