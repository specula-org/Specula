# Action: HandleSnapshot

**Module**: Snapshot

**Trigger**: Follower receives MsgSnap

**Parameters**:
- `m.From`: leader id
- `m.Snapshot`: snapshot data

**Control Flow**:
```
1. electionElapsed = 0
2. lead = m.From

3. IF snapshot.Index <= committed:
   - Send MsgAppResp{Index: committed}
   - Return (stale)

4. IF log already has matching entry:
   - commitTo(snapshot.Index)
   - Send MsgAppResp{Index: committed}
   - Return (fast-forward)

5. Restore log from snapshot:
   - raftLog.restore(snapshot)

6. Restore configuration:
   - Reset Progress tracker
   - Apply config from snapshot metadata

7. Send MsgAppResp{Index: lastIndex}
```

**Variable Changes (full restore)**:
- `electionElapsed`: 0
- `lead`: m.From
- `raftLog`: reset to snapshot
- `committed`: snapshot index
- `trk.Config`: restored
- `trk.Progress`: reset

**Variable Changes (fast-forward)**:
- `electionElapsed`: 0
- `lead`: m.From
- `committed`: may advance
