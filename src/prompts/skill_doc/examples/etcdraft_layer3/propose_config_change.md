# Action: ProposeConfigChange

**Module**: ConfigChange

**Trigger**: `stepLeader()` receives MsgProp with ConfChange entry

**Parameters**:
- Entry with Type: EntryConfChange or EntryConfChangeV2
- Entry.Data: marshaled ConfChange

**Control Flow**:
```
1. Parse ConfChange from entry.Data

2. Check constraints:
   alreadyPending = pendingConfIndex > applied
   alreadyJoint = len(Voters[1]) > 0
   wantsLeaveJoint = len(cc.Changes) == 0

3. Validate:
   - IF alreadyPending: reject
   - IF alreadyJoint AND NOT wantsLeaveJoint: reject
   - IF NOT alreadyJoint AND wantsLeaveJoint: reject

4. IF rejected:
   - Replace entry with empty EntryNormal
5. ELSE:
   - pendingConfIndex = entry index

6. Continue normal proposal flow:
   - Append to log
   - bcastAppend()
```

**Variable Changes**:
- `pendingConfIndex`: set to entry index
- `raftLog`: entry appended
