# Action: ApplyConfigChange

**Module**: ConfigChange

**Trigger**: Application applies committed ConfChange entry

**Parameters**:
- `cc`: ConfChangeV2

**Control Flow**:
```
1. Determine change type:
   - IF cc.LeaveJoint(): call LeaveJoint()
   - ELSE IF cc.EnterJoint(): call EnterJoint(autoLeave, changes)
   - ELSE: call Simple(changes)

2. Update configuration:
   trk.Config = newConfig
   trk.Progress = newProgress

3. Check self status:
   - IF self removed or demoted to learner:
      - IF leader AND stepDownOnRemoval: becomeFollower()

4. IF leader:
   - IF maybeCommit(): bcastAppend()
   - ELSE: probe new members

5. IF leadTransferee removed: abort transfer
```

**Variable Changes**:
- `trk.Config.Voters`: updated
- `trk.Config.Voters[1]`: outgoing (joint) or empty
- `trk.Config.Learners`: updated
- `trk.Progress`: new members added, removed deleted
- `isLearner`: updated
- `state`: may become Follower
