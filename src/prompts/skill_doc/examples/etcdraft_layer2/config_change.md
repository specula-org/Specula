# Module: Configuration Change

## Responsibility

Support dynamic membership changes safely using joint consensus. Handle adding/removing voters and learners.

## Actions

### ProposeConfigChange

**Responsibility**: Leader proposes configuration change

**Trigger**: Client proposes ConfChange or ConfChangeV2

**Behavior**:
1. Validate: no other pending config change
2. Validate: if in joint, only allow leave-joint
3. Validate: if not in joint, don't allow empty change
4. Append ConfChange entry to log
5. Track pendingConfIndex

**Code Reference**: `stepLeader()` case MsgProp with ConfChange entry

---

### ApplyConfigChange

**Responsibility**: Apply committed configuration change

**Trigger**: ConfChange entry is committed and applied

**Behavior**:
1. Parse ConfChange from entry
2. Determine change type:
   - Simple: add/remove single member
   - EnterJoint: start joint consensus
   - LeaveJoint: exit joint consensus
3. Update configuration:
   - Modify voters/votersOutgoing/learners
   - Update progress tracking
4. If autoLeave and in joint: propose leave-joint

**Code Reference**: `applyConfChange()` → `switchToConfig()`

---

## Configuration States

### Simple (Non-Joint)

- `voters`: Set of voting members
- `votersOutgoing`: empty
- Quorum: majority of voters

### Joint

- `voters`: incoming configuration
- `votersOutgoing`: outgoing configuration
- Quorum: majority of voters AND majority of votersOutgoing
- Transitions automatically to simple if autoLeave=true

## Change Types

| Type | Before | After |
|------|--------|-------|
| AddVoter | voters={A,B,C} | voters={A,B,C,D} |
| RemoveVoter | voters={A,B,C} | voters={A,B} |
| AddLearner | learners={} | learners={D} |
| PromoteLearner | learners={D} | voters includes D |
| EnterJoint | voters={A,B,C} | voters={A,B,C,D}, votersOutgoing={A,B,C} |
| LeaveJoint | voters={A,B,C,D}, votersOutgoing={A,B,C} | voters={A,B,C,D}, votersOutgoing={} |

## Action Boundaries

| Spec Action | Code Functions | Notes |
|-------------|----------------|-------|
| `ProposeConfigChange` | `stepLeader` with ConfChange | Validation and append |
| `ApplyConfigChange` | `applyConfChange` | Called on committed entry |

## Joint Consensus Flow

1. Propose multi-member change → EnterJoint
2. Entry replicates with joint quorum requirement
3. Entry commits (requires both old and new majorities)
4. Apply: enter joint state
5. If autoLeave: immediately propose LeaveJoint
6. LeaveJoint commits with joint quorum
7. Apply: exit joint state, only new config remains

## Learners

- Non-voting members
- Receive log entries but don't count for quorum
- Can be promoted to voter
- learnersNext: learners pending promotion after leaving joint
