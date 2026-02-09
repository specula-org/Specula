# Module: Election

## Responsibility

Elect a single leader through majority voting. Ensures that at most one leader exists per term.

## Actions

### Timeout

**Responsibility**: Follower/Candidate times out and starts election

**Trigger**: Election timeout expires (non-deterministic in spec)

**Behavior**:
1. Increment term (for real election) or keep term (for PreVote)
2. Transition to Candidate (or PreCandidate for PreVote)
3. Vote for self
4. Broadcast vote request to all other servers

**Code Reference**: `tickElection()` → `hup()` → `campaign()`

---

### HandleVoteRequest

**Responsibility**: Process incoming vote request

**Trigger**: Receive MsgVote or MsgPreVote

**Behavior**:
1. If msg.term > currentTerm: step down to follower, update term
2. Grant vote if:
   - Haven't voted for anyone else this term (or voted for this candidate)
   - Candidate's log is at least as up-to-date as ours
3. Send response (grant or reject)
4. If granted MsgVote: record votedFor

**Code Reference**: `Step()` case MsgVote/MsgPreVote

---

### HandleVoteResponse

**Responsibility**: Process vote response, potentially become leader

**Trigger**: Candidate receives MsgVoteResp or MsgPreVoteResp

**Behavior**:
1. Record vote (grant or reject)
2. Tally votes
3. If quorum reached:
   - For PreVote: start real election
   - For real Vote: become leader
4. If majority rejected: become follower

**Code Reference**: `stepCandidate()` case MsgVoteResp/MsgPreVoteResp

---

### BecomeLeader

**Responsibility**: Transition to leader state

**Trigger**: Candidate wins election (quorum votes)

**Behavior**:
1. Change state to Leader
2. Initialize nextIndex for all followers to log end + 1
3. Initialize matchIndex for all followers to 0
4. Set self as lead
5. Append empty entry (noop) to establish leadership

**Code Reference**: `becomeLeader()`

---

### BecomeFollower

**Responsibility**: Step down to follower

**Trigger**: See higher term, or lose election

**Behavior**:
1. Change state to Follower
2. Update term if higher
3. Reset votedFor if term changed
4. Update lead if known

**Code Reference**: `becomeFollower()`

---

## Action Boundaries

| Spec Action | Code Functions | Notes |
|-------------|----------------|-------|
| `Timeout` | `tickElection` → `hup` → `campaign` | Composite: timeout + start election |
| `HandleVoteRequest` | `Step` case MsgVote | Includes term update if needed |
| `HandleVoteResponse` | `stepCandidate` | May trigger BecomeLeader |
| `BecomeLeader` | `becomeLeader` | Includes noop entry append |
| `BecomeFollower` | `becomeFollower` | Called from multiple places |

## Implicit Operations

- Self-vote: `campaign()` sends MsgVoteResp to self, handled as part of `Timeout`
- PreVote doesn't change term until real election starts
