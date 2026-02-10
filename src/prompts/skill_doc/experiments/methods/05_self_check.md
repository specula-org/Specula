# Experiment F: Step-by-Step Generation with Self-Check

## Task

Generate a TLA+ specification for etcd/raft, with self-verification after each action.

## Inputs

**Source Code**:
```
/home/ubuntu/Specula/data/workloads/etcdraft/artifact/raft/
```

**Scope Document**:
```
/home/ubuntu/Specula/src/prompts/skill_doc/examples/etcdraft_layer1.md
```

## Instructions

### Phase 1: Generate Skeleton

Read the scope document and source code, then generate:
- Constants
- Variables
- Type definitions
- Init predicate
- Action stubs (signatures only)
- Next predicate

Write to:
```
/home/ubuntu/Specula/src/prompts/skill_doc/experiments/output_f/etcdraft_skeleton.tla
```

### Phase 2: Implement Actions with Self-Check

For EACH action, follow this process:

**Step 1**: Identify the code location for this action

**Step 2**: Write the action implementation

**Step 3**: Self-check by answering these questions:
- What variables does the code read? Does my spec read the same?
- What variables does the code modify? Does my spec modify the same?
- What are ALL the conditions/branches in the code? Are they ALL in my spec?
- Is there any condition I wrote from memory instead of from code?

**Step 4**: If self-check reveals issues, fix them before moving to next action

Write self-check results to:
```
/home/ubuntu/Specula/src/prompts/skill_doc/experiments/output_f/self_check_log.md
```

### Actions to implement (in order):

1. **Election**: Timeout, HandleVoteRequest, HandleVoteResponse, BecomeLeader, BecomeFollower
2. **Replication**: ClientRequest, AppendEntries, HandleAppendEntries, HandleAppendResponse
3. **Commit**: AdvanceCommitIndex
4. **Heartbeat**: SendHeartbeat, HandleHeartbeat, HandleHeartbeatResponse
5. **Snapshot**: SendSnapshot, HandleSnapshot
6. **Network**: Receive, Drop, Duplicate

### Self-Check Template

For each action, write in self_check_log.md:

```
## Action: HandleVoteRequest

### Code Location
raft.go:1204-1254

### Variables Read
- Code: r.Vote, r.lead, r.Term, r.raftLog (lastIndex, lastTerm)
- Spec: [list what your spec reads]
- Match: [Yes/No, explain differences]

### Variables Modified
- Code: r.Vote, r.electionElapsed (if grant)
- Spec: [list what your spec modifies]
- Match: [Yes/No, explain differences]

### Conditions/Branches
- Code: canVote (3 conditions), isUpToDate check, grant vs reject
- Spec: [list your conditions]
- Match: [Yes/No, explain differences]

### Issues Found & Fixed
- [List any issues found and how you fixed them]
```

## Output

Write final specification to:
```
/home/ubuntu/Specula/src/prompts/skill_doc/experiments/output_f/etcdraft.tla
```

Begin with Phase 1.
