# Experiment G: Detailed Fidelity Analysis

## Task

Compare multiple TLA+ specs against source code for consistency, performing fine-grained analysis.

## Inputs

**Ground Truth (Source Code)**:
```
/home/ubuntu/Specula/data/workloads/etcdraft/artifact/raft/
```

**Specifications to Compare**:
| ID | Method | Path |
|----|--------|------|
| A | Baseline | `output_a/etcdraft.tla` |
| B | Skill Doc | `output_b/etcdraft.tla` |
| D | Var First | `output_d/etcdraft.tla` |
| E | Diff Checklist | `output_e/etcdraft.tla` |
| F | Self-Check | `output_f/etcdraft.tla` |
| H | Code Reference | `output_h/etcdraft.tla` |

---

## Part 1: Variable Completeness

Extract all state variables from code, check whether each spec models them.

### 1.1 Node State (raft.go struct raft)

| Variable | Code Location | Type | A | B | D | E | F | H |
|----------|---------------|------|---|---|---|---|---|---|
| `id` | raft.go:342 | uint64 | | | | | | |
| `Term` | raft.go:344 | uint64 | | | | | | |
| `Vote` | raft.go:345 | uint64 | | | | | | |
| `raftLog` | raft.go:350 | *raftLog | | | | | | |
| `state` | raft.go:357 | StateType | | | | | | |
| `isLearner` | raft.go:360 | bool | | | | | | |
| `lead` | raft.go:380 | uint64 | | | | | | |
| `leadTransferee` | raft.go:382 | uint64 | | | | | | |
| `pendingConfIndex` | raft.go:390 | uint64 | | | | | | |
| `electionElapsed` | raft.go:405 | int | | | | | | |
| `heartbeatElapsed` | raft.go:408 | int | | | | | | |
| `checkQuorum` | raft.go:411 | bool | | | | | | |
| `preVote` | raft.go:412 | bool | | | | | | |

### 1.2 Log State (log.go struct raftLog)

| Variable | Code Location | Type | A | B | D | E | F | H |
|----------|---------------|------|---|---|---|---|---|---|
| `committed` | log.go:47 | uint64 | | | | | | |
| `applied` | log.go:52 | uint64 | | | | | | |
| `unstable.entries` | log_unstable.go | []Entry | | | | | | |
| `unstable.snapshot` | log_unstable.go | *Snapshot | | | | | | |

### 1.3 Progress State (tracker/progress.go)

| Variable | Code Location | Type | A | B | D | E | F | H |
|----------|---------------|------|---|---|---|---|---|---|
| `Match` | progress.go:44 | uint64 | | | | | | |
| `Next` | progress.go:48 | uint64 | | | | | | |
| `State` | progress.go:50 | StateType | | | | | | |
| `PendingSnapshot` | progress.go:67 | uint64 | | | | | | |
| `RecentActive` | progress.go:73 | bool | | | | | | |
| `MsgAppFlowPaused` | progress.go:80 | bool | | | | | | |
| `Inflights` | progress.go:85 | *Inflights | | | | | | |
| `IsLearner` | progress.go:87 | bool | | | | | | |

### 1.4 Config State (tracker/tracker.go)

| Variable | Code Location | Type | A | B | D | E | F | H |
|----------|---------------|------|---|---|---|---|---|---|
| `Voters` | tracker.go:35 | JointConfig | | | | | | |
| `AutoLeave` | tracker.go:43 | bool | | | | | | |
| `Learners` | tracker.go:47 | map | | | | | | |
| `LearnersNext` | tracker.go:54 | map | | | | | | |
| `Votes` | tracker.go:122 | map[uint64]bool | | | | | | |

### 1.5 Variable Score

| Spec | Modeled | Total | Percentage |
|------|---------|-------|------------|
| A | | 30 | |
| B | | 30 | |
| D | | 30 | |
| E | | 30 | |
| F | | 30 | |
| H | | 30 | |

---

## Part 2: Action-Level Correctness

For each action, check whether each branch in code is correctly modeled in spec.

### 2.1 HandleVoteRequest (raft.go:1204-1254)

**Code Branches:**

| Branch | Code Line | Condition | A | B | D | E | F | H |
|--------|-----------|-----------|---|---|---|---|---|---|
| Term check: higher term | 1092-1123 | m.Term > r.Term | | | | | | |
| Term check: lower term | 1125-1178 | m.Term < r.Term → reject | | | | | | |
| canVote: already voted for sender | 1206 | r.Vote == m.From | | | | | | |
| canVote: not voted and no leader | 1208 | r.Vote == None && r.lead == None | | | | | | |
| canVote: PreVote future term | 1210 | MsgPreVote && m.Term > r.Term | | | | | | |
| Log up-to-date check | 1214 | isUpToDate(candLastID) | | | | | | |
| Grant vote | 1233-1249 | canVote && upToDate | | | | | | |
| Update Vote (real vote only) | 1248 | m.Type == MsgVote | | | | | | |
| Reset electionElapsed | 1247 | grant vote | | | | | | |
| Reject vote | 1250-1253 | !canVote \|\| !upToDate | | | | | | |

### 2.2 HandleVoteResponse (raft.go:1668-1710, stepCandidate)

| Branch | Code Line | Condition | A | B | D | E | F | H |
|--------|-----------|-----------|---|---|---|---|---|---|
| Ignore wrong response type | 1672-1677 | PreCandidate expects PreVoteResp | | | | | | |
| Record vote | 1692 | poll(m.From, m.Type, !m.Reject) | | | | | | |
| VoteWon + PreCandidate | 1696-1697 | → campaign(Election) | | | | | | |
| VoteWon + Candidate | 1698-1700 | → becomeLeader, bcastAppend | | | | | | |
| VoteLost | 1702-1705 | → becomeFollower | | | | | | |

### 2.3 HandleAppendEntries (raft.go:1786-1828)

| Branch | Code Line | Condition | A | B | D | E | F | H |
|--------|-----------|-----------|---|---|---|---|---|---|
| Stale: prev < committed | 1791-1793 | → reply with committed | | | | | | |
| Success: log matches | 1795-1797 | maybeAppend succeeds | | | | | | |
| Reject: log mismatch | 1799-1827 | → reply with hint | | | | | | |
| Hint calculation | 1818-1819 | findConflictByTerm | | | | | | |

### 2.4 HandleAppendResponse (raft.go:1376-1569, stepLeader)

| Branch | Code Line | Condition | A | B | D | E | F | H |
|--------|-----------|-----------|---|---|---|---|---|---|
| Mark RecentActive | 1380 | always | | | | | | |
| Reject: decrease Next | 1382-1509 | m.Reject | | | | | | |
| Reject: use hint | 1406, 1501 | m.LogTerm > 0 | | | | | | |
| Reject: BecomeProbe | 1505-1507 | was Replicate | | | | | | |
| Accept: MaybeUpdate | 1519 | !m.Reject | | | | | | |
| Accept: Probe → Replicate | 1521-1522 | State == Probe | | | | | | |
| Accept: Snapshot recovery | 1523-1537 | State == Snapshot | | | | | | |
| Accept: free Inflights | 1538-1539 | State == Replicate | | | | | | |
| maybeCommit | 1542 | after update | | | | | | |
| bcastAppend on commit | 1546 | commit advanced | | | | | | |

### 2.5 SendHeartbeat (raft.go:691-708)

| Branch | Code Line | Condition | A | B | D | E | F | H |
|--------|-----------|-----------|---|---|---|---|---|---|
| Commit calculation | 700 | min(pr.Match, committed) | | | | | | |

### 2.6 HandleHeartbeat (raft.go:1830-1833)

| Branch | Code Line | Condition | A | B | D | E | F | H |
|--------|-----------|-----------|---|---|---|---|---|---|
| commitTo | 1831 | advance commit | | | | | | |
| Send response | 1832 | always | | | | | | |

### 2.7 maybeSendSnapshot (raft.go:662-689)

| Branch | Code Line | Condition | A | B | D | E | F | H |
|--------|-----------|-----------|---|---|---|---|---|---|
| Check RecentActive | 665-668 | !RecentActive → skip | | | | | | |
| BecomeSnapshot | 684 | set state | | | | | | |

### 2.8 HandleSnapshot (raft.go:1835-1851)

| Branch | Code Line | Condition | A | B | D | E | F | H |
|--------|-----------|-----------|---|---|---|---|---|---|
| Stale snapshot | 1858 | index <= committed | | | | | | |
| Log matches | 1908-1914 | fast-forward commit | | | | | | |
| Full restore | 1917-1932 | replace log and config | | | | | | |

### 2.9 Action Score

| Spec | Correct Branches | Total Branches | Percentage |
|------|------------------|----------------|------------|
| A | | 50 | |
| B | | 50 | |
| D | | 50 | |
| E | | 50 | |
| F | | 50 | |
| H | | 50 | |

---

## Part 3: Specific Logic Comparison

For critical logic, compare code and each spec implementation line by line.

### 3.1 Vote Eligibility (raft.go:1206-1210)

**Code:**
```go
canVote := r.Vote == m.From ||
    (r.Vote == None && r.lead == None) ||
    (m.Type == pb.MsgPreVote && m.Term > r.Term)
```

**Spec A:**
```tla
[paste actual spec A code here]
```

**Spec B:**
```tla
[paste actual spec B code here]
```

... [repeat for D, E, F, H]

**Analysis:**
| Condition | Code | A | B | D | E | F | H |
|-----------|------|---|---|---|---|---|---|
| Vote == m.From | ✓ | | | | | | |
| Vote == None | ✓ | | | | | | |
| lead == None | ✓ | | | | | | |
| PreVote && m.Term > r.Term | ✓ | | | | | | |

### 3.2 Progress State Transitions

**Code (progress.go):**
```
Probe → Replicate: on successful MsgAppResp (raft.go:1521-1522)
Replicate → Probe: on rejected MsgAppResp (raft.go:1505-1507)
Any → Snapshot: maybeSendSnapshot (raft.go:684)
Snapshot → Probe: on MsgSnapStatus or recovery (raft.go:1523-1537, 1606-1618)
```

| Transition | A | B | D | E | F | H |
|------------|---|---|---|---|---|---|
| Probe → Replicate | | | | | | |
| Replicate → Probe | | | | | | |
| Any → Snapshot | | | | | | |
| Snapshot → Probe | | | | | | |

### 3.3 Commit Index Calculation

**Code (raft.go:778-782):**
```go
return r.raftLog.maybeCommit(entryID{term: r.Term, index: r.trk.Committed()})
```

| Aspect | Code | A | B | D | E | F | H |
|--------|------|---|---|---|---|---|---|
| Uses quorum of Match | ✓ | | | | | | |
| Requires term == currentTerm | ✓ | | | | | | |
| Joint consensus support | ✓ | | | | | | |

---

## Part 4: Final Scoring

### 4.1 Summary Table

| Spec | Variables (30) | Branches (50) | Logic (15) | Total (95) | % |
|------|----------------|---------------|------------|------------|---|
| A | | | | | |
| B | | | | | |
| D | | | | | |
| E | | | | | |
| F | | | | | |
| H | | | | | |

### 4.2 Cost-Benefit

| Method | Prep Files | Prep Effort | Score | ROI (Score/Effort) |
|--------|------------|-------------|-------|-------------------|
| A: Baseline | 1 | Low | | |
| B: Skill Doc | 30 | High | | |
| D: Var First | 1 | Medium | | |
| E: Diff Checklist | 2 | Low | | |
| F: Self-Check | 1 | Medium | | |
| H: Code Reference | 1 | Medium | | |

### 4.3 Ranking

1. [Spec] - Score: X/95 - Method: ...
2. ...

### 4.4 Key Findings

**Most commonly missed items:**
1. ...
2. ...

**Method that best prevents overfitting:**
...

**Recommended approach:**
...

Begin analysis.
