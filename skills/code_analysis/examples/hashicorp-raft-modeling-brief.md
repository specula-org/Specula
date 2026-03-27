# Modeling Brief: hashicorp/raft

## 1. System Overview

- **System**: hashicorp/raft — Go Raft consensus library used by Consul, Nomad, Vault
- **Language**: Go, ~3600 LOC core logic
- **Protocol**: Raft (with PreVote extension, Leadership Transfer, joint consensus config changes)
- **Key architectural choices**:
  - Heartbeat runs in an **independent goroutine** separate from log replication (replication.go:385)
  - Uses **leader lease** (lastContact-based) instead of read-index for leader liveness
  - Tracks **two configurations**: `committed` and `latest` (uncommitted) separately
  - `persistVote` writes term and votedFor in **two separate disk operations** (raft.go:1135-1141)
- **Concurrency model**: Main state machine on single goroutine; replication and heartbeat on separate per-peer goroutines

## 2. Bug Families

### Family 1: Leader Cannot Self-Detect Failure (HIGH)

**Mechanism**: Leader fails to detect its own abnormality (storage hang, term superseded) and continues operating, causing cluster unavailability or split-brain.

**Evidence**:
- Historical: #503 — LogStore hang + heartbeat independence = entire cluster stuck (production)
- Historical: #522 — Leader cannot load snapshot, doesn't step down (production)
- Historical: #614 — Corrupted storage node wins elections repeatedly for 10 minutes (production)
- Code analysis: replication.go:412 — heartbeat does not check `resp.Term` (3 code paths, only heartbeat missing the check)

**Affected code paths**:
- `heartbeat()` (replication.go:385-439) — independent goroutine, no term check
- `replicateTo()` (replication.go:199-282) — checks resp.Term at line 239
- `pipelineDecode()` (replication.go:540-560) — checks resp.Term at line 548
- `checkLeaderLease()` (raft.go:1037-1082) — uses latestConfig for quorum

**Suggested modeling approach**:
- Variables: `leaseContact [Server -> SUBSET Server]`, `diskBlocked [Server -> BOOLEAN]`
- Actions: Split AppendEntries into `ReplicateEntries` (needs disk, checks term) and `SendHeartbeat` (no disk, no term check). Split response handling into `HandleReplicateResponse` (checks term) and `HandleHeartbeatResponse` (no term check, records contact).
- Add `CheckLeaderLease` and `DiskBlock`/`DiskUnblock` actions

**Priority**: High
**Rationale**: 3 severe production bugs sharing the same root cause. The heartbeat independence is a unique architectural choice not present in other Raft implementations. The heartbeat term-check omission (Issue #666) was confirmed as a real bug.

---

### Family 2: Configuration Change Safety (HIGH)

**Mechanism**: Inconsistent use of `committed` vs `latest` configuration across different code paths. Different functions use different versions of the configuration, which can lead to inconsistent decisions during config changes.

**Evidence**:
- Historical: commit `38cb186` — removed node can still vote
- Historical: commit `656e6c0` — NonVoter can transition to Candidate
- Historical: #472 — config divergence causes permanent election deadlock (production, multiple independent reports)
- Code analysis: committed vs latest usage table (analysis-report.md Section 6.3)

**Affected code paths**:
- `quorumSize()` uses latest (raft.go:1089)
- `checkLeaderLease()` uses latest (raft.go:1049)
- Leader step-down check uses committed (raft.go:798)
- Vote eligibility uses latest (raft.go:1645)
- `electSelf` sends to latest (raft.go:1096)

**Suggested modeling approach**:
- Variables: `committedConfig [Server -> SUBSET Server]`, `latestConfig [Server -> SUBSET Server]`
- Actions: Add `ProposeConfigChange` with one-uncommitted-at-a-time constraint. Update committed config in `AdvanceCommitIndex`. Followers update configs on AppendEntries accept.
- Key: election quorum, lease check, and commit quorum all use `latestConfig`, while leader step-down uses `committedConfig`

**Priority**: High
**Rationale**: 4+ historical bugs, has confirmed unfixed issue (#472). The committed/latest distinction is systematic and affects many code paths. TLA+ is well-suited for exploring config change + election interaction state space.

---

### Family 3: Non-Atomic Persistence (MEDIUM)

**Mechanism**: Operations that persist multiple values in separate disk writes. A crash between writes leaves inconsistent state.

**Evidence**:
- Code analysis: raft.go:1135-1141 — `persistVote` writes term then votedFor separately
- Historical: #85 — panic after restoring from old snapshot (open 10 years)
- Historical: #86 — `TrailingLogs=0` crashes after snapshot (open 8 years)
- Code analysis: raft.go:1540 — developer TODO acknowledging lastLog cache stale after truncation + StoreLogs failure

**Affected code paths**:
- `persistVote()` (raft.go:1135-1141) — SetUint64(term), then Set(votedFor)
- `appendEntries` truncation path (raft.go:1526-1543) — DeleteRange then StoreLogs

**Suggested modeling approach**:
- Variables: `persistedTerm`, `persistedVotedFor`, `pendingVote`
- Actions: Split `HandleRequestVoteRequest` grant-with-higher-term into two steps: step 1 persists term only, step 2 (`CompletePersistVote`) persists votedFor and sends response. Model `Crash` recovering from persisted (not volatile) state.
- Also provide `HandleRequestVoteRequestAtomic` for trace validation (normal non-crash path)

**Priority**: Medium
**Rationale**: Long-standing unfixed bugs (#85, #86). Crash recovery is a classic TLA+ strength. The non-atomic persistVote is a concrete crash window that could violate vote safety.

---

### Family 4: Copy-Paste / Incomplete Implementation (LOW)

**Mechanism**: PreVote implemented by copying RequestVote code, with some paths missing necessary modifications.

**Evidence**:
- Confirmed: raft.go:1738 — metrics label "requestVote" should be "requestPreVote" (PR #665 accepted)
- Historical: commit `42d3446` — granting PreVote incorrectly updates leader last-contact
- Code analysis: raft.go:1758 — requestPreVote missing `len(req.ID) > 0` guard

**Priority**: Low
**Rationale**: Not suitable for TLA+ modeling. These are code-level issues better found by systematic code comparison (requestVote vs requestPreVote, line by line).

---

### Family 5: Error Handling Gaps (LOW)

**Mechanism**: Incomplete recovery paths after disk/network failures, leaving intermediate state inconsistent.

**Evidence**:
- Code analysis: configuration.go:352 — EncodeConfiguration panics on error
- Code analysis: raft.go:2210 — timeoutNow has no state guard
- Historical: #498 — `Apply()` permanently deadlocks when quorum lost (3+ years open)

**Priority**: Low (for TLA+ modeling)
**Rationale**: Most of these are better verified by testing or code review. The timeoutNow issue requires Byzantine-like assumptions (abnormal node sending RPCs). The Apply() deadlock is a liveness issue in the Go channel implementation, not protocol logic.

## 3. Modeling Recommendations

### 3.1 Model

| What | Why | How |
|------|-----|-----|
| Independent heartbeat path | Family 1: root cause of 3 production bugs, confirmed Issue #666 | Split AppendEntries send/response into heartbeat vs replicate variants |
| Leader lease via lastContact | Family 1: lease is the mechanism that should detect stale leaders | `leaseContact` variable + `CheckLeaderLease` action |
| Disk IO blocking | Family 1: heartbeat continues when disk blocked (#503) | `diskBlocked` variable as guard on `ReplicateEntries` and `ClientRequest` |
| Committed vs latest config | Family 2: systematic code inconsistency, unfixed #472 | Two config variables, different actions use different ones |
| Non-atomic persistVote | Family 3: concrete crash window | Split vote persist into two steps + `Crash` recovering from persisted state |
| Crash and recovery | Family 3: validates persistence correctness | `Crash` action resets volatile state, recovers from persisted |

### 3.2 Do Not Model

| What | Why |
|------|-----|
| PreVote | Not related to any high-priority bug family. Adds state space without targeting known issues. Can be added later. |
| Metrics/logging | Family 4: code-level issue, not protocol logic |
| Snapshot | Important but not in the top bug families for this analysis round. Would significantly expand spec scope. |
| Pipeline replication | Optimization path. #612 is a real bug but requires modeling Go channel semantics, not protocol logic. |
| Leadership Transfer | timeoutNow guard (Family 5) is a robustness issue, not a protocol safety issue under normal operation |

## 4. Proposed Extensions

| Extension | Variables | Purpose | Bug Family |
|-----------|-----------|---------|------------|
| Heartbeat path | (split in actions, no new vars) | Distinguish heartbeat from replicate to model term-check omission | Family 1 |
| Leader lease | `leaseContact` | Track follower contacts for lease quorum check | Family 1 |
| Disk blocking | `diskBlocked` | Model heartbeat continuing when disk IO blocks | Family 1 |
| Dual configuration | `committedConfig`, `latestConfig` | Capture committed/latest config inconsistency | Family 2 |
| Non-atomic persist | `persistedTerm`, `persistedVotedFor`, `pendingVote` | Model crash between two disk writes | Family 3 |

## 5. Proposed Invariants

| Invariant | Type | Description | Targets |
|-----------|------|-------------|---------|
| ElectionSafety | Safety | At most one leader per term | Standard |
| LogMatching | Safety | Matching term at same index implies identical prefix | Standard |
| LeaderCompleteness | Safety | Committed entries appear in future leaders' logs | Standard |
| NoPhantomContact | Safety | Leader's lease contacts only count followers with term <= leader's term | Family 1, Issue #666 |
| LeaseImpliesLoyalty | Safety | If leader's lease check passes, a real quorum has term <= leader's term | Family 1 |
| ConfigSafety | Safety | At most one uncommitted config change at a time | Family 2 |

## 6. Findings Pending Verification

### 6.1 Model-Checkable

| ID | Description | Expected violation | Family |
|----|-------------|-------------------|--------|
| P2-A | Heartbeat phantom contact allows stale leader | NoPhantomContact, LeaseImpliesLoyalty | 1 |
| P2-C | checkLeaderLease uses latestConfig — miscalculated quorum during config change | LeaseImpliesLoyalty | 1, 2 |
| P3-A | quorumSize uses latest — incorrect quorum during config change | ElectionSafety | 2 |
| P3-B | electSelf sends to latest — votes from uncommitted members | ElectionSafety | 2 |
| P5-B | persistVote crash window — term persisted but votedFor not | ElectionSafety | 3 |

### 6.2 Test-Verifiable

| ID | Description | Suggested test approach |
|----|-------------|----------------------|
| P1-C | nextIndex non-atomic read-write (replication.go:256) | Go race detector test with concurrent heartbeat + replicate |
| P5-E | lastLog cache stale after truncation + StoreLogs failure | Unit test: mock StoreLogs to fail after DeleteRange |
| P5-F | EncodeConfiguration panic on corrupted input | Fuzz test with malformed log entries |

### 6.3 Code-Review-Only

| ID | Description | Suggested action |
|----|-------------|-----------------|
| P4-E | requestPreVote address decoding differs from requestVote | Compare line by line, submit PR if confirmed |
| P4-F | requestPreVote missing `len(req.ID) > 0` guard | No practical impact (PreVote only in new protocol) |
| P2-B | timeoutNow no state guard | Discuss with maintainers whether guard should be added |

## 7. Reference Pointers

- **Full analysis report**: `case-studies/hashicorp-raft/analysis-report.md`
- **Bug reports**: `case-studies/hashicorp-raft/scenarios/base/bugs/`
- **Key source files**:
  - `artifact/raft/raft.go` (core state machine, 2200 lines)
  - `artifact/raft/replication.go` (replication + heartbeat, 660 lines)
  - `artifact/raft/configuration.go` (config changes, 370 lines)
- **GitHub issues**: #503, #522, #614 (Family 1); #472 (Family 2); #85, #86 (Family 3)
- **Reference spec**: Raft paper (Ongaro & Ousterhout, 2014)
- **Reference TLA+ spec**: `data/repositories/workloads/raft/tla/etcdraft.tla` (for syntax patterns only)
