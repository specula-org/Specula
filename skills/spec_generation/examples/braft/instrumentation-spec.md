# Instrumentation Spec: brpc/braft

Action-to-code mapping for trace harness generation. Each spec action maps to one or more source code locations where trace events must be emitted.

## Section 1: Trace Event Schema

### Event Envelope

```json
{
  "tag": "trace",
  "ts": "<monotonic_ns>",
  "event": {
    "name": "<spec_action_name>",
    "nid": "<server_id>",
    "state": {
      "term": "<int64>",
      "role": "<Follower|Candidate|Leader>",
      "votedFor": "<server_id|empty_string>",
      "commitIndex": "<int64>",
      "lastLogIndex": "<int64>",
      "lastLogTerm": "<int64>"
    },
    "msg": {
      "from": "<server_id>",
      "to": "<server_id>",
      "term": "<int64>",
      ...message-specific fields...
    }
  }
}
```

### State Fields (captured at every event)

| Impl Field | TLA+ Variable | Getter |
|-----------|---------------|--------|
| `_current_term` | `currentTerm` | `NodeImpl::_current_term` (under `_mutex`) |
| `_state` | `state` | `state2str(NodeImpl::_state)` |
| `_voted_id` | `votedFor` | `NodeImpl::_voted_id.to_string()` (empty if unset) |
| `_ballot_box->last_committed_index()` | `commitIndex` | `BallotBox::last_committed_index()` |
| `_log_manager->last_log_index()` | `lastLogIndex` | `LogManager::last_log_index()` |
| `last_log_id.term` | `lastLogTerm` | via `LogManager::get_term(last_log_index())` |

## Section 2: Action-to-Code Mapping

### 2.1 PreVote

| Field | Value |
|-------|-------|
| **Spec action** | `PreVote` |
| **Code location** | `node.cpp:1658-1660` (pre_vote, after _pre_vote_ctx initialization) |
| **Trigger point** | After `_pre_vote_ctx.init()` and before sending RPCs |
| **Trace event name** | `PreVote` |
| **Fields** | state snapshot only (no msg fields) |
| **Notes** | PreVote does NOT change term or votedFor; snapshot is pre-action state |

### 2.2 HandlePreVoteRequest

| Field | Value |
|-------|-------|
| **Spec action** | `HandlePreVoteRequest` |
| **Code location** | `node.cpp:2109-2174` (handle_pre_vote_request, before return) |
| **Trigger point** | After decision is made, before response is sent |
| **Trace event name** | `HandlePreVoteRequest` |
| **Fields** | `msg.from` = candidate_id, `msg.to` = self, `msg.term` = request.term(), `msg.granted` = response.granted(), `msg.rejectedByLease` = response.rejected_by_lease() |
| **Notes** | State snapshot is POST-action (after any term update). `msg.from` is the PreVote candidate. |

### 2.3 HandlePreVoteResponse

| Field | Value |
|-------|-------|
| **Spec action** | `HandlePreVoteResponse` |
| **Code location** | `node.cpp:1503-1581` (handle_pre_vote_response, after processing) |
| **Trigger point** | After vote counting / step_down decision |
| **Trace event name** | `HandlePreVoteResponse` |
| **Fields** | `msg.from` = peer_id (responder), `msg.to` = self, `msg.granted` = response.granted() |
| **Notes** | Also emit on RPC error (OnPreVoteRPCDone::Run, cntl.ErrorCode() != 0) for transport failure cases |

### 2.4 BecomeCandidate (ElectSelf)

| Field | Value |
|-------|-------|
| **Spec action** | `ElectSelf` |
| **Code location** | `node.cpp:1705-1710` (elect_self, after in-memory state update) |
| **Trigger point** | After `_current_term++`, `_state = STATE_CANDIDATE`, `_voted_id = _server_id`, BEFORE RPCs sent |
| **Trace event name** | `BecomeCandidate` |
| **Fields** | state snapshot only |
| **Notes** | State snapshot captures new term/candidate state. RPCs are sent AFTER this point (line 1735). Persist happens even later (line 1738). |

### 2.5 HandleRequestVoteRequest

| Field | Value |
|-------|-------|
| **Spec action** | `HandleRequestVoteRequest` |
| **Code location** | `node.cpp:2176-2289` (handle_request_vote_request, before return) |
| **Trigger point** | After persist (if grant) and before response is sent on the wire |
| **Trace event name** | `HandleRequestVoteRequest` |
| **Fields** | `msg.from` = candidate_id, `msg.to` = self, `msg.term` = request.term(), `msg.granted` = response.granted() |
| **Notes** | On grant path, state snapshot is AFTER persist (line 2271). Captures votedFor = candidate_id. |

### 2.6 HandleRequestVoteResponse

| Field | Value |
|-------|-------|
| **Spec action** | `HandleRequestVoteResponse` |
| **Code location** | `node.cpp:1394-1460` (handle_request_vote_response, after processing) |
| **Trigger point** | After vote counting / step_down |
| **Trace event name** | `HandleRequestVoteResponse` |
| **Fields** | `msg.from` = peer_id, `msg.to` = self, `msg.granted` = response.granted() |
| **Notes** | Self-vote is logged as `msg.from == msg.to`. Transport failure: emit from OnRequestVoteRPCDone::Run on error. |

### 2.7 BecomeLeader

| Field | Value |
|-------|-------|
| **Spec action** | `BecomeLeader` |
| **Code location** | `node.cpp:1940-1975` (become_leader, after state = Leader) |
| **Trigger point** | After `_state = STATE_LEADER` and `_follower_lease.reset()` |
| **Trace event name** | `BecomeLeader` |
| **Fields** | state snapshot only |
| **Notes** | Follower lease is reset at line 1949 — snapshot must capture AFTER this point. |

### 2.8 SendReplicateEntries

| Field | Value |
|-------|-------|
| **Spec action** | `ReplicateEntries` |
| **Code location** | `replicator.cpp:199-282` (_send_entries, after building AppendEntries request) |
| **Trigger point** | Before RPC send |
| **Trace event name** | `SendReplicateEntries` |
| **Fields** | `msg.from` = leader, `msg.to` = peer, `msg.term` = request.term(), `msg.prevLogIndex` = request.prev_log_index() |
| **Notes** | Distinguish from heartbeat by presence of `prevLogIndex` field (>= 1 for replicate). |

### 2.9 SendHeartbeat

| Field | Value |
|-------|-------|
| **Spec action** | `SendHeartbeat` |
| **Code location** | `replicator.cpp:385-395` (heartbeat, after building request) |
| **Trigger point** | Before RPC send |
| **Trace event name** | `SendHeartbeat` |
| **Fields** | `msg.from` = leader, `msg.to` = peer, `msg.term` = request.term() |
| **Notes** | Heartbeat does NOT include prevLogIndex. Omit field to distinguish from replicate in trace spec. |

### 2.10 SendInstallSnapshot

| Field | Value |
|-------|-------|
| **Spec action** | `SendInstallSnapshot` |
| **Code location** | `replicator.cpp:811-869` (_install_snapshot, before RPC send) |
| **Trigger point** | Before `cntl.request_attachment().append()` / RPC issue |
| **Trace event name** | `SendInstallSnapshot` |
| **Fields** | `msg.from` = leader, `msg.to` = peer, `msg.term` = request.term() |

### 2.11 HandleAppendEntriesRequest

| Field | Value |
|-------|-------|
| **Spec action** | `HandleAppendEntriesRequest` |
| **Code location** | `node.cpp:1441-1578` (handle_append_entries_request, before response) |
| **Trigger point** | After log append/truncation and commitIndex update, before response send |
| **Trace event name** | `HandleAppendEntriesRequest` |
| **Fields** | `msg.from` = leader_id, `msg.to` = self, `msg.term` = request.term(), `msg.prevLogIndex` = request.prev_log_index() (omit if 0 for heartbeat) |
| **Notes** | Post-state includes updated commitIndex and lastLogIndex. |

### 2.12 HandleReplicateResponse

| Field | Value |
|-------|-------|
| **Spec action** | `HandleReplicateResponse` |
| **Code location** | `replicator.cpp:359-500` (_on_rpc_returned, after processing) |
| **Trigger point** | After matchIndex/nextIndex update or step_down |
| **Trace event name** | `HandleReplicateResponse` |
| **Fields** | `msg.from` = peer, `msg.to` = leader, `msg.term` = response.term(), `msg.success` = response.success(), `msg.matchIndex` (on success) |
| **Notes** | State snapshot from leader node (via `node->` access after `increase_term_to` if stepped down). |

### 2.13 HandleHeartbeatResponse

| Field | Value |
|-------|-------|
| **Spec action** | `HandleHeartbeatResponse` |
| **Code location** | `replicator.cpp:279-333` (_on_heartbeat_returned, after processing) |
| **Trigger point** | After term check and lease contact update |
| **Trace event name** | `HandleHeartbeatResponse` |
| **Fields** | `msg.from` = peer, `msg.to` = leader, `msg.term` = response.term() |
| **Notes** | This handler DOES check term (unlike snapshot response). |

### 2.14 HandleInstallSnapshotRequest

| Field | Value |
|-------|-------|
| **Spec action** | `HandleInstallSnapshotRequest` |
| **Code location** | `snapshot_executor.cpp` (install_snapshot, after decision) |
| **Trigger point** | After term check and accept/reject decision |
| **Trace event name** | `HandleInstallSnapshotRequest` |
| **Fields** | `msg.from` = leader, `msg.to` = self, `msg.term` = request.term() |

### 2.15 HandleInstallSnapshotResponse

| Field | Value |
|-------|-------|
| **Spec action** | `HandleInstallSnapshotResponse` |
| **Code location** | `replicator.cpp:870-933` (_on_install_snapshot_returned, after processing) |
| **Trigger point** | After success/failure handling, before _send_entries() |
| **Trace event name** | `HandleInstallSnapshotResponse` |
| **Fields** | `msg.from` = peer, `msg.to` = leader, `msg.term` = response.term(), `msg.success` = response.success() |
| **Notes** | **BUG FAMILY 2**: This handler does NOT check response.term(). The trace captures the term but the spec action does not use it for step-down. |

### 2.16 AdvanceCommitIndex

| Field | Value |
|-------|-------|
| **Spec action** | `AdvanceCommitIndex` |
| **Code location** | `ballot_box.cpp:49-96` (commit_at, after _last_committed_index update) |
| **Trigger point** | After commitIndex advances |
| **Trace event name** | `AdvanceCommitIndex` |
| **Fields** | state snapshot only |
| **Notes** | May be called from multiple threads (replicator bthreads). Capture under ballot_box mutex. |

### 2.17 ProposeConfigChange

| Field | Value |
|-------|-------|
| **Spec action** | `ProposeConfigChange` |
| **Code location** | `node.cpp:3292-3325` (ConfigurationCtx::next_stage) |
| **Trigger point** | After config entry appended to log |
| **Trace event name** | `ProposeConfigChange` |
| **Fields** | `msg.to` = target server being added/removed |
| **Notes** | Config change has multiple stages. Emit at each stage transition. |

### 2.18 CheckLeaderLease

| Field | Value |
|-------|-------|
| **Spec action** | `CheckLeaderLease` |
| **Code location** | `lease.cpp:58-82` (LeaderLease::get_lease_info) or `node.cpp` (check_dead_nodes) |
| **Trigger point** | After lease check result is determined |
| **Trace event name** | `CheckLeaderLease` |
| **Fields** | state snapshot only |
| **Notes** | Only emit when lease check actually runs (not every timer tick). |

## Section 3: Special Considerations

### 3.1 State Access Challenges

- **commitIndex**: `BallotBox::last_committed_index()` uses `memory_order_relaxed` load. For trace consistency, read under ballot_box mutex or use `memory_order_acquire`.
- **lastLogIndex/lastLogTerm**: `LogManager` has its own mutex. To get consistent snapshots, must coordinate with node mutex or accept slight inconsistency on async events (use weak validation in trace spec).
- **Persisted state**: `persistedTerm`/`persistedVotedFor` are not directly accessible. Shadow variables needed in `FileBasedSingleMetaStorage` or hook into `set_term_and_votedfor()`.

### 3.2 Concurrency and Event Ordering

- **Replicator bthreads**: Each peer has its own replicator bthread. Response handlers (_on_rpc_returned, _on_heartbeat_returned, _on_install_snapshot_returned) run in separate bthreads. Events from different replicators may interleave.
- **Log manager disk thread**: Disk writes are async. The trace may show `HandleAppendEntriesRequest` before the disk write completes.
- **Timer callbacks**: `election_timer`, `vote_timer`, `stepdown_timer`, `snapshot_timer` all run in timer threads. Their events may interleave with RPC handlers.
- **Node mutex serialization**: Most state transitions are serialized by `NodeImpl::_mutex`. Instrumentation points under this mutex have natural ordering. Points outside the mutex (replicator bthreads) require care.

### 3.3 Bootstrap State

braft initializes with `term=0`, empty log, and `state=Follower`. If a bootstrap configuration is provided, it writes a config entry at index 1 with term 1. The trace Init should capture the initial state after bootstrap completes.

For trace validation, if bootstrap writes a config entry, `TraceInit` should set `log` = `<<[term |-> 1, type |-> ConfigEntry, config |-> Server]>>` and `currentTerm` = 1.

### 3.4 Serialization Notes

- **PeerId serialization**: braft uses `ip:port:idx` format. For trace, extract a stable server ID (e.g., `s1`, `s2`, `s3`) from a mapping table.
- **Empty votedFor**: braft uses `PeerId::EMPTY_PEER` (all zeros). Serialize as empty string `""` in JSON; trace spec maps to `Nil`.
- **Config serialization**: Configuration is a set of PeerIds. Serialize as array of server IDs.
