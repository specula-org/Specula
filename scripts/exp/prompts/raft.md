## Focus: Raft Consensus Protocol

This system implements the Raft consensus protocol (Ongaro & Ousterhout, 2014).

### Key areas to model
- **Leader election**: RequestVote RPC, term advancement, split-vote, pre-vote (if present)
- **Log replication**: AppendEntries RPC, log matching, commit advancement
- **Safety**: Election safety, leader completeness, state machine safety
- **Membership changes**: Joint consensus or single-server changes (if implemented)
- **Log compaction**: Snapshotting, InstallSnapshot RPC (if implemented)

### Known Raft bug patterns to hunt for
1. **Stale leader**: Leader doesn't step down when partitioned, applies entries after term change
2. **Commit index regression**: commitIndex moves backward after leader change
3. **Log divergence on rejoin**: Node with longer but uncommitted log overrides committed entries
4. **Pre-vote bypass**: Pre-vote check skipped under certain partition/rejoin sequences
5. **Snapshot-log gap**: Snapshot at index N but log starts at N+2, missing entry N+1
6. **Configuration change race**: New config committed before old config fully replicated
7. **Read stale after leader change**: ReadIndex or lease-based read returns stale data during leadership transfer
8. **Non-monotonic term in AppendEntries**: Follower accepts entries from outdated leader
