# Experiment B: Skill Doc (Layer 1 + 2 + 3)

## Task

Generate a TLA+ specification for etcd/raft using the structured skill documentation.

## Inputs

**Source Code**:
```
/home/ubuntu/Specula/data/workloads/etcdraft/artifact/raft/
```

**Documentation**:
```
Layer 1: /home/ubuntu/Specula/src/prompts/skill_doc/examples/etcdraft_layer1.md
Layer 2: /home/ubuntu/Specula/src/prompts/skill_doc/examples/etcdraft_layer2/
Layer 3: /home/ubuntu/Specula/src/prompts/skill_doc/examples/etcdraft_layer3/
```

## Instructions

### Phase 1: Generate Skeleton

1. Read Layer 1 (system overview and feature scope)
2. Read Layer 2 definitions.md (constants and variables)
3. Read Layer 2 module files (action boundaries)
4. Generate the specification skeleton:
   - Constants
   - Variables
   - Type definitions
   - Init predicate
   - Action stubs (name and signature only)
   - Next predicate

Write skeleton to:
```
/home/ubuntu/Specula/src/prompts/skill_doc/experiments/output_b/etcdraft_skeleton.tla
```

### Phase 2: Implement Actions

For each action in Layer 3, in order:
1. Read the action's control flow document
2. Implement the action based on the control flow
3. Reference source code only when clarification needed

Action implementation order:
1. Election: timeout, handle_vote_request, handle_vote_response, become_leader, become_follower
2. Replication: client_request, append_entries, handle_append_entries, handle_append_response
3. Commit: advance_commit_index
4. Heartbeat: send_heartbeat, handle_heartbeat, handle_heartbeat_response
5. Snapshot: send_snapshot, handle_snapshot, snapshot_done
6. ConfigChange: propose_config_change, apply_config_change
7. Network: receive, drop, duplicate

Write final specification to:
```
/home/ubuntu/Specula/src/prompts/skill_doc/experiments/output_b/etcdraft.tla
```

Begin.
