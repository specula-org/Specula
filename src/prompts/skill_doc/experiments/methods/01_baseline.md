# Experiment A: Baseline (Layer 1 Only)

## Task

Generate a TLA+ specification for etcd/raft based on the system overview.

## Inputs

**Source Code**:
```
/home/ubuntu/Specula/data/workloads/etcdraft/artifact/raft/
```

**Documentation**:
```
/home/ubuntu/Specula/src/prompts/skill_doc/examples/etcdraft_layer1.md
```

## Instructions

1. Read the Layer 1 documentation to understand the system scope
2. Read the source code in the artifact directory
3. Generate a complete TLA+ specification that:
   - Defines all necessary constants and variables
   - Implements all actions within the feature scope
   - Follows TLA+ best practices

## Output

Write the specification to:
```
/home/ubuntu/Specula/src/prompts/skill_doc/experiments/output_a/etcdraft.tla
```

Begin.
