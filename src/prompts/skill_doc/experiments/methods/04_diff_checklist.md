# Experiment E: Diff Checklist

## Task

Generate a TLA+ specification for etcd/raft, using a checklist of implementation differences from the Raft paper.

## Inputs

**Source Code**:
```
/home/ubuntu/Specula/data/workloads/etcdraft/artifact/raft/
```

**Scope Document**:
```
/home/ubuntu/Specula/src/prompts/skill_doc/examples/etcdraft_layer1.md
```

**Diff Checklist** (IMPORTANT - read this carefully):
```
/home/ubuntu/Specula/src/prompts/skill_doc/experiments/diff_checklist.md
```

## Instructions

1. Read the scope document to understand what to model
2. **Read the diff checklist carefully** - it lists where the code differs from the Raft paper
3. Read the source code
4. Generate the specification

**Important**: The diff checklist highlights implementation details that are often missed when following the Raft paper. Make sure your spec includes ALL items in the checklist.

## Output

Write the specification to:
```
/home/ubuntu/Specula/src/prompts/skill_doc/experiments/output_e/etcdraft.tla
```

Begin.
