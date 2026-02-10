# Experiment D: Variable Extraction First

## Task

Generate a TLA+ specification for etcd/raft, but **extract variables from code first** before writing any spec logic.

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

### Phase 1: Variable Extraction (MUST complete before Phase 2)

Read the source code carefully and extract ALL state variables that need to be modeled.

For each variable, provide:
- Variable name in code
- Type in code
- Which file/line it's defined
- Brief description

Focus on these files:
- `raft.go`: main state (Term, Vote, lead, state, etc.)
- `log.go`: log state
- `tracker/progress.go`: replication progress
- `tracker/tracker.go`: configuration

**Write the extracted variable list to**:
```
/home/ubuntu/Specula/src/prompts/skill_doc/experiments/output_d/variables.md
```

### Phase 2: Generate Spec

Based on your extracted variable list (NOT from memory), generate the TLA+ specification.

Rules:
- You MUST use the variables you extracted in Phase 1
- Do NOT add variables that you didn't extract from code
- Do NOT omit variables that you extracted

**Write the specification to**:
```
/home/ubuntu/Specula/src/prompts/skill_doc/experiments/output_d/etcdraft.tla
```

Begin with Phase 1.
