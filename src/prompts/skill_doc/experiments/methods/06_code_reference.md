# Experiment H: Code Reference Required

## Task

Generate a TLA+ specification for etcd/raft. **Every statement must have a code reference.**

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

### Rule: Every Statement Needs Code Reference

For EVERY line in your spec that describes behavior (not just syntax), you MUST include a code reference comment.

Format:
```tla
\* [raft.go:380] lead field tracks known leader
lead,

\* [raft.go:1206-1210] canVote conditions
canVote == \/ votedFor[s] = m.from                     \* [raft.go:1206]
           \/ (votedFor[s] = Nil /\ lead[s] = Nil)     \* [raft.go:1208]
           \/ (isPreVote /\ m.term > currentTerm[s])   \* [raft.go:1210]
```

### What Needs References

- Variable declarations: where is this state in code?
- Conditions: what line has this IF/condition?
- Assignments: what line updates this variable?
- Message fields: where are these fields defined?

### What Doesn't Need References

- TLA+ syntax (VARIABLES, LET, IN, etc.)
- Helper operators that are pure spec abstraction

### Self-Check Phase

After generating the spec, verify your references:

1. For each reference `[file:line]`, check:
   - Does the file exist?
   - Does line N actually contain the code you're referencing?
   - Is the logic at that line consistent with your spec?

2. Write verification results to:
```
/home/ubuntu/Specula/src/prompts/skill_doc/experiments/output_h/reference_check.md
```

Format:
```markdown
## Reference Verification

| Spec Line | Reference | Code Content | Match? |
|-----------|-----------|--------------|--------|
| `lead,` | raft.go:380 | `lead uint64` | ✓ |
| `canVote == ...` | raft.go:1206 | `canVote := r.Vote == m.From` | ✓ |
| ... | ... | ... | ... |

### Issues Found
- [List any incorrect references and corrections]
```

## Output

Write specification to:
```
/home/ubuntu/Specula/src/prompts/skill_doc/experiments/output_h/etcdraft.tla
```

Begin.
