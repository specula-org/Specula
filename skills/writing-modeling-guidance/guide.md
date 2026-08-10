# Writing Modeling Guidance

Read this when the user asks you to set up Specula for a new target, or to write or revise a modeling guidance file for them.

## What this file is

Modeling guidance is an optional text file supplied to a single-target run with `--guidance=/absolute/path/to/file`. Specula adds the same guidance to analysis, specification generation, harness generation, validation and repair, and bug confirmation. Severity classification does not use it.

The file may live anywhere and may use any filename. Specula records its absolute path when the run is created. A resumed run reuses that path and reads its current contents, so the user may edit the file between invocations without selecting a new path.

## When to write one

Write guidance if at least one of these is true:

- The user has hypotheses about specific scenarios they want investigated.
- There are known production incidents or upstream issues that phase agents should consider.
- Default phase behavior would over-scope a large target.
- The user wants to include or exclude specific subsystems.

If none apply, explain that guidance is optional and Specula can determine the modeling scope automatically. Avoid generic boilerplate that would weaken the agents' decisions.

## Hard rules

1. **State WHAT to verify, not HOW to model it.** Specification generation decides modeling abstractions.
2. **Phrase hypotheses as questions.** Ask whether an event can cause an outcome instead of declaring a formal invariant.
3. **Use real `file:line` locations or symbols when the user supplies them or asks for help locating relevant code.** Source anchors are optional and must not replace user intent.
4. **Keep it concise.** Aim for roughly 20–60 lines.
5. **Do not repeat what source analysis can discover.** Prioritize user intent, incidents, risks, and exclusions.
6. **Do not invent or silently complete user intent.** Ask a focused question when a missing priority, expected behavior, or assumption would materially change what gets verified. Resolving a user-selected question to code locations is useful; adding a new priority or contract is not.
7. **Treat expected behavior as a contract to test.** Do not assume it is implemented correctly or encode it into a model guard or assumption so that violations become unreachable.

## Keep / Remove

| Keep | Remove |
|---|---|
| Subsystem scope | TLA+ variable names, types, or operators |
| Scenario hypotheses phrased as questions | Predefined invariants with formal conditions |
| Key files and entry points | Prescribed action structure |
| Known incidents and design references | State-space bounds |
| Explicit exclusions and their reasons | Symmetry, fairness, or TLC configuration choices |

Self-test before writing: would the guidance still make sense if Specula switched modeling languages? If not, remove the modeling-specific prescription.

## Recommended structure

Start from `docs/modeling-guidance-template.md`. Complete every Required section and include only relevant Optional sections:

Required sections:

1. Goal: the decision or confidence the run should support.
2. Scope and boundary.
3. Prioritized questions, each pairing a trigger or condition with an observable outcome and the intended contract. Three to five is typical, but never invent filler to reach that range.
4. Module or component interactions that must be followed.
5. Non-obvious caller, environment, or fault assumptions; write `None` when there are none.

Optional sections:

1. Known incidents and references.
2. Suggested source locations or symbols.
3. Additional exploration after the priority questions.

Priority questions are a coverage floor, not an exploration ceiling. Agents should address every priority question without treating it as a known bug, then remain free to investigate adjacent risks derived from the code.

## Procedure

1. Confirm the target system, the user's priorities, and any hypotheses or exclusions.
2. If the user supplies source locations or requests help finding them, verify enough source to cite real paths, lines, or symbols. Research incidents when requested or needed to ground user-provided context; do not mine either as a substitute for missing intent.
3. Draft concise guidance using the template and hard rules.
4. Show the draft to the user before writing it, including any sections intentionally omitted.
5. Write the approved text to a user-chosen path and show the corresponding `specula run --guidance=/absolute/path/to/file ...` command.

## Anti-patterns

- Formal variable, operator, invariant, or action definitions.
- State-space bounds selected by the guidance author.
- Hypotheses presented as established bugs without evidence.
- Expected behavior encoded as an action guard or assumption instead of a property that may be violated.
- AI-generated priorities, contracts, or assumptions presented as if the user supplied them.
- README summaries or generic correctness advice.
- Long protocol background that source analysis can recover.

If the user requests modeling-specific prescriptions, explain the tradeoff and ask before including them. The user owns the guidance and the final decision.
