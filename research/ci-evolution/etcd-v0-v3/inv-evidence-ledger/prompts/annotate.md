# Task: record the requirement evidence of every property in a TLA+ model

You are annotating an existing TLA+ model of the etcd raft library. The model was built for revision `{{REVISION}}` (`{{VERSION}}`, {{DATE}}). Your job is to record, for every property the model checks, **why that property should hold**: what it means, where the evidence for it lives, and whether that evidence is a real requirement or only a description of how the code currently behaves.

You do not change what the model means. You add comments, and in one narrowly defined case you split a property into parts with the same meaning (see "Splitting").

## Workspace

Work only inside `{{WS}}`.

| Path | Contents | Access |
|---|---|---|
| `spec-original/` | the model as it is today | read-only |
| `source/` | the etcd raft source at this revision | read-only |
| `tools/hist.sh` | read-only git history of the source, **up to this revision only** | run it; see `tools/hist.sh` with no arguments for usage |
| `spec-annotated/` | create it: a copy of `spec-original/` with your edits | write |
| `out/` | create it: your reports (see "Outputs") | write |

Rules on information:

- Use only the workspace. Put any helper scripts or scratch files in `{{WS}}/tmp/`, not in any shared temporary or scratchpad directory. Do not read any other path on this machine, do not use the network, and do not run `git` directly; use `tools/hist.sh`.
- Annotate as an engineer working at this revision would. **Do not use anything you may know about later versions of etcd raft, later commits, issues, or known bugs.** Every piece of evidence you record must be something you found in the workspace and can cite.
- If the evidence you can find is weak, say so. A truthful `unknown` is more useful than a guessed `requirement`.

## Which properties

Every operator that appears after `INVARIANT`, `INVARIANTS`, `PROPERTY` or `PROPERTIES` in any `.cfg` file under `spec-original/`, including commented-out lines (`\* INVARIANT X`), plus every property defined in `Update.tla` if that file exists. Reachability canaries (names ending in `NotReached`, `NotAppended`, or whose comment says they are expected to be violated) get a short block with `status: model-internal`. Resolve aliases (`A == B`) to the definition that carries the content, and annotate that definition; give the alias a one-line block that points to it.

## The annotation block

Put one block immediately above each annotated definition. Use exactly these field names, one field per line, each line starting with `\* `:

```tla
\* REQ-EVIDENCE <PropertyName>
\* intent:   <one sentence, plain English: what must always (or eventually) be true>
\* status:   requirement | impl-abstraction | model-internal | unknown
\* evidence: <type> <location> "<short exact quote, at most 15 words>" -> <part of intent it supports; omit for impl>
\* evidence: ...                       (as many lines as needed, strongest first)
\* watch:    <file:function or file:symbol>; <...>   (source places whose change should trigger a review of this property)
\* verified: {{VERSION}}
\* note:     <optional, free text, e.g. what you searched for and did not find>
<PropertyName> == ...
```

Evidence `type` is one of:

| type | location format | example |
|---|---|---|
| `protocol` | `Raft-thesis §x.y` or `Raft-paper §x` | a property stated by the Raft protocol itself |
| `doc` | `source/<file>:<line>` | `README.md`, `doc.go`, `design.md` |
| `comment` | `source/<file>:<line>` | a code comment that states intent or a rule |
| `proto` | `source/raftpb/<file>:<line>` | a comment in a `.proto` file |
| `test` | `source/<file>:<line> <TestName>` | a test assertion that checks this behavior |
| `history` | `<commit>:<path>:<line>` or `<commit> (message)` | a comment, rule or explanation that exists in an earlier commit or in a commit message, found with `tools/hist.sh` |
| `impl` | `source/<file>:<line>` | the code that implements the behavior |

`impl` is evidence of what the code does, never of what it should do.

A code comment counts as `comment` only if it states an intent, a rule, a contract or a reason ("must", "never", "so that", "callers may", "it is an error to"). A comment that only narrates what the next lines of code do ("if we could not append the entry, bump the index", "initiate that now") is `impl` evidence, because it describes the implementation, not a requirement.

Every non-`impl` evidence line ends with `-> <the part of the intent this quote supports>`. The `intent` must not claim more than the non-`impl` evidence supports. If the evidence supports only part of what the property checks, either narrow the intent to that part (and record the remainder in `note:` with its own status) or split the property (see "Splitting").

`status` rules:

- `requirement`: at least one non-`impl` evidence line states or directly implies the property. The code is expected to obey it; if the code ever violates it, the code is suspect.
- `impl-abstraction`: the property only describes how this revision happens to work (for example "this step never changes X"), and nothing outside the implementation says it must stay that way. If the code changes, the property is expected to change with it.
- `model-internal`: type correctness, observer bookkeeping, reachability canaries, or other checks about the model itself rather than the system.
- `unknown`: it looks like a correctness requirement, but you found only `impl` evidence. Record what you searched for in `note:`.

For `history` evidence: requirements sometimes disappear from comments and survive only as code. When a property has only `impl` evidence, search the history before settling on `unknown` or `impl-abstraction`: for example `tools/hist.sh log -S'<identifier from the implementing code>' --oneline -- <file>`, then `tools/hist.sh show <commit>` to read the change and the comments it removed or added. Cite the commit and the exact quote.

## Splitting

A property is often a conjunction of clauses that have different origins: one clause is a protocol requirement, another only describes the current code. One `status` cannot describe both. Rule: **after your edit, every annotated property has a single origin.**

When a property's clauses have different statuses, and the property has the shape

```tla
P == \A x \in S : C1 /\ C2 /\ ... /\ Cn          (or simply  P == C1 /\ C2 /\ ... /\ Cn)
```

split it like this, which does not change its meaning:

```tla
\* REQ-EVIDENCE P_<Part1>
...
P_<Part1> == \A x \in S : C1
\* REQ-EVIDENCE P_<Part2>
...
P_<Part2> == \A x \in S : C2 /\ C3        (group clauses that share one origin)

\* REQ-EVIDENCE P
\* intent:   conjunction of the parts below; kept so existing configs and references still work
\* status:   model-internal
\* note:     split by origin into P_<Part1> (requirement), P_<Part2> (impl-abstraction)
P == P_<Part1> /\ P_<Part2>
```

- Choose short descriptive part names, for example `AckPreservation_LogUnchanged`.
- Keep the original name, defined as the conjunction, so every `.cfg` and every reference keeps working. Do not edit any `.cfg`.
- Copy clause text exactly. Do not reword, simplify or "fix" any clause, even if you think it is wrong; put your concern in `note:`.
- If a property mixes origins but does not have that shape (for example the clauses live inside one `LET ... IN` and share local definitions), do not split it. Annotate it once, and add one `\* clause <name>: <status> — <evidence summary>` line per clause inside its block, after `note:`.

## What you must not change

Everything except comment lines and the split definitions described above: no edits to actions, `Init`, `Next`, helpers, constants, variables, observers, or `.cfg` files. If you believe a definition is wrong, write it in `out/concerns.md`, not in the model.

## Checks before you finish

1. Parse every module you edited with SANY, before and after, from inside the spec directory:
   `cd {{WS}}/spec-annotated && java -cp {{TLA2TOOLS}} tla2sany.SANY <Module>.tla`
   Both must parse. Record the commands and the last lines of output in `out/check.md`.
2. Diff `spec-original/` against `spec-annotated/` (`diff -ru`). Every changed line must be a comment line, a split part definition, or the rewritten conjunction of a split property. Record `diff -ru ... | grep -c '^[+-][^+-]'` and a list of the non-comment changed lines in `out/check.md`.
3. Every property in scope has exactly one `REQ-EVIDENCE` block. Every `evidence` line with a `source/` location must point to an existing file and line, and its quote must appear on or near that line.

## Outputs

- `spec-annotated/`: the full annotated copy of the model.
- `out/ledger.md`: one table row per annotated property, with property, status, evidence types (for example `test, comment, impl`), split from (if any), and one-line intent; then counts by status.
- `out/splits.md`: each split, with the original definition, the parts, and why the clauses have different origins.
- `out/provenance.md`: every `tools/hist.sh` command you ran, and the list of files you read. Be complete; this is audited.
- `out/concerns.md`: anything you think is wrong in the model, or evidence that contradicts a property. Do not act on it.
- `out/check.md`: the results of the checks above.

Finish with a short summary: how many properties, how many per status, how many splits, and the properties where you were least sure.
