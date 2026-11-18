# Task: review the requirement-evidence annotations of a TLA+ model

Another engineer has annotated a TLA+ model of the etcd raft library, revision `{{REVISION}}` (`{{VERSION}}`, {{DATE}}). Above every checked property they placed a `REQ-EVIDENCE` comment block that states the property's intent, its status, and the evidence for it. Your job is an independent review of **every** block against the rules below. You correct blocks that the evidence does not support. You do not add new properties and you do not change what the model checks.

## Workspace

Work only inside `{{WS}}`.

| Path | Contents | Access |
|---|---|---|
| `spec-original/` | the model before annotation | read-only |
| `spec-annotated/` | the annotated model you are reviewing | read-only |
| `source/` | the etcd raft source at this revision | read-only |
| `tools/hist.sh` | read-only git history, **up to this revision only**; run it without arguments for usage | run |
| `ANNOTATION-RULES.md` | the rules the annotator followed | read |
| `spec-reviewed/` | create it: a copy of `spec-annotated/` with your corrections | write |
| `review/` | create it: your reports | write |
| `tmp/` | your scratch files | write |

Rules on information: use only the workspace. Do not read any other path, do not use the network, do not run `git` directly, and do not use any shared temporary or scratchpad directory. Do not use anything you may know about later versions of etcd raft, later commits, issues or known bugs. Do not read the annotator's reports (there are none in this workspace); judge each block only from its text and the cited sources.

## What to check, for every block

Read `ANNOTATION-RULES.md` first. Then, for each `REQ-EVIDENCE` block:

1. **Quote check.** Open each cited location. Does the quote appear there? Is the evidence type right?
   - A comment that only narrates what the code next to it does ("if X fails, bump Y", "initiate that now") is `impl`, not `comment`.
   - A test is evidence only for what it actually asserts.
2. **Support check.** This is the main one. For each non-`impl` evidence line, write down which part of the `intent` sentence the quote actually supports. Then ask: **does the non-`impl` evidence, read literally, support the whole intent as written?**
   - Watch for intents that generalize. "Never changes the log" is stronger than "never overwrites an existing entry". "Always appends X" is stronger than "appends X when Y".
   - Also check that the intent describes what the property's formula actually checks. Read the formula.
3. **Status check.** Given the evidence that survives checks 1–2, is the status right under the rules?
   - `requirement` needs non-`impl` evidence that supports the intent.
   - An intent supported only by `impl` evidence or narrating comments is `impl-abstraction` (it describes how this revision works) or `unknown` (it looks like a correctness requirement but nothing outside the code says so).
   - When only `impl` evidence remains, you may search the history yourself (`tools/hist.sh log -S'<identifier>' --oneline -- <file>`, then `tools/hist.sh show <commit>`) before deciding.
4. **Granularity check.** If part of what the formula checks is supported as a requirement and another part is not:
   - Prefer narrowing the `intent` to the supported part, with status `requirement`, and recording the rest in a `\* clause <name>: <status> — <reason>` line.
   - Or split the property following the "Splitting" rules in `ANNOTATION-RULES.md`, if its shape allows.
   - Do not leave a block whose single status covers clauses of different origin without `clause` lines.

## How to correct

- Edit only comment lines, and split definitions exactly as `ANNOTATION-RULES.md` allows. Never change a formula's text, an action, a helper or a `.cfg`.
- Keep the field format. Add the missing `-> <part supported>` suffix to every non-`impl` evidence line you keep.
- When you change a block, add one line `\* review:   <what you changed and why, one sentence>`. When you keep a block unchanged, add `\* review:   ok`.
- Apply the same standard to every block. Do not spend more care on some properties than on others because they look more interesting.

## Checks before you finish

1. SANY parses every edited module: `cd {{WS}}/spec-reviewed && java -cp {{TLA2TOOLS}} tla2sany.SANY <Module>.tla`.
2. `diff -ru spec-annotated spec-reviewed`: every non-comment changed line belongs to a split. List them.
3. Every in-scope property still has exactly one block, and every block has a `review:` line.

## Outputs

- `spec-reviewed/`: the corrected model.
- `review/decisions.md`: one row per block, with property, old status, new status, intent changed (yes/no), evidence lines retyped or removed, and a one-line reason.
- `review/summary.md`: counts. How many blocks were reviewed, kept, changed in intent, changed in status (old → new, as a small matrix), and changed in evidence type; how many new splits or clause lines; and the five blocks you were least sure about.
- `review/provenance.md`: every `tools/hist.sh` command and every file you read.
- `review/check.md`: the results of the checks above.

Finish with a short summary of `review/summary.md`.
