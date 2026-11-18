# Task: record the requirement evidence of every property in a TLA+ model

You are annotating an existing TLA+ model of {{SYSTEM}} ({{MODULE}}). The model was built for the source revision in `/work/source/`. Your job is to record, for every property the model checks, **why that property should hold**: what it means, where the evidence for it lives, and whether that evidence is a real requirement or only a description of how the code currently behaves.

You do not change what the model means. You only add comment lines.

## Workspace

| Path | Contents | Access |
|---|---|---|
| `/work/spec-original/` | the model as it is today | read-only |
| `/work/source/` | the source tree at this revision | read-only |
| `/work/tools/hist.sh` | read-only git history of the source, **up to this revision only**; run it without arguments for usage | run |
| `/work/out/spec-annotated/` | create it: a copy of `spec-original/` with your comments | write |
| `/work/out/` | your reports (see "Outputs") | write |

Rules on information:

- Use only `/work`. Put scratch files in `/work/out/tmp/`. Do not use the network, and do not run `git` directly; use `tools/hist.sh`.
- Annotate as an engineer working at this revision would. **Do not use anything you may know about later versions of this system, later commits, issues, or known bugs.** Every piece of evidence you record must be something you found in `/work` and can cite.
- If the evidence you can find is weak, say so. A truthful `unknown` is more useful than a guessed `requirement`.

## Which properties

Every operator that appears after `INVARIANT`, `INVARIANTS`, `PROPERTY` or `PROPERTIES` in any `.cfg` file under `spec-original/`, including commented-out lines (`\* INVARIANT X`), plus every property defined in `Update.tla` if that file exists. Reachability canaries (names ending in `NotReached` or similar, or whose comment says they are expected to be violated), type invariants, and observer bookkeeping get a short block with `status: model-internal`. Resolve aliases (`A == B`) to the definition that carries the content and annotate that one; give the alias a one-line block that points to it.

## The annotation block

Put one block immediately above each annotated definition, after any existing comments. Use exactly these field names, one field per line, each line starting with `\* `:

```tla
\* REQ-EVIDENCE <PropertyName>
\* intent:   <one sentence, plain English: what must always (or eventually) be true>
\* status:   requirement | impl-abstraction | model-internal | unknown | mixed
\* evidence: <type> <location> "<short exact quote, at most 15 words>" -> <part of intent it supports; omit for impl>
\* evidence: ...                       (as many lines as needed, strongest first)
\* watch:    <file:function or file:symbol>; <...>   (source places whose change should trigger a review)
\* verified: base
\* clause <name>: <status> — <evidence summary>      (only for mixed; one line per clause)
\* note:     <optional: evidence search only: what you searched for, what you did not find, why a source was not counted>
<PropertyName> == ...
```

Evidence `type` is one of:

| type | location format | meaning |
|---|---|---|
| `protocol` | `<paper or spec> §x` | a property stated by the protocol the system implements |
| `doc` | `source/<file>:<line>` | README, design notes, package documentation |
| `comment` | `source/<file>:<line>` | a code comment that states an intent, rule, contract or reason |
| `contract` | `source/<file>:<line>` | an interface, API, schema or protocol-buffer comment |
| `test` | `source/<file>:<line> <TestName>` | a test assertion that checks this behavior |
| `history` | `<commit>:<path>:<line>` or `<commit> (message)` | a comment, rule or explanation in an earlier commit or a commit message, found with `tools/hist.sh` |
| `impl` | `source/<file>:<line>` | the code that implements the behavior |

`impl` is evidence of what the code does, never of what it should do.

A comment counts as `comment` only if it states an intent, a rule, a contract or a reason ("must", "never", "so that", "callers may", "it is an error to"). A comment that only narrates what the next lines do is `impl`. For example, in a ticket-lock service, `// release the ticket and wake the next waiter` above the release code is `impl`; `// a ticket must never be granted to two holders at once` is `comment`.

Every non-`impl` evidence line ends with `-> <the part of the intent this quote supports>`. The `intent` must not claim more than the non-`impl` evidence supports. Watch for intents that generalize: in the ticket-lock example, "the queue is never reordered" is stronger than "a waiter is never skipped", and "every release wakes a waiter" is stronger than "a release wakes a waiter when one is queued". If the evidence supports only part of what the formula checks, narrow the intent and record the rest as `clause` lines.

`status` rules:

- `requirement`: at least one non-`impl` evidence line states or directly implies the intent. The code is expected to obey it; if the code ever violates it, the code is suspect.
- `impl-abstraction`: the property only describes how this revision happens to work, and nothing outside the implementation says it must stay that way. If the code changes, the property is expected to change with it.
- `model-internal`: type correctness, observer bookkeeping, reachability canaries, or other checks about the model itself.
- `unknown`: it looks like a correctness requirement, but you found only `impl` evidence. Record what you searched for in `note:`.
- `mixed`: the formula's clauses have different origins. Give the block-level intent for the whole formula and one `clause` line per group of clauses with the same origin, each with its own status and evidence summary.

`note:` is about the **evidence**, never about the **model**. It may say what you searched for, what you did not find, why a quote was not counted, and how the evidence relates to the intent. It must not say how the model's actions or helpers behave, whether the formula or the model matches the code, where the model is weaker, stronger or a proxy, or what could be wrong, unmodelled, vacuous or a false alarm. Those observations go only in `out/concerns.md`; do not mention `concerns.md` in the model. In the ticket-lock example, `note: searched lock.go and the history for "skip", "order", "fair"; nothing states fairness` is allowed; `note: the model grants tickets on enqueue rather than on release, see concerns.md` is not.

When a property has only `impl` evidence, search the history before settling on `unknown` or `impl-abstraction`: `tools/hist.sh log -S'<identifier from the implementing code>' --oneline -- <file>`, then `tools/hist.sh show <commit>` to read the change and the comments it removed or added. Requirements sometimes disappear from comments and survive only as code.

## What you must not change

Only add comment lines (`\* ...`). Do not edit, split, reorder or reformat any definition, action, helper, constant, variable, observer or `.cfg` file. If you believe a definition is wrong, write it in `out/concerns.md`, not in the model.

## Checks before you finish

1. Parse every module you edited with SANY: `cd /work/out/spec-annotated && java -cp /work/lib/tla2tools.jar:/work/lib/CommunityModules-deps.jar tla2sany.SANY <Module>.tla`. Record the commands and the last lines of output in `out/check.md`.
2. Every property in scope has exactly one `REQ-EVIDENCE` block.
3. Every `evidence` line with a `source/` location points to an existing file and line, and its quote appears on or near that line.

## Outputs

- `out/spec-annotated/`: the full annotated copy of the model (every file of `spec-original/`, changed or not).
- `out/ledger.md`: one table row per annotated property: property, status, evidence types, one-line intent; then counts by status.
- `out/provenance.md`: every `tools/hist.sh` command you ran, and the files you read. Be complete; this is audited.
- `out/concerns.md`: anything you think is wrong in the model, or evidence that contradicts a property.
- `out/check.md`: the results of the checks above.

Finish with a short summary: how many properties, how many per status, and the properties where you were least sure.
