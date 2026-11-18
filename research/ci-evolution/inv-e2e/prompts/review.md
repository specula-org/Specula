# Task: review the requirement-evidence annotations of a TLA+ model

Another engineer has annotated a TLA+ model of {{SYSTEM}} ({{MODULE}}) for the source revision in `/work/source/`. Above every checked property they placed a `REQ-EVIDENCE` comment block stating the property's intent, its status, and the evidence for it. Your job is an independent review of **every** block against the rules in `/work/ANNOTATION-RULES.md`. You correct blocks that the evidence does not support. You only edit comment lines.

## Workspace

| Path | Contents | Access |
|---|---|---|
| `/work/spec-original/` | the model before annotation | read-only |
| `/work/spec-annotated/` | the annotated model you are reviewing | read-only |
| `/work/source/` | the source tree at this revision | read-only |
| `/work/tools/hist.sh` | read-only git history, **up to this revision only**; run it without arguments for usage | run |
| `/work/ANNOTATION-RULES.md` | the rules the annotator followed | read |
| `/work/out/spec-reviewed/` | create it: a copy of `spec-annotated/` with your corrections | write |
| `/work/out/` | your reports | write |

Rules on information: use only `/work`; scratch files go in `/work/out/tmp/`. Do not use the network and do not run `git` directly. Do not use anything you may know about later versions of this system, later commits, issues or known bugs. Judge each block only from its text and the cited sources.

## What to check, for every block

1. **Quote check.** Open each cited location. Does the quote appear there? Is the evidence type right? A comment that only narrates the code next to it is `impl`. A test is evidence only for what it actually asserts.
2. **Support check.** This is the main one. For each non-`impl` evidence line, write down which part of the intent the quote actually supports. Then ask: does the non-`impl` evidence, read literally, support the whole intent as written? Watch for intents that generalize beyond their evidence (for example "never changes X" when the evidence only says "never overwrites an existing X"). Also check that the intent describes what the formula actually checks. Read the formula.
3. **Status check.** Given the evidence that survives checks 1–2, is the status right? `requirement` needs non-`impl` evidence that supports the intent. An intent supported only by `impl` evidence or narrating comments is `impl-abstraction` or `unknown`. When only `impl` evidence remains, you may search the history yourself (`tools/hist.sh log -S'<identifier>' --oneline -- <file>`, then `tools/hist.sh show <commit>`).
4. **Granularity check.** If part of what the formula checks is supported as a requirement and another part is not, narrow the intent and record each part in a `\* clause <name>: <status> — <reason>` line, with block status `mixed`.

5. **Note check.** `note:` lines may only describe the evidence search: what was searched for, what was not found, why a source was not counted, how the evidence relates to the intent (rule in `ANNOTATION-RULES.md`). Remove or rewrite any sentence that describes the model itself: how its actions or helpers behave, whether it matches the code, where it is weaker, stronger or a proxy, or what might be wrong, unmodelled, vacuous or a false alarm. Move such sentences, unchanged, to `out/concerns.md`. Remove any reference to `concerns.md` from the model.

## How to correct

- Edit only comment lines. Never change a definition, an action, a helper or a `.cfg`.
- Keep the field format. Add the missing `-> <part supported>` suffix to every non-`impl` evidence line you keep.
- When you change a block, add `\* review:   <what you changed and why, one sentence>`. When you keep it, add `\* review:   ok`.
- Apply the same standard to every block. Do not spend more care on some properties than on others because they look more interesting.

## Checks before you finish

1. SANY parses every edited module: `cd /work/out/spec-reviewed && java -cp /work/lib/tla2tools.jar:/work/lib/CommunityModules-deps.jar tla2sany.SANY <Module>.tla`.
2. Every in-scope property still has exactly one block, and every block has a `review:` line.

## Outputs

- `out/spec-reviewed/`: the corrected model (every file).
- `out/decisions.md`: one row per block: property, old status, new status, intent changed (yes/no), evidence lines retyped or removed, one-line reason.
- `out/summary.md`: counts (reviewed, kept, intent changed, status changed as a small old → new matrix), and the five blocks you were least sure about.
- `out/provenance.md`: every `tools/hist.sh` command and every file you read.
- `out/concerns.md`: model observations you moved out of `note:` lines, with the property they came from.
- `out/check.md`: the results of the checks above.

Finish with a short summary of `out/summary.md`.
