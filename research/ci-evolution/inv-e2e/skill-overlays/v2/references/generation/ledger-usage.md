# Requirement-Evidence Annotations

The prior suite may carry a `REQ-EVIDENCE` comment block above each checked property. The blocks were written from the prior revision only, by an annotator who did not see this update. They record why each property should hold, so that a later update can tell a requirement from a description of how the old code happened to work. Use them together with [Divergence Evidence](divergence-evidence.md): the blocks tell you which properties to distrust and why; the separating states show whether the distrust is justified.

## 1. Block Format

```tla
\* REQ-EVIDENCE <PropertyName>
\* intent:   <what must always (or eventually) be true>
\* status:   requirement | impl-abstraction | unknown | model-internal | mixed
\* evidence: <type> <location> "<quote>" -> <part of the intent it supports>
\* watch:    <file:symbol>; ...
\* verified: <revision label>
\* clause <name>: <status> — <evidence summary>      (only when status is mixed)
\* note:     <remarks>
```

- `requirement`: non-implementation evidence (protocol, documentation, a comment stating a rule, an interface or protocol-buffer contract, a test assertion, history) supports the intent.
- `impl-abstraction`: the property only describes how the prior code worked.
- `unknown`: it looks like a correctness requirement, but only implementation evidence was found.
- `model-internal`: a check about the model itself (types, observers, reachability canaries).
- `mixed`: the property's clauses have different statuses, listed in `clause` lines.
- `evidence` lines of type `impl` show what the code did, never what it should do.
- `watch` lists source locations whose change should trigger a review of the property.

## 2. How to Use Them

Where these rules and the general property rules disagree, these rules take precedence for annotated properties.

1. Read a property's block before deciding anything about that property.
2. If the update touches any `watch` location, the property is affected (Divergence Evidence §1); re-examine it against the new source and say so in its entry, even if you keep it.
3. `watch` only catches changes. When the update introduces a new kind of entry, message, state, or configuration, search the blocks and the source for every property and code site that handles the existing kinds, and decide whether the new kind must be covered. An omission does not touch any `watch` location.
4. `requirement`, or a `requirement` clause:
   - the new code is expected to obey it; do not weaken or narrow it to match the new implementation;
   - if the new source no longer satisfies it, keep it and treat the mismatch as a bug candidate (Divergence Evidence §5);
   - the exception is new non-implementation evidence in the updated source (a comment stating the rule, documentation, a contract comment, a test assertion) showing that the requirement itself changed; cite it.
5. `impl-abstraction`, or an `impl-abstraction` clause:
   - it describes old behavior; if the update changes that behavior, revise it to describe the new behavior, bounded by what the new source and its non-implementation evidence support;
   - do not keep it unchanged without the keep evidence of Divergence Evidence §7.
6. `unknown`, or an `unknown` clause: do not weaken it toward the new implementation. If the update conflicts with it, mark it `unresolved` and state what evidence would settle it.
7. `mixed`: apply rules 4–6 clause by clause.
8. The blocks can be wrong. If the evidence you find contradicts a block, say so, cite the evidence, and decide from the evidence.

## 3. Keep the Blocks Current

For every revised or added property, write an updated `REQ-EVIDENCE` block in the same format, with `verified:` set to the current revision. For a kept affected property, update `verified:` and add any new evidence. In each `spec/invariant-evidence.json` entry for an annotated property, add `ledger_status` (the status or clause statuses you relied on) and `watch_touched` (true or false).
