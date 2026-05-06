# Writing `.prompt-extra.md`

Read this when the user asks you to set up Specula for a new target, or to write/revise a `.prompt-extra.md` for them.

## What this file is

`.prompt-extra.md` is an optional per-target file that every Specula phase launcher (`launch_code_analysis.sh`, `launch_spec_generation.sh`, `launch_harness_generation.sh`, `launch_spec_validation.sh`, `launch_bug_confirmation.sh`) appends to its agent prompt under a `## Target-Specific Instructions` heading. It lives at:

- `.prompt-extra.md` in the directory the user launches the pipeline from, OR
- `.specula-output/.prompt-extra.md` (used when scripted launchers create per-target work directories — checked second).

Every phase agent reads the same file, so phase-specific instructions need to be marked (e.g., `### Phase 4 only`).

## When to write one

Write a `.prompt-extra.md` only if at least one of these is true:

- The user has hypotheses about specific bug families they want investigated.
- There are known production incidents or upstream issues that phase agents should be aware of.
- Default phase behavior would over-scope (e.g., target is 500K LOC and only one subsystem matters).
- The user wants to gate scope explicitly (e.g., "skip transport, model only session lifecycle").

If none of these apply, tell the user `.prompt-extra.md` is unnecessary for their target — Phase 1 (code_analysis) will produce the modeling brief on its own. Don't write a generic `.prompt-extra.md` just to have one; an over-scoped or boilerplate file degrades phase agents' decisions instead of improving them.

## Hard rules (do not violate)

1. **State WHAT to verify, not HOW to model it.** Phase 2 (spec_generation) decides modeling abstractions. If you pre-specify abstractions, the spec agent copies your wording instead of reading the code, and you get worse specs.

2. **Phrase hypotheses as questions.** "Does the receiver enforce that each chunk index appears exactly once?" — yes. "Define invariant `NoDuplicateChunk` requiring …" — no.

3. **Cite real `file:line` whenever possible.** "Race in `fdborch.cpp` LAG transition path" beats "race somewhere in fdborch".

4. **Keep it under ~60 lines.** If your draft is longer, you are over-specifying. The strongest examples in `case-studies/` are 20–60 lines.

5. **Don't repeat what Phase 1 will discover.** `.prompt-extra.md` is for context Phase 1 *cannot* derive from the code alone (production incident reports, upstream maintainer's stated trade-offs, the user's specific hypotheses). It is not a place to summarize the codebase.

## Keep / Remove

| Keep | Remove |
|------|--------|
| Subsystem scope ("focus on chunking layer, not transport") | TLA+ variable names, types, operators (`Seq(Nat)`, etc.) |
| Bug-family hypotheses, phrased as questions | Pre-defined invariants with formal conditions |
| Key files / entry points (cite paths) | Action structure ("split `Receive` into `ReceiveStart` / `ReceiveEnd`") |
| Known historical bugs / incidents (issue links + brief mechanism) | State-space bounds (`Server = {s1, s2, s3}`, `MaxTerm = 5`) |
| Out-of-scope list (what to skip and why) | Symmetry / fairness annotations |
| Reference paper, RFC, or design doc citations | Specific TLC config flags |

Self-test before writing: would your draft still make sense if Specula switched its modeling language tomorrow? If "no" because you mentioned `Seq(...)` or named a TLA+ operator, that part is HOW, not WHAT — remove it.

## Read these examples before drafting

Pick the closest in style to the user's target and read it in full:

- `case-studies/sonic-fdb/.prompt-extra.md` — full distributed-system scope brief: architecture sketch + production incident + key files + 5 hypothesized bug families.
- `case-studies/eliben-raft/.prompt-extra.md` — minimal: protocol focus + 8 bug patterns to hunt for. No abstractions specified.
- `case-studies/libspdm-chunking/.prompt-extra.md` — pure-WHAT writing: every hypothesis is phrased as a question.
- `case-studies/mongodb-chunkmigration/.prompt-extra.md` — Phase 4-specific re-run instructions for already-found bugs.

If your draft strays from the style of these, revise.

## Recommended structure

There is no required template. Most working `.prompt-extra.md` files contain some subset of:

1. **One-line system summary** — language, GitHub URL, system category (A: distributed / B: concurrent), reference paper if any.
2. **Architecture sketch** — the 2–5 components that interact, in plain English.
3. **Key files** — paths phase agents should read first.
4. **Known production incidents / bug references** — issue numbers + brief mechanism, with links.
5. **Bug-family hypotheses** — open questions phrased as questions.
6. **Out of scope** — what to skip and why.
7. **Phase-specific sections** (optional) — `### Phase 4 only` etc.

Choose the subset the target actually needs. A target with no production incidents should not have a "Known incidents" section padded with non-incidents.

## Procedure

1. **Confirm with the user**: target system, system category (A or B), specific hypotheses they want investigated. If they have no hypotheses, ask whether to skip `.prompt-extra.md` entirely.
2. **Read the closest example** from the list above and match its style.
3. **Read enough of the target source** to cite real file paths. If there's a GitHub repo, run `gh issue list` with relevant keywords to surface production incidents the user may not have mentioned.
4. **Draft** using the structure above and the hard rules. Aim for under 60 lines.
5. **Show the draft to the user before writing the file.** Highlight which sections you included and why, and call out any sections you considered including but dropped (e.g., "I skipped Out-of-Scope because the target is small enough that scoping isn't a concern").
6. **Write to** `.prompt-extra.md` (or `.specula-output/.prompt-extra.md` if the user is using scripted launchers with a work directory).

## Anti-patterns

If your draft contains any of these, fix it before showing the user:

- TLA+ variable names, types, or operators.
- Pre-defined invariant names with formal conditions ("Define `SafetyInv == ...`").
- State-space bounds chosen by you instead of by the spec generation agent.
- Hypotheses phrased as statements ("the system has a race in X") instead of questions ("can a race in X cause Y?").
- Restating what's obvious from the README or top-level source files.
- Generic boilerplate that would apply to any target ("focus on correctness", "model the protocol carefully").
- A long "background" section explaining the protocol that any phase agent could derive from the source.

## When the user pushes back

If the user provides text they want included that violates the hard rules (e.g., they want to specify variable names), explain the trade-off briefly and ask before including it. Their `.prompt-extra.md`, their call — but the consequences are theirs to weigh, not yours to silently absorb.
