# Brief Coverage Checklist

## What this is

A **self-audit tool** for the spec generation phase. Its only job is to keep you honest about whether the spec you produced actually covers what the modeling brief asked for — specifically at the **MC config level**, where coverage gets silently dropped most often.

This is **not** a grading rubric handed to you at the end. The intended workflow is:

1. **Before** writing the final hunt cfgs: enumerate brief §2 / §5 / §6.1 entries and sketch the audit table mentally or in scratch
2. Identify gaps (invariants you defined but didn't enable; families with no hunt cfg; findings that no cfg targets)
3. **Modify the spec** — add invariants to hunt cfgs, create missing hunt cfg files, document why anything is genuinely out of scope
4. Repeat 2–3 until you can fill the table without a single empty cell
5. Only then write `spec/brief-coverage.md` as the durable artifact

If you find yourself writing "—" or "skipped" rows in `brief-coverage.md`, **go fix the spec instead**. The audit document is supposed to be boring.

## Why this checklist exists

In recent runs we observed a recurring failure mode that this checklist directly targets:

> **arc-swap case (real example)**: brief proposed 5 bug families, 10 safety invariants, 12 model-checkable findings. The spec defined all 6 family invariants in `base.tla`, wired them through `MC.tla`, then commented them out of `MC.cfg` with a note "re-enable in MC_hunt_*.cfg" — and **never re-enabled them**. All 5 generated hunt cfgs only checked `MCTypeOK`. The spec ran 30 minutes per hunt and could not have found any bug.

The agent didn't lack effort; it lost track of the last assembly step. This checklist forces that step to be visible.

## What the brief gives you

The modeling brief is the **only** source for what to cover. You do **not** consult any abstract fault-family taxonomy when filling the checklist — those taxonomies (e.g., the 8 concurrent fault families in `code_analysis/references/concurrent-analysis.md`) exist as inspiration during the *brief* writing step, not as a required slate during spec generation. If the brief did not raise it, you do not have to cover it.

Three brief sections drive the audit:

| Brief section | What it gives you | Where it must show up in the spec |
|---|---|---|
| §2 Bug Families | named families with mechanism + suggested invariants/actions | one `MC_hunt_<family>.cfg` per family (or one with documented merger) |
| §5 Proposed Invariants | named invariants with type (Safety/Liveness) + targets | each Safety invariant defined in `base.tla`, wired in `MC.tla`, **enabled in ≥1 hunt cfg** |
| §6.1 Model-Checkable Findings | concrete attack scenarios with expected violated invariant | each finding has a hunt cfg whose fault-counter setup makes the trigger reachable |

Liveness invariants and §6.2/§6.3 findings are explicitly out of scope for this audit unless the brief says otherwise.

## The three audit tables

These are the tables `spec/brief-coverage.md` must contain. Use them first as scratch during Phase 2, then promote to the final file.

### Table 1: Bug Families (from brief §2)

| Brief Family | Hunt cfg file | Family-relevant invariants enabled in that cfg | If skipped, why? |
|---|---|---|---|
| (one row per family in brief §2) | `MC_hunt_<name>.cfg` or `(merged into <other>.cfg)` | comma-separated invariant names from cfg | only filled if not covered |

**Default expectation**: one hunt cfg per family. Mergers are allowed — e.g., "Family E (Writer-scan) is the natural top-level safety property of Family A; covered by `MC_hunt_familyA.cfg` invariants" — but every such merger must be written out. **Do not silently merge.**

### Table 2: Proposed Invariants (from brief §5)

| Brief invariant | Defined at (file:line) | Wired in MC.tla? | Enabled in which hunt cfg(s)? | If skipped, why? |
|---|---|---|---|---|
| (one row per Safety invariant in brief §5) | `base.tla:NNN` | `MC<Name>` exists / no | filenames of cfg(s) | only filled if not enabled anywhere |

**The "Enabled in which hunt cfg(s)" column is the one that breaks most often.** A Safety invariant defined in `base.tla` and wired through `MC.tla` but enabled in no hunt cfg is **not** providing coverage — it is dead code.

**Fill this column by reading the actual cfg files**, not from memory of what you intended to write. The arc-swap failure was that the agent's intent (re-enable in hunt cfgs) and the actual file content (still commented out) had drifted apart.

### Table 3: Model-Checkable Findings (from brief §6.1)

| Finding ID | Trigger mechanism (action/fault) | Expected violated invariant | Hunt cfg targeting it |
|---|---|---|---|
| (one row per §6.1 entry) | the fault counter / action that opens the bug | name as it appears in the spec | filename |

**A finding with no targeting hunt cfg is a finding that won't be hunted.** If you genuinely can't reach the trigger (e.g., it requires a fault model not implemented), say so in this row — but check first whether a small `MC*` counter would expose it.

## Coverage Summary

End the document with a one-paragraph summary:

```
Families: M / N implemented + P partial (skipped: list)
Proposed Safety Invariants: M / N enabled in ≥1 hunt cfg (skipped: list with reasons)
Model-Checkable Findings: M / N targeted by a hunt cfg (skipped: list with reasons)
Hunt cfg files: count
```

## Worked failure example

What `arc-swap_2`'s brief-coverage.md *should* have looked like (if the spec had been correct):

```markdown
### Table 2: Proposed Invariants (from brief §5)
| Brief invariant | Defined at | Wired in MC.tla? | Enabled in which hunt cfg(s)? | If skipped, why? |
|---|---|---|---|---|
| NoUseAfterFree | base.tla:1108 | yes | familyA.cfg, familyB.cfg, familyC.cfg | — |
| PayAllCompleteness | base.tla:1112 | yes | familyA.cfg, familyE.cfg | — |
| NoConcurrentNodeClaim | base.tla:1142 | yes | familyD.cfg | — |
| ... | | | | |
```

What it *actually* would have been (if anyone had written it):

```markdown
| NoUseAfterFree | base.tla:1108 | yes | (none — commented out for state cost) | not justified |
| PayAllCompleteness | base.tla:1112 | yes | (none) | not justified |
| ... | | | | |
```

Filling out the table — even informally — would have made this row painful to write down without going back and fixing it. **That is the entire point of the checklist.**

## What this checklist does NOT do

- It does **not** require you to cover the 8 concurrent / 6 distributed fault families. The brief is the source.
- It does **not** require a minimum number of invariants. If the brief proposed 3, three is the right answer.
- It does **not** require one hunt cfg per family if mergers are honest and explicit.
- It does **not** care about action granularity, instrumentation mapping, or trace spec — those are audited by other rules in the main `guide.md`.

It does one thing: catches the gap between *defining* coverage and *enabling* coverage.
