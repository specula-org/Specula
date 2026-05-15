# Brief Coverage Checklist

## What this is

A **gentle self-audit reminder** for the spec generation phase. Its only purpose is to help you notice if the spec you produced silently dropped something the modeling brief asked for — most commonly at the MC config level, where coverage tends to fall through the cracks.

This is **not** a grading rubric, a required artifact, or a mandatory ritual. It is a hand-rail you can reach for when finishing up the spec. The rough workflow:

1. Before locking in the final hunt cfgs, glance over brief §2 / §5 / §6.1 and sketch where each entry shows up in the spec (mentally or in scratch is fine).
2. Notice any obvious gaps — invariants defined but not enabled in any cfg, families with no hunt cfg, §6.1 findings nothing targets.
3. Either close the gap, or note honestly why it's intentionally out of scope.

If something is genuinely not worth modeling, say so plainly. The point is to avoid the silent gap, not to inflate coverage.

## A real failure mode this catches

The kind of thing easy to miss: a spec defines all the family invariants in `base.tla`, wires them through `MC.tla`, then comments them out of `MC.cfg` with a TODO ("re-enable in hunt cfgs") — and the TODO never gets done. The hunt cfgs run, but only check `MCTypeOK`. The spec spends hours of compute and could not have found any bug.

That's not lack of effort; it's just losing track of the last assembly step. Glancing at the cfg files with the brief open catches it.

## What the brief gives you

The modeling brief is the **only** source for what to cover. Do **not** consult fault-family vocabularies (in `code_analysis/references/`) when filling the audit — those exist as shorthand during brief writing, not as a required slate during spec generation. If the brief did not raise it, you do not have to cover it.

The three sections worth glancing at:

| Brief section | What it gives you | Where it should show up |
|---|---|---|
| §2 Bug Families | named families with mechanism + suggested invariants/actions | usually one `MC_hunt_<family>.cfg` per family, or an explicit merger |
| §5 Proposed Invariants | named invariants with type + targets | each Safety invariant defined, wired, and enabled in ≥1 hunt cfg |
| §6.1 Model-Checkable Findings | concrete mechanism questions with expected violated invariant | each finding has a hunt cfg whose fault setup makes the trigger reachable |

Liveness invariants and §6.2 / §6.3 findings are out of scope for this audit unless the brief says otherwise.

## What to glance at

Three loose tables — these are useful as scratch, and you can promote them to `spec/brief-coverage.md` if you want a durable artifact. The audit document is supposed to be boring; "—" rows mean go fix the spec, not fill in apologetic prose.

**Families (brief §2)** — for each named family, which hunt cfg covers it? Mergers are fine if explicit.

**Invariants (brief §5)** — for each Safety invariant: defined where, wired in MC.tla, enabled in which hunt cfg(s)? **The "enabled in cfg" column is the one that breaks most often** — fill it by reading the actual cfg files, not from memory of what you intended to write.

**Findings (brief §6.1)** — for each finding: trigger mechanism, expected violated invariant, hunt cfg targeting it. A finding with no targeting cfg won't be hunted — if you genuinely can't reach the trigger, say so plainly.

## What this checklist does NOT require

- It does **not** require covering any fault-family vocabulary. The brief is the source.
- It does **not** require a minimum number of invariants, hunt cfgs, or findings. If the brief proposed three, three is the right answer.
- It does **not** require one hunt cfg per family if mergers are honest and written down.
- It does **not** care about action granularity, instrumentation mapping, or trace spec — those have their own discussions elsewhere.

The one thing it tries to catch: the gap between *defining* coverage and *enabling* it.
