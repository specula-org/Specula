# Brief Coverage Checklist

## What this is

A self-audit aid for the spec generation phase. Check whether the spec preserves the requested scope and modeling handoff, including baseline behavior, component interactions, and properties enabled in MC configs.

The tables below are optional ways to prepare the required `brief-coverage.md` output. The workflow:

1. Review the scope guidance, baseline modeling recommendations, linked modeling documents, and brief §2 / §5 / §6.1; map them to the spec and checking configs.
2. Notice any obvious gaps — invariants defined but not enabled in any cfg, Scenarios with no hunt cfg, §6.1 findings nothing targets.
3. Either close the gap, or note honestly why it's intentionally out of scope.

If something is genuinely not worth modeling, say so plainly. The point is to avoid the silent gap, not to inflate coverage.

## A real failure mode this catches

The kind of thing easy to miss: a spec defines all the Scenario invariants in `base.tla`, wires them through `MC.tla`, then comments them out of `MC.cfg` with a TODO ("re-enable in hunt cfgs") — and the TODO never gets done. The hunt cfgs run, but only check `MCTypeOK`. The spec spends hours of compute and could not have found any bug.

That's not lack of effort; it's just losing track of the last assembly step. Glancing at the cfg files with the brief open catches it.

## What the brief gives you

Use the requested scope, the modeling brief and its linked documents, and relevant implementation evidence. If the brief omitted a requested behavior or source reading reveals an in-scope interaction, account for it in the handoff and audit. Fault-category vocabularies can help identify questions, but are not a required slate for every system.

Useful mappings:

| Brief section | What it gives you | Where it should show up |
|---|---|---|
| Scope guidance and §1 / §3 baseline behavior | components, contracts, configuration, and lifecycle interactions | corresponding state/actions and source mappings, with abstractions and unresolved coverage explained |
| §2 Scenarios | named Scenarios with mechanism + suggested invariants/actions | usually one `MC_hunt_<scenario>.cfg` per Scenario, or an explicit merger |
| §5 Proposed Invariants | named invariants with type + targets | each Safety invariant defined, wired, and enabled in ≥1 hunt cfg |
| §6.1 Model-Checkable Findings | concrete mechanism questions with expected violated invariant | each finding has a hunt cfg whose fault setup makes the trigger reachable |

Liveness invariants and §6.2 / §6.3 findings are out of scope for this audit unless the brief says otherwise.

## What to glance at

The following tables can support `spec/brief-coverage.md`; include the baseline and scope mapping above as well. Missing entries identify work to complete or a coverage limitation to explain.

**Scenarios (brief §2)** — for each named Scenario, which hunt cfg covers it? Mergers are fine if explicit.

**Invariants (brief §5)** — for each Safety invariant: defined where, wired in MC.tla, enabled in which hunt cfg(s)? **The "enabled in cfg" column is the one that breaks most often** — fill it by reading the actual cfg files, not from memory of what you intended to write.

**Findings (brief §6.1)** — for each finding: trigger mechanism, expected violated invariant, hunt cfg targeting it. A finding with no targeting cfg won't be hunted — if you genuinely can't reach the trigger, say so plainly.

## What this checklist does NOT require

- It does **not** require covering every fault-category vocabulary entry. The requested scope and implementation determine relevance.
- It does **not** impose a minimum or maximum number of invariants, hunt cfgs, or findings. Determine sufficiency from the requested behavior, contracts, and unresolved questions.
- It does **not** require one hunt cfg per Scenario if mergers are honest and written down.
- It does **not** care about action granularity, instrumentation mapping, or trace spec — those have their own discussions elsewhere.

The one thing it tries to catch: the gap between *defining* coverage and *enabling* it.
