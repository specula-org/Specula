# Skill overlays for the inv-e2e arms

Each arm is the base `incremental-modeling` skill plus the files and hook lines below. `../build_skills.py` builds every arm from a base commit with `git archive` and fails unless each hook anchor in `hooks.json` matches exactly one line.

| Arm | Overlay |
|---|---|
| v0 | none |
| v1 | `v1/references/generation/divergence-evidence.md` + 5 v1 hooks |
| v2 | v1 + `v2/references/generation/ledger-usage.md` + 2 v2 hooks |

## `divergence-evidence.md` (v1, v2)

Rules for every property decision the update affects, adapted from the A2/A3 prompts of `../../etcd-v0-v3/inv-ablation/`:

- Every affected property gets a decision: keep, modify, add, remove or unresolved. The initial decision is recorded before any code observation.
- A weakening needs a state that the new model reaches, on which the old property is false and the new one true. A strengthening needs a state that the old model reaches, on which the old property is true and the new one false. Keeping an affected property also needs evidence.
- TLC evaluates the actual definitions on that state. The evidence must be non-vacuous and comes with a control.
- Two questions are answered separately: does the implementation produce the state, and does the requirement allow it. A state the implementation produces but the requirement forbids is a bug candidate, not a reason to change the property.
- Everything is recorded in `spec/invariant-evidence.json`.

## `ledger-usage.md` (v2)

How to read and maintain the `REQ-EVIDENCE` blocks that `../annotate.py` adds to the prior spec:

- the block format and statuses;
- what a status implies for a decision, for example that a `requirement` clause is not weakened without non-implementation evidence;
- a property is affected when the update touches any of its `watch` locations;
- an omission touches no `watch` location: when the update adds a new kind of entry, message, state or configuration, search for every property and code site that handles the existing kinds;
- keeping blocks current for added or modified properties;
- recording `ledger_status` and `watch_touched` in `invariant-evidence.json`.

## Hooks

v1 hooks: one line each, in `guide.md` (Part 1, after item 3), `03-update-focused-analysis.md` (§3), `04-update-model-generation.md` (§5), `05-completeness-review.md` (§3, new bullet), and `validation/02-update-focused-scenarios.md` (end). v2 adds two lines, in `guide.md` and `03-update-focused-analysis.md`. The exact text and anchor of every line are in `hooks.json`.
