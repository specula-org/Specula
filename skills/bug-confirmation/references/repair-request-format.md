# Repair-Request Format

A **repair request** carries a confirmation-loop back-edge. When reproduction concludes — *with a citation* — that a counterexample is a spec / fault-model / invariant **artifact** rather than a real triggerable bug, the finding is not dropped: it is handed back to Phase 3 (spec validation) for a scoped repair, then returned here for re-check. This file defines the artifact and the state machine that keeps the loop **bounded** and **idempotent**.

- **Produced by**: Phase 2 reproduction, first pass — see `phases/02-reproduction.md`.
- **Consumed by**: Phase 3 spec validation in repair mode (`--repair=`), and this skill's re-check pass (`--recheck`) — see `phases/03-recheck.md`.

## Location

```
.specula-output/<name>/spec/
├── repair-requests/
│   ├── RR-001.md
│   └── RR-002.md
└── repair-ledger.md      # rollup index; maintained by the orchestrator (pipeline)
```

One file per request. `id` is `RR-NNN`, zero-padded. To allocate a new id, scan existing `RR-*.md` and take max + 1. Never reuse or renumber ids. The per-request frontmatter is always the source of truth; `repair-ledger.md` is a derived rollup and is owned by the pipeline orchestrator, not by this skill.

## File schema

Markdown with a YAML frontmatter header (machine-routable by the orchestrator) and an evidence body (read by the repair agent).

```markdown
---
id: RR-001
bug_id: <heading/label of the finding's entry in confirmed-bugs.md>
target: SPEC_REPAIR            # SPEC_REPAIR | FAULT_MODEL | INVARIANT
status: OPEN                   # OPEN | IN_REPAIR | RECHECK | REOPENED | RESOLVED | DEFERRED
round: 0                       # times this request has entered repair; ++ on each REOPENED
counterexample: output/MC_hunt_log_div_20260531.out
scope:                         # hint to the repair agent; not a hard constraint
  actions: [HandleAppendEntries]
  invariants: [LogMatching]
  hunt_cfgs: [MC_hunt_log_div.cfg]
  fault_actions: []
---

## Trigger
One line: why this counterexample is judged an artifact, naming the target category.

## Evidence  (REQUIRED — no request without a citation)
- The exact CE step that cannot be reproduced / has no consequence.
- Predicted state (from the CE) vs realized state (from the repro run).
- The code citation that grounds the judgment:
  - SPEC_REPAIR  -> the guard/branch the model is missing (file:line)
  - FAULT_MODEL  -> evidence the injected fault is outside the failure model,
                    or is modeled with the wrong semantics (file:line / issue / doc)
  - INVARIANT    -> developer-intent evidence that the implementation does not
                    promise the violated property (commit / comment / issue / test)

## Proposed change  (optional, advisory)
What the repair agent might do. The agent decides; this is a hint, not an order.

## History  (append-only; one entry per round, newest last)
- r0 (phase4-confirm): created. <verdict summary>
```

## State machine

Terminal: `RESOLVED`, `DEFERRED`. All others are non-terminal.

| Transition | Owner | When |
|---|---|---|
| (new) → `OPEN` | Phase 2 confirm (first pass) | reproduction yields a **cited** artifact verdict |
| `OPEN`/`REOPENED` → `IN_REPAIR` | Phase 3 repair | on entry, before editing the spec |
| `IN_REPAIR` → `RECHECK` | Phase 3 repair | after editing + **full trace re-validation** + scoped MC; appends History |
| `RECHECK` → `RESOLVED`/`REOPENED`/`DEFERRED` | Phase 2 re-check | exactly one; **never leaves `RECHECK`**; appends History; `round++` only on `REOPENED` |

`DEFERRED` is written **only** by the re-check agent, per finding, with evidence — on a genuine no-progress verdict or when the per-request `--max-repair-rounds` cap is reached. The orchestrator never sets `DEFERRED` and never edits `confirmed-bugs.md`. (It may flip a crashed `IN_REPAIR` back to `OPEN` for retry; that is lifecycle bookkeeping, not a verdict.)

### Idempotency rule (critical)

Each phase consumes requests in exactly **one** input status and **must** move them out of that status before its turn ends.

- Phase 2 re-check processes **only** `RECHECK` and always transitions them — a request it just rechecked cannot be re-rechecked next round.
- Phase 3 repair processes **only** `OPEN` / `REOPENED`.
- `RESOLVED` / `DEFERRED` are never touched again.

`IN_REPAIR` and `RECHECK` double as crash markers: if the orchestrator finds a request still `IN_REPAIR` at the top of a loop iteration (its repair phase died mid-turn), it resets it to `OPEN`.

### Termination

No fixed iteration cap by default. The loop terminates when **every request is terminal** (`RESOLVED` / `DEFERRED`). Progress toward termination comes from:

1. **The re-check agent**, which each round either resolves a request or — when it cannot cite a further repair — defers it (`phases/03-recheck.md`).
2. **The per-request cap** `--max-repair-rounds=N` (default `0` = unlimited): when a request's own `round` reaches `N`, the re-check agent defers it instead of reopening.
3. **Anti-oscillation**: `round` and `History` stop the agent re-requesting a repair already tried and failed.

Budget pressure does **not** defer anything. The orchestrator waits for quota between rounds (like every other phase) rather than dumping work to `DEFERRED` — mass-deferring under throttling would be an exploitable weakness.

## When NOT to create a request

A request is a **positive, cited claim** that the counterexample is an artifact. Do **not** create one when:

- The bug reproduced — it's real; report it.
- Reproduction failed but you believe the bug is real-but-hard-to-trigger (timing-sensitive, needs a topology or fault the harness lacks). That stays `REPRODUCTION FAILED`; there is nothing to repair. A failed reproduction is not, by itself, evidence of a spec defect.
- You cannot cite the missing guard / inadmissible fault / unpromised property. Without a citation, fall back to a terminal defer (`NEEDS MORE INFO`); do not send Phase 3 on a fishing expedition.
