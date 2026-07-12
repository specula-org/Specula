# Repair-Request Format

A **repair request** carries a confirmation-loop back-edge. When reproduction concludes — *with a citation* — that a counterexample is a spec / fault-model / invariant **artifact** rather than a real triggerable bug, the finding is not dropped: it is handed back to Phase 3 (spec validation) for a scoped repair. Phase 3 fixes the spec and **re-runs model checking**; the fresh output is then re-confirmed by a normal pass of the confirmation skill — **there is no separate re-check pass**. This file defines the artifact and the small state machine that keeps the loop **bounded** and **idempotent**.

- **Produced by**: Phase 2 reproduction — see `phases/02-reproduction.md`.
- **Consumed by**: Phase 3 spec validation in repair mode (`--repair`), which repairs the spec, re-runs MC, and marks the request `CONSUMED`.

## Location

```
.specula-output/<name>/spec/
├── repair-requests/
│   ├── RR-001.md
│   ├── RR-002.md
│   └── deferred/
│       └── RR-003.md
└── repair-ledger.md      # rollup index; maintained by the orchestrator (pipeline)
```

One file per request. `id` is `RR-NNN`, zero-padded. To allocate a new id, scan active and `deferred/` `RR-*.md` files and take max + 1. Never reuse or renumber ids. The per-request frontmatter is always the source of truth; a `DEFERRED` request lives under `repair-requests/deferred/`. `repair-ledger.md` is a derived rollup and is owned by the pipeline orchestrator, not by this skill.

## File schema

Markdown with a YAML frontmatter header (machine-routable by the orchestrator) and an evidence body (read by the repair agent).

```markdown
---
id: RR-001
bug_id: <heading/label of the finding's entry in confirmed-bugs.md>
target: SPEC_REPAIR            # SPEC_REPAIR | FAULT_MODEL | INVARIANT
status: OPEN                   # OPEN | IN_REPAIR | CONSUMED | DEFERRED
round: 0                       # times Phase 3 has repaired this request
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

Small. Terminal states: `CONSUMED` (Phase 3 completed the scoped repair) and `DEFERRED` (the orchestrator exhausted the global loop cap).

| Transition | Owner | When |
|---|---|---|
| (new) → `OPEN` | Phase 2 confirm | reproduction yields a **cited** artifact verdict |
| `OPEN` → `IN_REPAIR` | Phase 3 repair | on entry, before editing the spec |
| `IN_REPAIR` → `CONSUMED` | Phase 3 repair | after editing + **full trace re-validation** + re-running MC; appends History |
| `OPEN` → `DEFERRED` | pipeline orchestrator | the global repair-loop round cap is reached; move the file under `repair-requests/deferred/` and update the linked report entry |

Whether a `CONSUMED` repair actually **settled** the finding is answered by the next Phase 4 confirmation on the fresh bug-report: a repaired artifact simply no longer appears (resolved); a surviving or new violation is confirmed from scratch and may emit a fresh `OPEN` request. There is no re-check pass and no `RESOLVED` / `REOPENED` status. `DEFERRED` is legal only as the orchestrator-owned terminal state; an agent never emits it as a verdict or writes that transition.

`IN_REPAIR` doubles as a crash marker: if the orchestrator finds a request still `IN_REPAIR` at the top of a loop iteration (its repair phase died mid-turn), it resets it to `OPEN`.

### Termination — the orchestrator's job, not an agent's

The loop is bounded by a **global round cap** (`--max-repair-rounds=N`, default `10`; `0` = unlimited), enforced by the orchestrator. When the cap is reached with requests still `OPEN`, the orchestrator changes each request to `status: DEFERRED`, moves it to `repair-requests/deferred/`, and marks the linked finding `DEFERRED` in `confirmed-bugs.md`. `DEFERRED` therefore means only "the repair loop ran out of rounds" — never an agent verdict. Budget pressure does **not** defer anything: the orchestrator waits for quota between rounds like every other phase.

## Repairing a request (Phase 3 repair mode)

Phase 3 in repair mode (`--repair`) processes each request with status `OPEN`:

1. Set `status: IN_REPAIR` before editing anything.
2. Read its Trigger / Evidence and its `History` — never repeat a repair a prior round already tried and recorded as failed.
3. Apply the repair for its `target`:
   - **SPEC_REPAIR** — tighten the cited action / add the missing guard in `base.tla` so the model matches the implementation at the cited `file:line`.
   - **FAULT_MODEL** — correct the fault model as a whole: the fault action's semantics in `base.tla`, its counter/wrapper in `MC.tla`, the cfg constants, or removing a fault that is not in the system's failure model. Not just `MC.cfg` bounds.
   - **INVARIANT** — weaken / correct the cited invariant per the evidence.
4. Re-validate (follow the validation-workflow skill):
   - Run **full trace validation on all traces** — the soundness gate. If the repair excludes a real trace, it is wrong; undo it and reconsider.
   - Re-run model checking on the request's `scope.hunt_cfgs`, and update `bug-report.md` for the affected cfg.
5. Set `status: CONSUMED` and append a `History` entry (tag `phase3-repair`) describing what changed and the re-run result (original CE gone / new CE / unchanged).

Process **only** active `OPEN` requests here; never touch `CONSUMED` or `DEFERRED`. The implementation is ground truth — do not overfit the spec to make a trace pass (model checking catches overfit repairs; see the validation-workflow skill). Do not edit `confirmed-bugs.md` in repair mode — the next Phase 4 confirmation pass owns it.

## When NOT to create a request

A request is a **positive, cited claim** that the counterexample is an artifact. Do **not** create one when:

- The bug reproduced — it's real; report it.
- Reproduction failed but you believe the bug is real-but-hard-to-trigger (timing-sensitive, needs a topology or fault the harness lacks). That is `ENV_LIMITED`; there is nothing to repair. A failed reproduction is not, by itself, evidence of a spec defect.
- You cannot cite the missing guard / inadmissible fault / unpromised property. Without a citation, fall back to a terminal defer (`NEEDS MORE INFO`); do not send Phase 3 on a fishing expedition.
