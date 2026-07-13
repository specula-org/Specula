# Repair-Request Format

A **repair request** carries a confirmation-loop back-edge. When reproduction concludes — *with a citation* — that a counterexample is a spec / fault-model / invariant **artifact** rather than a real triggerable bug, the finding is not dropped: it is handed back to Phase 3 (spec validation) for a scoped repair. Phase 3 fixes the spec and **re-runs model checking**; the fresh output is then re-confirmed by a normal pass of the confirmation skill — **there is no separate re-check pass**. This file defines the artifact and the small state machine that keeps the loop **bounded** and **idempotent**.

- **Drafted by**: Phase 2 reproduction — see `phases/02-reproduction.md`.
- **Validated and published by**: the invoking dispatcher / legacy outer orchestrator, which is the sole allocator and shared-queue writer.
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

One file per request. `id` is `RR-NNN`, zero-padded. Only the dispatcher allocates it: scan active and `deferred/` `RR-*.md` files and take max + 1. Per-finding workers must not inspect or write this shared directory. Never reuse or renumber terminal ids. Every final file MUST carry the candidate's stable `finding_id`; all reuse and lifecycle decisions use that field. `bug_id: Bug N` is only a mutable report/display label and is never identity. The per-request frontmatter is always the source of truth; a `DEFERRED` request lives under `repair-requests/deferred/`. `repair-ledger.md` is a derived rollup and is owned by the pipeline orchestrator, not by this skill.

## Finding-local semantic draft

For `PENDING REPAIR`, the per-finding worker writes the caller-supplied `repair-request.body.md`. It contains only the semantic fields `target`, `counterexample`, and `scope`, followed by non-empty `## Trigger` and cited `## Evidence` sections (and optional `## Proposed change`). All four scope lists (`actions`, `invariants`, `hunt_cfgs`, `fault_actions`) must be present; `hunt_cfgs` and the list corresponding to `target` must be non-empty.

The draft MUST NOT contain `id`, `bug_id`, `finding_id`, `allocation_key`, `status`, `round`, or `## History`. Those fields, the final `RR-NNN.md` path, and `confirmed-bugs.md` are dispatcher-owned. A missing or malformed draft makes the finding `INCOMPLETE`; it must never create an empty OPEN request.

Use this exact shape (no inline YAML comments):

```markdown
---
target: SPEC_REPAIR
counterexample: output/MC_hunt_log_div_20260531.out
scope:
  actions: [HandleAppendEntries]
  invariants: [LogMatching]
  hunt_cfgs: [MC_hunt_log_div.cfg]
  fault_actions: []
---

## Trigger
The counterexample requires a transition the implementation rejects.

## Evidence
The missing implementation guard is at src/node.py:42.

## Proposed change
Add the guard to the modeled action.
```

## Final file schema (dispatcher output)

Markdown with a YAML frontmatter header (machine-routable by the orchestrator) and an evidence body (read by the repair agent).

```markdown
---
id: RR-001
finding_id: MC-1              # immutable candidate identity; never derive from Bug N
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
- r0 (phase4-confirm): created from MC-1
- r0 (phase4-confirm): prior attempt RR-003 (CONSUMED): r1 (phase3-repair): <what it changed and the re-run result>
```

When the finding already has terminal (`CONSUMED` / `DEFERRED`) requests, the dispatcher seeds the fresh request's History with one `prior attempt` bullet per terminal record, quoting that record's newest History line. This is the cross-round memory: the repair agent starts from what earlier rounds already tried.

## State machine

Small. Terminal states: `CONSUMED` (Phase 3 completed the scoped repair) and `DEFERRED` (the orchestrator exhausted the global loop cap).

| Transition | Owner | When |
|---|---|---|
| (new) → `OPEN` | confirmation dispatcher | validates a finding-local draft after reproduction yields a **cited** artifact verdict |
| `OPEN` → `IN_REPAIR` | Phase 3 repair | on entry, before editing the spec |
| `IN_REPAIR` → `CONSUMED` | Phase 3 repair | after editing + **full trace re-validation** + re-running MC; appends History |
| `OPEN` → `DEFERRED` | pipeline orchestrator | the global repair-loop round cap is reached; move the file under `repair-requests/deferred/` and update the linked report entry |

Whether a `CONSUMED` repair actually **settled** the finding is answered by the next Phase 4 confirmation on the fresh bug-report: a repaired artifact simply no longer appears (resolved); a surviving or new violation is confirmed from scratch and may emit a fresh `OPEN` request, whose History is seeded with one `prior attempt` bullet per terminal record for the same finding. There is no re-check pass and no `RESOLVED` / `REOPENED` status. `DEFERRED` is legal only as the orchestrator-owned terminal state; an agent never emits it as a verdict or writes that transition.

`IN_REPAIR` doubles as a crash marker: if the orchestrator finds a request still `IN_REPAIR` at the top of a loop iteration (its repair phase died mid-turn), it resets it to `OPEN`.

If a new validated draft arrives for the same finding while its request is still `OPEN`, the dispatcher reuses that id and atomically refreshes the semantic payload while preserving `status`, `round`, and History. A `finding_id` may have at most one active (`OPEN` or `IN_REPAIR`) request; multiple terminal audit records are allowed. It never rewrites `IN_REPAIR`. `CONSUMED` and `DEFERRED` are immutable audit records: a later, different allocation receives a new `OPEN` id; an exact retry may only point back to the unchanged `DEFERRED` record.

Identity is always `finding_id`, never `bug_id`. Candidate order may change
between confirmations, so the dispatcher refreshes a stale display-only `bug_id`
without changing request identity. When importing an older request that lacks
`finding_id`, migration is allowed only if the prior canonical report uniquely
links the RR id and its `Bug N` row to the same explicit Finding ID; otherwise
the dispatcher fails closed and must not create a possible duplicate request.

### Termination — the orchestrator's job, not an agent's

The loop is bounded by a **global round cap** (`--max-repair-rounds=N`, default `10`; `0` = unlimited), enforced by the orchestrator. When the cap is reached with requests still `OPEN`, the orchestrator changes each request to `status: DEFERRED`, moves it to `repair-requests/deferred/`, and marks the linked finding `DEFERRED` in `confirmed-bugs.md`. `DEFERRED` therefore means only "the repair loop ran out of rounds" — never an agent verdict. Budget pressure does **not** defer anything: the orchestrator waits for quota between rounds like every other phase.

## Repairing a request (Phase 3 repair mode)

Phase 3 in repair mode (`--repair`) processes each request with status `OPEN`:

1. Set `status: IN_REPAIR` before editing anything.
2. Read its Trigger / Evidence and its `History`. If History cites `prior attempt RR-NNN` bullets, read those request files too — they are this finding's earlier rounds. Never repeat a repair a prior round already tried and recorded as failed.
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
