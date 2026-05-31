# Phase 2 (re-check): Resolve repair requests

This pass runs **only in re-check mode** (`--recheck`), invoked by the pipeline's repair loop after Phase 3 has attempted a scoped repair. It consumes repair requests in status `RECHECK`, decides whether the repair settled the finding, and transitions each request out of `RECHECK`. See `references/repair-request-format.md` for the artifact and state machine.

> **Hard rule: every `RECHECK` request you process MUST end this pass in `RESOLVED`, `REOPENED`, or `DEFERRED`. Never leave a request in `RECHECK`** — otherwise the next loop iteration re-checks it forever.

## Input

- `repair-requests/RR-*.md` with `status: RECHECK` — **process only these**; ignore every other status.
- The repair's outcome, appended by Phase 3 to each request's `History`.
- The updated `spec/bug-report.md` and the re-run TLC output under `spec/output/` for the request's `scope.hunt_cfgs`.
- The linked finding in `confirmed-bugs.md` (via `bug_id`).
- `--max-repair-rounds=N` (0 = unlimited): the **per-request** cap. When a request's own `round` reaches `N`, defer it rather than reopening (see step 4).

**You own every status write.** Both the request's frontmatter `status:` and the finding's entry in `confirmed-bugs.md` are updated by you, here — the orchestrator never edits `confirmed-bugs.md`. A finding that entered as `PENDING REPAIR (RR-NNN)` leaves this pass as REPRODUCED / FALSE POSITIVE / DEFERRED (or stays PENDING if the request reopens).

## Per-request procedure

For each `RECHECK` request:

1. **Read** the request (target, scope, History) and the re-run result for its hunt cfg.
2. **Compare** against the original counterexample:

   | Re-run result | Meaning | Transition |
   |---|---|---|
   | Original CE gone, no new violation on that cfg | The spec/fault/invariant error was the cause; the finding was an artifact | finding → **FALSE POSITIVE** (cite the repair as evidence); request → **RESOLVED** |
   | INVARIANT target: corrected invariant no longer flags | The property was wrong, not the code | finding → **FALSE POSITIVE** ("invariant corrected"); request → **RESOLVED** |
   | A new / different CE on that cfg | The repair surfaced an adjacent behavior | go to step 3 |
   | CE unchanged / still impossible at code level | Repair did not settle it | go to step 4 |

3. **New-CE path.** Reproduce the new CE via the Phase 2 escalation ladder (Level 0 → 3, per `02-reproduction.md`):
   - Reproduces → real adjacent bug. Update/replace the finding as **REPRODUCED**; request → **RESOLVED**.
   - Still an artifact, and you can cite a *fresh* repair (a different missing guard / fault / invariant than any in History) → request → **REOPENED** (`round++`), append the new evidence; it re-enters Phase 3.
4. **No-progress path.**
   - **Per-request cap.** If `--max-repair-rounds=N` with `N > 0` and this request's `round >= N` → **DEFERRED**, even if you could cite another repair. The cap is the hard stop on a single request's repair attempts.
   - Else if you can cite a *new* repair to try (not already in History) → **REOPENED** (`round++`).
   - Otherwise → **DEFERRED**. In both DEFERRED cases, write the deferral into the finding's `confirmed-bugs.md` entry (status `DEFERRED`, with a one-line summary of the repair history and why it could not be settled). The candidate is preserved for a developer — never dropped.

> Budget/quota is **not** a reason to defer. The orchestrator waits for quota to free up between rounds; you defer a request only on the per-request cap or a genuine no-progress verdict above.
5. **Append** a `History` entry (newest last, tagged `phase4-recheck`) and **set the new status**. Do not leave `RECHECK`.

## Anti-oscillation

Before choosing `REOPENED`, read the request's `History`. If the repair you would request is the same one a prior round already tried and it did not settle the finding, do **not** REOPEN with it — either cite a genuinely different hypothesis or **DEFER**. Repeating an identical failed repair is the loop's main failure mode.

## Batch-mode constraints

Same as the rest of bug confirmation (see `guide.md` → Batch Mode Constraints). Block in-turn on any TLC re-run or reproduction (`timeout`, `wait`, or `scripts/infra/wait_for_pid.sh`); never register a cross-turn wakeup.
