# Parallel Per-Finding Confirmation (with an optional Reproducer ⇄ Challenger debate)

Used when the bug-confirmation dispatcher processes findings **one per work item,
in parallel** (`scripts/exp/parallel_confirm.py`), instead of one agent
consolidating all findings. Two layers: **concurrency is always on** (one
Reproducer per finding); the **debate is opt-in** (`--debate`) — without it the
Reproducer's verdict is final. This document does not replace `../guide.md` or the
phase docs — it defines the two roles and the debate that decides a *confirmed*
finding when the debate is enabled. Read `../guide.md`,
`phases/01-investigation.md`, and `phases/02-reproduction.md` first; every rule
there still applies **unchanged**.

**No new statuses, no new interfaces.** This mechanism only changes *how* a
finding's verdict is decided; the verdict is always one of the framework's
existing outcomes (see "Final verdict" below). A missing consensus is
`NEEDS MORE INFO`, not a new state.

**Step 0 already ran.** The single-agent phase consolidates the two finding
sources ("Consolidate the two finding sources into one candidate list") in its
own context. The dispatcher lifts that into an explicit step 0
(`scripts/exp/consolidate_findings.py`) that merges model-checking findings
(`bug-report.md` / `findings.json`) with code-review families
(`modeling-brief.md`) and **dedups** them — a code-review family already covered
by an MC counterexample is merged into the MC candidate (which wins), so the same
bug is not debated twice. You therefore own exactly one *already-deduped*
candidate; do not go looking for its duplicate in the other source.

## The two roles

### Agent A — Reproducer (neutral)

A runs the **existing** confirmation flow for its one finding, exactly as the
single-agent phase does: investigation (`01-investigation.md`) → reproduction
(`02-reproduction.md`), producing a `repro/test_bug<id>_*` file that was actually
executed, and a candidate verdict.

A's stance is **neutral, even charitable**: give the finding its best honest
shot. Do **not** carry a refute-it bias into reproduction — that is what loses
real bugs. If the finding is real, your job is to make it manifest.

A stops here and no debate opens when its candidate verdict is already
"not a real bug": `FALSE POSITIVE`, `DROPPED`, or a cited spec-artifact
repair request (`PENDING REPAIR`). Debate exists to challenge *confirmations*,
not dismissals.

### Agent B — Challenger (adversarial)

B opens **only when A's candidate verdict asserts a real bug** (`REPRODUCED`, or
`REPRODUCTION FAILED` that A still believes is real). B's standing goal:
**remove every finding that is not a genuine, real-world-triggerable bug.** The
burden is on the finding to survive B.

**B cannot remove a finding on its own.** A finding is only downgraded when **A
agrees** — consensus requires A's and B's `VERDICT:` lines to match (the
dispatcher checks this). B's aggressive stance is therefore bounded: it must
*convince A with cited evidence*, not merely assert. This is the safeguard
against B over-killing real bugs — an unconvinced A holds, and the finding
stands. B never gets to unilaterally rule a finding out.

B is **not** a code-reading desk reviewer. B actively attacks the reproduction
and may demand concrete changes to it. B's toolkit — all grounded in
`02-reproduction.md`'s existing rules:

1. **Is the repro legitimate?** Check A's `repro/` test against
   `02-reproduction.md` "Prohibited approaches": does it pre-populate illegal
   state, call private/internal functions directly, hand-craft inputs that
   normal flows could never produce, or modify core logic to manufacture the
   bug? If so, the reproduction is invalid — demand A redo it through public
   entry points, or the "bug" is an artifact of an illegitimate test.
2. **Does it trigger the RIGHT bug?** Per `02-reproduction.md` "Verify you
   triggered the RIGHT bug": same action sequence as the counterexample, same
   violated invariant, same root-cause code path. A repro that trips a
   *different* fault does not confirm this finding.
3. **Path vs. harm.** Does the repro show observable anomalous behavior (crash,
   deadlock, data inconsistency, safety violation) — or just an intermediate
   variable with an unexpected value? The latter is not a bug.
4. **Improve, don't only reject.** When the repro is weak but the bug may be
   real, B says *how* to strengthen it: which public API to drive instead, which
   escalation level (0→3) is warranted, where a race window should be widened
   with a documented delay rather than a logic edit. B pushing A to a *better*
   repro is a valid, wanted outcome — it produces stronger evidence, not a lost
   bug.
5. **Already known / precedent / spec artifact?** Apply the guide's
   code-review × known pre-filter, and re-check the precedent's prerequisites
   at this site (`01-investigation.md` Step 3). If the counterexample is a
   *cited* spec/fault/invariant artifact, the outcome is a **repair request**,
   not `FALSE POSITIVE` (see `02-reproduction.md` "When a counterexample is an
   artifact"). Do **NOT** conduct fresh developer-intent research (git blame,
   issue-tracker archaeology): A already did that in turn 1 (its `## Developer
   intent`). Rely on what is on the record — do not re-litigate it in a debate
   turn.

B must ground every objection in a citation (a prohibited-approach clause, a
`file:line` safeguard, a developer-intent source **already on the record from A's
turn-1 investigation**, a failed prerequisite). "I'm not convinced" is not an
objection — see the anti-sycophancy rule below.

## The debate (dispatcher-orchestrated)

The dispatcher (plain code, not an agent) plays the group-chat manager. It owns a
shared transcript `debate.md` in the finding's work dir, the turn order, and the
round cap. Neither agent messages the other directly; each turn is a fresh
invocation reading `debate.md` and appending to it.

```
Turn 1   A: investigation + reproduction + candidate verdict.
         A's verdict is a real bug?  no  → done (no debate); verdict stands.
                                     yes → open B.

Round 1..≤5   (each round = B once, then A once; both append to debate.md)
   B: strongest cited objection or concrete repro-improvement demand.
      Ends its turn with a line:  VERDICT: <one of the final-verdict values>
   A: responds with evidence — concede if B's citation actually refutes,
      rebut with counter-evidence otherwise, or produce the improved repro
      B demanded and re-run it.
      Ends its turn with a line:  VERDICT: <one of the final-verdict values>
   Dispatcher: A's and B's VERDICT lines identical this round? → CONSENSUS, stop.
                                                        else    → next round.

After 5 rounds without matching VERDICT lines → NEEDS MORE INFO.
```

### Anti-sycophancy (both agents)

Convergence must come from evidence, not politeness — the known failure mode of
debate is one party caving to end it.

- **B**: do not withdraw an objection unless A's evidence actually refutes it
  with a citation. Do not invent objections you cannot cite, either — your job is
  to remove non-bugs, which includes conceding a bug that genuinely survives.
- **A**: do not change your verdict just to reach agreement. Move only when B
  produces a real reason (a cited safeguard, a prohibited-approach violation in
  your test, a documented intent). If B is wrong, hold and show why.

Facts decide. If the finding is a real, legitimately-reproducible bug, the
correct consensus is that it stands; if it is not, the correct consensus is that
it is removed. Either is a success.

## Final verdict — the framework's existing statuses only

The consensus verdict (or A's solo verdict when no debate opened) is written to
`verdict.md` using the guide's per-bug schema, status ∈ exactly:

`REPRODUCED` · `REPRODUCTION FAILED` · `FALSE POSITIVE` · `NEEDS MORE INFO` ·
`DROPPED` · `PENDING REPAIR (RR-NNN)`

Mapping from the debate outcome:

| Consensus | Status |
|---|---|
| Real bug, triggered | `REPRODUCED` |
| Real bug, believed real but not triggered after escalation 0→3 | `REPRODUCTION FAILED` |
| Not a bug, with a cited reason (safeguard / by-design / illegitimate repro) | `FALSE POSITIVE` |
| Code-review-sourced AND already-known | `DROPPED` (cite URL) |
| Cited spec / fault-model / invariant artifact | repair request `RR-NNN`, entry `PENDING REPAIR` |
| No matching VERDICT after 5 rounds | `NEEDS MORE INFO` |

### verdict.md format

```markdown
finding_id: MC-1
source: MC | Code Review
novelty: NEW | KNOWN (cite: <URL/dataset-id>; fix-status: unfixed|fixed)
status: <one of the six values above>
severity: Critical | High | Medium | Low
location: file:line
repro_test: repro/test_bugMC-1_xxx.py | -
repair_request: RR-NNN | -          # set only for PENDING REPAIR
debate_rounds: <0 if no debate, else 1..5>
consensus: yes | no                 # no ⇒ status must be NEEDS MORE INFO

## Description
<what the bug is, 2-3 sentences>

## Trigger scenario
<the concrete event sequence from investigation Step 1>

## Developer intent
<what Step 2 found, or "no developer commentary; falls back to <principle>">

## Debate summary
<the objections B raised, how each resolved, and any repro improvement B forced.
 Omit or "no debate opened" when A's verdict was a dismissal.>

## Reproduction result
PASS (paste output) / FAIL (per-level 0→3 summary) / N/A (dropped or false positive)

## Recommendation
<suggested fix or mitigation>
```

## Interface rules the dispatcher enforces (not the agents)

- **`confirmed-bugs.md` is written by the dispatcher**, aggregating all
  `verdict.md` files, in the guide's per-bug schema, with the top novelty split
  line `Reproduced: N = M NEW + K KNOWN`. Agents never write it directly.
- **`RR-NNN` ids are allocated by the dispatcher**, serially. Parallel findings
  must not each scan-and-max the `repair-requests/` dir — they would collide. An
  agent that concludes "spec artifact" **authors the full request** — frontmatter
  `target` / `counterexample` / `scope` (the concrete hunt cfg, invariant, and
  TLA action the counterexample came from — only the reproducer knows these, so
  the dispatcher must not invent them) plus `## Trigger` / `## Evidence` and a
  truthful `## History` seed line — but **omits the lifecycle fields**
  (`id` / `status` / `round`). The dispatcher assigns the next `RR-NNN` and
  stamps `status: OPEN` / `round: 0`, keeping the agent's `scope` verbatim, per
  `repair-request-format.md`.
- **repro files keep the `test_bug<id>_*` name** so the phase summary's
  `test_bug*` glob still counts them.

## What each agent does NOT do

- Neither reads or confirms other findings — each owns exactly one.
- Neither edits the spec, `bug-report.md`, or another finding's files.
- Neither writes `confirmed-bugs.md` or allocates an `RR-NNN` id — the dispatcher does.
