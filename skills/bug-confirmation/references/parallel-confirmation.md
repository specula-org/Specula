# Parallel Per-Finding Confirmation

Used when the bug-confirmation dispatcher processes findings **one per work item,
in parallel** (`src/specula/confirmlib.py`), instead of one agent consolidating
all findings. This document does not replace `../guide.md` or the phase docs — it
defines the per-finding role and how each finding's verdict is decided. Read
`../guide.md`, `phases/01-investigation.md`, and `phases/02-reproduction.md`
first; every rule there still applies **unchanged**.

**No new statuses, no new interfaces.** This mechanism only changes *how* a
finding's verdict is produced (one dedicated agent per finding, concurrently);
the verdict is always one of the framework's existing outcomes (see "Final
verdict" below).

**Step 0 already ran.** The single-agent phase consolidates the two finding
sources ("Consolidate the two finding sources into one candidate list") in its
own context. The dispatcher lifts that into an explicit step 0
(`consolidate` → `candidates.json`) that merges model-checking findings
(`bug-report.md` / `findings.json`) with code-review families
(`modeling-brief.md`) and **dedups** them — a code-review family already covered
by an MC counterexample is merged into the MC candidate (which wins), so the same
bug is not confirmed twice. You therefore own exactly one *already-deduped*
candidate; do not go looking for its duplicate in the other source.

## The role

### Reproducer (neutral)

The Reproducer runs the **existing** confirmation flow for its one finding,
exactly as the single-agent phase does: investigation (`01-investigation.md`) →
reproduction (`02-reproduction.md`), producing a `repro/test_bug<id>_*` file that
was actually executed, and a verdict.

Its stance is **neutral, even charitable**: give the finding its best honest
shot. Do **not** carry a refute-it bias into reproduction — that is what loses
real bugs. If the finding is real, your job is to make it manifest. If it is not,
say so with a citation. Facts decide.

When reproduction concludes — *with a citation* — that a counterexample is a
spec / fault-model / invariant **artifact** rather than a real bug, the finding
is not dropped: emit a repair request (see "Interface rules" below and
`references/repair-request-format.md`), and the verdict is `PENDING REPAIR`.

## Final verdict — the framework's existing statuses only

The verdict is written using the guide's per-bug schema, status ∈ exactly:

`REPRODUCED` · `REPRODUCTION FAILED` · `FALSE POSITIVE` · `NEEDS MORE INFO` ·
`DROPPED` · `PENDING REPAIR (RR-NNN)`

| Outcome | Status |
|---|---|
| Real bug, triggered | `REPRODUCED` |
| Real bug, believed real but not triggered after escalation 0→3 | `REPRODUCTION FAILED` |
| Not a bug, with a cited reason (safeguard / by-design / illegitimate repro) | `FALSE POSITIVE` |
| Code-review-sourced AND already-known | `DROPPED` (cite URL) |
| Cited spec / fault-model / invariant artifact | repair request `RR-NNN`, entry `PENDING REPAIR` |
| Cannot tell, with a cited gap | `NEEDS MORE INFO` |

## Interface rules the dispatcher enforces (not the agents)

- **`confirmed-bugs.md` is written by the dispatcher**, aggregating all
  per-finding verdicts, in the guide's per-bug schema, with the top novelty split
  line `Reproduced: N = M NEW + K KNOWN`. Agents never write it directly.
- **`RR-NNN` ids are allocated by the dispatcher**, serially. Parallel findings
  must not each scan-and-max the `repair-requests/` dir — they would collide. An
  agent that concludes "spec artifact" **authors the request** — frontmatter
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

- Neither reads nor confirms other findings — each owns exactly one.
- Neither edits the spec, `bug-report.md`, or another finding's files.
- Neither writes `confirmed-bugs.md` or allocates an `RR-NNN` id — the dispatcher does.
