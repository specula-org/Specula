# Property evidence ledger (etcd V0–V3)

For #188 §3.2. A follow-up to `../inv-ablation/`. There, the wrong property decisions came from one confusion: the agent could not tell whether a property was a protocol requirement or only a description of how the code behaved at the time.

The idea tested here: record next to every property in the model why it should hold, as a fixed-format `REQ-EVIDENCE` comment block:

```tla
\* REQ-EVIDENCE <Property>
\* intent:   <what must hold>
\* status:   requirement | impl-abstraction | model-internal | unknown | mixed
\* evidence: <type> <location> "<quote>" -> <part of the intent it supports>
\* watch:    <source locations whose change should trigger a review>
\* clause <name>: <status> — <evidence>   (only for mixed)
```

Evidence types are protocol, doc, comment, contract, test, history and impl. `impl` evidence shows what the code does, never what it should do. A later judge reads these blocks when an update arrives.

The question: with such a ledger in the input model, do the arms of `../inv-ablation/` fix the cells they got wrong without it?

## Stage 1: annotate the input models

The two transitions that separated the arms in `../inv-ablation/` are V01 (input: the V00 model) and V03 (input: the V02 model). Each input model was annotated by a fresh agent that had not seen the experiment, the gold obligations or the later revisions.

| Workspace | Model | Revision |
|---|---|---|
| `ws-V00-model` | V00 (input of V01) | `d58d5d159ae1a1f644a10003f2d8b3b807cd0b3a` (2019-07-13) |
| `ws-V02-model` | V02 (input of V03) | `3ea6503e58b03833d7d32a4ffcd3a76db9ea2520` (2019-08-09) |

- **Prompt:** `prompts/annotate.md`.
- **Workspace contents:** the input packet's `old/spec` and `old/source`, both read-only, and `tools/hist.sh`, which shows etcd history up to the workspace's revision only.
- **Leakage controls:**
  - `hist.sh` refuses any commit that is not the cutoff or one of its ancestors. It also refuses `--all`, branch and tag options, and explicit revisions.
  - The prompt names nothing from the experiment: no bugs, obligations or arms.
  - The agent logs every command and every file it reads in `provenance.md`.
  - The agents ran as Claude Code subagents without a sandbox, so these controls are instructions plus an audit, not enforcement. The provenance logs were checked before the annotations were used.
- **Stage 1b, independent review.** The first pass showed three gaps:
  - intents stated more broadly than their evidence;
  - comments that only narrate the code, counted as requirement evidence;
  - the two annotators labelling the same kind of clause differently.

  `prompts/annotate.md` was extended to cover the first two. A fresh agent per model then reviewed every block against the updated rules (`prompts/review.md`): quote, support for the intent as written, status, and granularity. It edited comments only, and did not see the annotator's reports.
- **Stage 1c, mechanical relabel.** After review, 12 blocks (V00) and 16 blocks (V02) had a block-level status that disagreed with their own `clause` lines, mostly `LET`-based decision contracts that the rules do not allow to be split. `tools/relabel_mixed.py` set these to `status: mixed` and added a `relabel:` line. It changes comments only, and SANY passes on every module.

Final blocks (`spec-final/`):

| Model | Blocks | requirement | mixed | model-internal | impl-abstraction | unknown | alias |
|---|---:|---:|---:|---:|---:|---:|---:|
| V00 | 34 | 18 | 12 | 3 | 0 | 1 | 0 |
| V02 | 68 | 23 | 16 | 17 | 2 | 1 | 9 |

V00 has fewer blocks, because its packet lacks `MC.tla` and `Trace.tla` (see `../inv-ablation/README.md`).

## Stage 2: rerun two arms with the annotated inputs

`run_ledger.py` reuses `../inv-ablation/run.py` unchanged, with four differences:
- **Arms.** L0 is the A0 prompt plus `prompts/ledger-addendum.md`, which says how to use the blocks. L2 is the A2 prompt plus the same addendum. The combined prompts are `prompts/L0.md` and `prompts/L2.md`.
- **Input.** After the packet is verified, `annotated/<model>/spec-final/` is overlaid on `old/spec`. The overlay hashes are recorded in `run.json` under `packet.ledger_overlay`.
- **Runs.** One run per cell, one at a time.
- **Retries.** Up to 30 usage-limit attempts per run; `queue.sh` loops until every job has a result.

**Predictions, written before the runs:**
- A0 with the ledger no longer adopts the V03 crossing guard as the auto-leave requirement.
- A2 with the ledger reviews and modifies the log-equality part of `AckPreservation` in V01.

## Results

Each cell is one run, compared with one run without the ledger.

| Arm | V01 | V03 | USD (V01, V03) | Baseline without the ledger (`../inv-ablation/`) |
|---|---|---|---|---|
| L0 = A0 + ledger | 4/4 | **4/4** | 9.21, 8.58 | A0: 4/4, **3/4** (crossing guard copied into AutoLeaveAdvance); USD 6.23, 5.07 |
| L2 = A2 + ledger | **4/4** | 4/4 (progress borderline) | 9.09, 10.07 | A2: **3/4** (AckPreservation kept without evidence), 4/4; USD 9.73, 10.52 |

- **Both predicted cells flipped.**
  - L0-V03 keeps the level-based eligibility for AutoLeaveAdvance, adds no crossing guard, and adds a liveness property `AutoLeaveProgress`.
  - L2-V01 relaxes the impl-abstraction clause of `AckPreservation_LogUnchanged` and keeps its requirement clause.
- **No new errors.** Every other obligation stays correct. Bug A is named or confirmed in both V01 runs, and bug B in both V03 runs.
- **Cost.** L0 costs about 1.5× A0, because it reads the annotations. L2 costs about the same as A2. The one-time annotation cost is not included.
- **`watch` cannot catch omissions.** In both V01 runs, `CampaignDecisionEligibility` had `watch_touched=false`. Its watched function, `numOfPendingConf`, is not in the diff, because bug A is precisely that this function was not changed. Catching omissions needs a reverse search: when an update introduces a new concept (here, the V2 entry type), find every property and code site that still uses the old one.

**Limits:**
- One run per cell on both sides, and only two discriminating cells.
- The treatment bundles three things: the annotations, the splits and the usage rules of the addendum. Their separate effects are not identified.
- The scorer was not blind to the arm; scores and notes are in each `results/<run>/score.json`.
- The annotations were made under leakage controls that are instructions plus an audit, not a sandbox.
- On the blind cohort, the V0 models carry no such evidence, so the ledger has to be written first. `../../inv-e2e/` tests that end to end.

## Files

| Path | Contents |
|---|---|
| `prompts/annotate.md`, `prompts/review.md` | stage 1 and 1b prompts (placeholders: `{{VERSION}}`, `{{REVISION}}`, `{{DATE}}`, `{{WS}}`, `{{TLA2TOOLS}}`) |
| `prompts/ledger-addendum.md`, `prompts/L0.md`, `prompts/L2.md` | stage 2 addendum and the combined arm prompts |
| `annotated/<model>/spec-final/` | the annotated modules used as stage 2 input (the `.cfg` files are unchanged and omitted) |
| `annotated/<model>/ledger.md`, `splits.md`, `provenance.md` | annotator's property table, splits, and command/file log |
| `annotated/<model>/review/` | reviewer's per-block decisions, summary and provenance |
| `annotated/<model>/relabel.json` | blocks changed by `tools/relabel_mixed.py` |
| `run_ledger.py`, `queue.sh` | stage 2 runner and queue |
| `results/<run>/` | `run.json`, `decision.json`, `decision.md`, `score.json`; L2 also `decision.initial.json` and `evidence.json` |
| `results/summary.md` | one row per run |

Not committed: the intermediate annotation passes (`spec-annotated/`, `spec-reviewed/`), raw L2 evidence files, full stream logs and invalid attempts. Three attempts were cut off by the usage limit and wasted $29.45. All of these stay under `$LEDGER_WORK` (default `/mydata/bingzhuo/inv-evidence-ledger`).

```sh
python3 run_ledger.py plan          # list jobs and which are done
python3 run_ledger.py run --reps 1  # run every missing job
python3 run_ledger.py summarize
LEDGER_WORK=... nohup setsid ./queue.sh >> "$LEDGER_WORK/queue.log" 2>&1 &
```
