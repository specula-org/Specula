# inv-e2e: end-to-end blind test of invariant-evolution evidence (#188 §3.2)

`../etcd-v0-v3/inv-ablation/` and `../etcd-v0-v3/inv-evidence-ledger/` reran only the invariant judgment step, on the etcd V0–V3 dev set. In the real workflow, property decisions interact with action modeling, trace validation, configs and model checking, so a judgment-only result need not carry over.

This experiment runs the **full incremental CI workflow** on the blind cohort of `../blind-incremental-bugs/` with three skill variants:

| Arm | Skill tree | Prior suite |
|---|---|---|
| v0 | base `incremental-modeling` and shared skills | blind V0 |
| v1 | v0 + `divergence-evidence.md` + 5 hook lines | blind V0 |
| v2 | v1 + `ledger-usage.md` + 2 hook lines | blind V0 with `REQ-EVIDENCE` comments (comments only) |

- **v0 → v1** measures what requiring divergence evidence adds. Every changed or affected property needs a separating state evaluated by TLC, keeping a property also needs evidence, and implementation behavior is not requirement evidence.
- **v1 → v2** measures what the requirement-evidence ledger adds on top of that.

The overlays and hooks are described in `skill-overlays/`.

**Questions.**
- Does each arm find the update-introduced bug?
- What does it cost?
- How does it treat the prior properties: keep, strengthen, weaken or delete them, and with what evidence?

Grading follows the blind protocol (`../blind-incremental-bugs/PROTOCOL.md`) once Gold is unsealed. With at most 10 cases, the results are directional, not statistical.

The etcd V0–V3 experiments served as the dev set: the skill overlays were written there, and were frozen before any blind case ran.

## Pipeline

| Step | Script | Writes |
|---|---|---|
| 1. Subjects | `materialize.py` | `WORK/subjects/<case>/{old-tree,buggy-tree,old-source,new-source,subject.json}`; `WORK/history/<case>.git` (base and its ancestors only) |
| 2. Skill trees | `build_skills.py [--base-ref REF] --show-diff` | `WORK/skills/<arm>/` + `manifest.json` |
| 3. v2 annotation | `annotate.py --case ...` | `WORK/annotated/<case>/spec/` (frozen) + manifest |
| 4. Workspaces | `prepare.py --arm ... --case ... --rep N` | `WORK/neutral/<hex>/` (the sandbox's `/work`); `WORK/attempts/<arm>/<case>/r<N>/{ws,attempt.json}` |
| 5. Runs | `run.py --arm ... --case ... --rep N [--plan]` | `WORK/attempts/.../log/`; `results/<arm>/<case>/r<N>/` |
| 6. Summary | `collect.py` | `results/summary.{md,json}` |
| Driver | `pipeline.py --case ...` | steps 3–5 for several cases: arms in the fixed order v2, v0, v1, one at a time; the next case is annotated while the current one runs its last arm |
| Analysis | `analysis/timeline.py`, `analysis/prop_changes.py` | per-run behavior timeline from the activity log; which prior properties a run kept, changed, deleted or stopped checking |

`WORK` is `$INV_E2E_WORK` (default `/mydata/bingzhuo/inv-e2e`); `results/` can be redirected with `$INV_E2E_RESULTS`.

Other files:
- `common.py`: paths, the case list, and helpers. It reuses the blind study's `prepare_incremental.py`, which builds the neutral two-commit artifact.
- `agent.py`: the sandbox, plus behavior and cost extraction.
- `check_annotation.py`: checks that a v2 input changes comments only.
- `tools/hist.sh`: git history up to the base commit.
- `prompts/`: the task text, the final-response schema, and the annotation and review prompts.

## v2 inputs: annotation

`annotate.py` runs two fresh agent sessions per case in the sandbox: one annotates (`prompts/annotate.md`), the other reviews every block (`prompts/review.md`).

- **What the sessions see.** Only the base revision: its source tree, the V0 spec, and a history repository that physically contains no later commit.
- **What they write.** Comment lines only. `check_annotation.py` requires that:
  - non-comment lines and `.cfg` files are unchanged;
  - every property has exactly one block, with a known status;
  - SANY parses every changed module.
- **No model review in the notes.** `note:` lines may describe only the evidence search, never the model. Otherwise v2 would get a free model review that v1 does not get. Observations about the model go to `concerns.md`, which stays outside the workspace. The checker warns on model talk in `note`, `clause` and `review` lines.
- **No hint about the cohort.** The examples in the prompts come from a fictional system, not from any cohort case or from etcd.

## Controls

- **Same everything but the arm.** Same V0, task text, schema, model (`claude-opus-5-5`, effort `xhigh`), 4 h timeout, $100 budget and sandbox. Workspaces carry no arm name; the arm is recorded only outside the sandbox.
- **Isolation.** The sandbox is bubblewrap with `--unshare-all --share-net --clearenv`:
  - the workspace is at `/work`;
  - HOME is a throwaway directory holding only the agent's credentials;
  - `network-guard` is first on PATH and blocks curl, wget, gh, text browsers and git fetch/clone/pull.

  The network stays up for the model API and for dependency downloads. Every shell command is audited afterwards, and a hit marks the run `contaminated`. Each flagged run is reviewed by hand and recorded in `results/audit-review.json`. Every flag so far was a false alarm: a local `git clone` of the workspace's own artifact repository, or a `cat` of the guard scripts.
- **Freeze.** Skill trees and annotations are built once. Their hashes go into `manifest.json` and `attempt.json`, and the overlays were not changed after the first real run. Each run is used once.
- **Infrastructure failures.** Runs that end in `USAGE_LIMIT` (the account's 5-hour window) or `AUTH_ERROR` (the sandbox's OAuth session expired) are archived as invalid and restarted from scratch with a freshly prepared workspace. They are never results; their cost is reported separately.

## What is recorded per run

`results/<arm>/<case>/r<N>/` holds three files:
- `run.json`:
  - status, final decision, workflow status and findings paths;
  - wall time, cost and token usage, turns;
  - tool-call counts, and the number of TLC, SANY and build/test commands;
  - the skill files read, which shows whether the arm used its overlay;
  - `invariant-evidence.json` statistics: decisions, evidence records, state sources, claimed versus TLC truth values, bug candidates;
  - the network audit, and the hashes of the skill tree and the prior.
- `final-response.json`: the agent's final answer.
- `invariant-evidence.json` (v1, v2 only).

Grading (`BLIND_DISCOVERED` and so on) is entered by hand in `results/grading.json` after Gold is unsealed; `collect.py` merges it.

## Pilot results: case-006 (etcd Raft, Linearizable ReadIndex)

One run per arm. Gold is still sealed, so "found" below means the arm reported a defect and reproduced it in code; whether it is the Gold bug is not yet known.

| Arm | Decision | Reported defect | Confirmation | Minutes | USD | Turns | TLC cmds |
|---|---|---|---|---:|---:|---:|---:|
| v0 | MODEL_UPDATED | stale read after ReadIndex context reuse | TLC, real trace, reachability test (fails on update, passes on baseline); bug-confirmation step skipped | 118 | 25.51 | 224 | 18 |
| v1 | MODEL_UPDATED | same | TLC, Go reproduction | 114 | 17.06 | 142 | 11 |
| v2 | MODEL_UPDATED | same | TLC, real trace, Go reproduction | 95 | 18.74 | 154 | 14 |

All three arms ended with workflow status `COMPLETED_WITH_LIMITED_COVERAGE`.

**The defect.** The update deletes released ReadIndex requests under their real key, so a caller context can be registered again in the same term. `recvAck` matches acks by context only, so a heartbeat response for the earlier registration confirms the new request. If a newer leader has committed meanwhile, the old leader returns a stale read index.

**Findings.**
- **Detection.** All three arms report the same defect. On this case the baseline already finds it, and v1/v2 add no detection gain.
- **Property evolution, the only visible difference.**
  - v0 added `UpdReadAckFreshness`. When TLC violated it, v0 relaxed it to `UpdReadAckAfterEnqueue`, without a separating state and without saying why the violating state was not a bug. The counterexample it relaxed away was the defect's own mechanism. v0 still found the defect through a later linearizability property, so the relaxation cost nothing here, but it is the behavior `divergence-evidence.md` targets.
  - v1 and v2 made no unsupported reversals. Each recorded 11 evidence records, and the claimed truth values matched TLC on all 18 evaluated sides. v2's run.json shows 16/18 only because of a string-format difference.
  - v2 used the ledger. It kept `ReadDeliveryJustified`, which is annotated as a requirement, and added a stronger property. v1 recorded the same change as a modify.
- **Prior properties.** None of the 25 prior properties was deleted or weakened by any arm. Only `TypeOK` gained fields.
- **Cost.** v1 < v2 < v0. With one run per arm, this may be noise. Part of v0's extra cost is its property-revision loop and an extra repair of a pre-existing V0 crash defect.
- **Annotation cost (v2 only, once per case).** $12.21: annotation $7.80 plus review $4.41.

## Status (2026-11-18)

- Pilot cases 002 (ZooKeeper), 003 (CometBFT) and 004 (OpenRaft) were picked from public metadata only, without looking at Gold. They are running through `pipeline.py`, and their results will be added when all three arms of a case finish.
- Not yet exercised: the codex backend.

## Known gaps

- The base skill commit of the original blind runs is not confirmed; `build_skills.py` defaults to `HEAD`. Here the shared skills come from the same base commit as `incremental-modeling`.
- The incremental skill mentions `specula ci-result` and context compaction. Neither is available in the blind task, which uses `final-schema.json` instead, as the original blind runs did.
- **Cost of killed runs.** The claude backend reports USD only in its final result event, which a timed-out or budget-killed run never emits. `run.json` then has `cost_usd: null` and `behavior.streamed_usage`. Input and cache tokens there are exact; output tokens are a lower bound.
- The scorer of property-evolution behavior is not blind to the arm.

## Example

```sh
python3 materialize.py
python3 build_skills.py --show-diff
python3 annotate.py --case case-006
python3 prepare.py --arm v0 --arm v1 --arm v2 --case case-006 --rep 1
python3 run.py --arm v2 --case case-006 --rep 1     # one arm at a time
python3 pipeline.py --case case-002 --case case-003 --case case-004
python3 collect.py
python3 analysis/prop_changes.py v0 case-006
```
