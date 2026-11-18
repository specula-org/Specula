# Invariant-maintenance ablation (etcd V0–V3)

For #188 §3.2. The V0–V3 report ran one invariant-maintenance pipeline once per transition with GPT-6 Astra: a judge call, then a call that gathers concrete-state evidence. There was no comparison arm, and the runs were scored by hand. This folder reruns the judgment step with Claude Opus 5.5. The inputs are fixed, the arms differ in method, and every run is scored against the same preregistered obligations.

The question: when an update changes the code, does the agent change the right properties, and does it avoid writing implementation behavior, including a bug, into a property as if it were a requirement?

## Arms

| Arm | Prompt | What it adds |
|---|---|---|
| A0 | `prompts/A0-skill-rules.md` | Product baseline: the property rules of `skills/incremental-modeling` (02 §3, 03 §3, 04 §5). Same inputs and output fields as A1. No separating state is required. |
| A1 | `prompts/A1-judge.md` | Qian's `inv-judge` prompt, unchanged except that `/workspace` became "the current directory". Requires a concrete state on which the old and proposed properties disagree, and states that implementation behavior is not requirement evidence. |
| A2 | `prompts/A2-judge-evidence.md` | A1, then an execution phase in the same session: TLC truth values of old and new properties on the separating state, Go tests on old and new code, and controls. The initial judgment is frozen before any command runs. |
| A3 | `prompts/A3-two-axis.md` | A2, plus a two-axis classification of every witness (implementation produces it × requirement allows it). Requirement evidence must come from tests, documentation, contracts or intent comments, never implementation code. A state the implementation produces but the requirement forbids defaults to a bug candidate, not a property edit. |

A0 → A1 changes two things at once: the guidance wording and the separating-state requirement. So this compares the product's rules with the prototype's prompt; it does not isolate the separating state. Every prompt and harness change, with what triggered it, is listed in `ITERATIONS.md`.

## Setup

- **Packets.** `run.py` rebuilds Qian's judge packets from `../agent-runs/inv-judge-V0x-1/input-manifest.json`:
  - source files come from etcd-io/raft git objects at the manifest revisions;
  - spec files are found by sha256 among the `.tla`/`.cfg` files under `research/`;
  - `update.patch` is the committed one.
  Every file is checked against its recorded hash, and a mismatch stops the run. `TASK.md` is replaced by the arm's prompt. V02 (160 files) and V03 (192 files) are complete. V01 is missing `old/spec/MC.tla` and `old/spec/Trace.tla`, which cannot be recovered by hash; every arm gets the same incomplete packet.
- **Agent.** `claude -p`, Claude Opus 5.5 (`claude-opus-5-5`), effort `xhigh`. Budget cap: $25 per run for A0/A1, $40 for A2/A3.
- **Isolation, A0/A1.** The only tools are `Read, Glob, Grep, Write, Edit`: no shell, web, skills, subagents or MCP. The workspace lies outside the repository. User and project settings are not loaded, auto memory is off, and reads outside the workspace are denied.
- **Isolation, A2/A3.** These arms need Bash, so they run in `sandbox.sh`, which uses unprivileged user and mount namespaces. Only the workspace, the TLC jars and an offline Go module cache are visible; home, the repository and the data disks are empty tmpfs mounts. The network stays up for the model API, so `run.py` records every Bash command and flags any that look like network use.
- **Smoke tests.** Haiku smoke runs confirmed that the rubric and the transcripts could not be read and that TLC and offline Go builds worked.
- **Gold.** `gold.json` restates the 12 obligations (4 per transition) of `../control/inv-judgment-rubric.md`, which was written before Qian's original judge calls, and adds `wrong_if` patterns. One scoring rule differs from the original: in V03, adopting the buggy crossing guard as the auto-leave requirement counts as `incorrect_change`, not `partial_unresolved`.
- **Scoring.** `check_decision.py` checks that each decision is well formed and that its citations point at real packet lines; for A2/A3 it also compares claimed truth values with TLC. Each run is then scored per obligation by hand, in `score.json`. The scorer was not blind to the arm. `audit_freeze.py` checks that no A2/A3 run executed anything before freezing its initial decision.

## Predictions (written before the first run)

- V03 `autoleave_effect_and_progress` is the cell that matters. Qian's Astra run wrote the buggy guard (`oldApplied < pendingConfIndex`) into AutoLeaveAdvance as the requirement. Expectation: A0 does the same, and A1 avoids it in at least some runs.
- If Opus 5.5 avoids the error under both A0 and A1, this dev set cannot separate the arms on its most important obligation.
- Unchanged-safety and representation-only obligations should be handled correctly by every arm.

## Results

One valid run per setting: 12 runs, $96.06.

| Arm | V01 | V02 | V03 | Total | Known bug (A: V01/V02, B: V03) | USD |
|---|---|---|---|---|---|---|
| A0 | 4/4 | 4/4 | 3/4 (crossing guard copied) | 11/12 | named A, A, B | 15.40 |
| A1 | 4/4 | 4/4 | 4/4 | 12/12 | named A, A, B | 15.33 |
| A2 | 3/4 (AckPreservation kept without evidence) | 4/4 | 4/4 | 11/12 | confirmed in code: A, A (found by its own simulation), B | 33.33 |
| A3 | 4/4 | 4/4 | 4/4 | 12/12 | A observed in code but left as requirement-unknown; A not named; B confirmed as a bug candidate | 32.01 |

Supplementary: V03 was run twice more for A0 and A1 before the one-run-per-setting rule was set. Only the auto-leave obligation is scored for them. The crossing guard was copied into the requirement in 2 of 3 A0 runs and 0 of 3 A1 runs (`results/supplementary/`).

What this shows:
- On this dev set, every arm meets 10 of the 12 obligations. The arms separate on two cells only: V03 auto-leave, where A0 copied the crossing guard (2 of 3 runs counting the supplementary ones), and V01 AckPreservation, which A2 missed.
- Executed evidence rarely changes an obligation score. Its main effect is to turn a named bug into one triggered on real code: 5 of the 6 A2/A3 runs did, against 0 for A0/A1. It costs about 2× the money and 3× the time.
- No prompt was changed after the runs (`ITERATIONS.md`, iteration 2).

What this does not show:
- Anything statistical: one run per setting, 12 obligations, and a scorer who was not blind.
- Any downstream effect on the rest of the incremental workflow. That is the question of `../../inv-e2e/`.
- Generality beyond etcd V00–V03.

## Files

| Path | Contents |
|---|---|
| `run.py` | packet rebuild and check, agent runs, retry after usage limits, `results/summary.md` |
| `sandbox.sh` | namespace sandbox for A2/A3 |
| `queue.sh` | the sequential queue used for the last 9 runs |
| `check_decision.py`, `audit_freeze.py` | decision checker; freeze audit (`results/freeze-audit.json`) |
| `gold.json`, `prompts/` | obligations; arm prompts |
| `results/<arm>-<transition>-r1/` | `run.json` (model, prompt hash, packet check, cost, turns, tool use, permission denials, log hash), `decision.json` and `decision.md` (the decision), `check.json` (checker output), `score.json` (per-obligation score); A2/A3 also `decision.initial.json` (the frozen first judgment) and `evidence.json` (each executed check and its result) |
| `results/supplementary/` | the extra V03 runs for A0/A1 (`run.json`, `decision.*`) and their auto-leave scores |
| `results/summary.md` | one row per run |

Runs that hit the account's usage limit are invalid and are not included; `ITERATIONS.md` (1a–1g) records each one and how it was retried. The raw evidence files of A2/A3 (TLC configs and logs, trace dumps, Go probes) and the full stream logs are not committed; `evidence.json` and `check.json` summarize them.

## Running

```sh
python3 run.py prepare V03                       # rebuild and verify a packet only
python3 run.py run A0,A1 V03                     # one run per arm, rep 1
python3 run.py run A2,A3 V01,V02,V03 --jobs 1
python3 run.py --summarize
python3 check_decision.py --all
python3 audit_freeze.py
```

`INV_ABLATION_WORK` (default `/mydata/bingzhuo/inv-ablation`) holds packets, workspaces and full stream logs; the paths in `run.json` point there. `ETCD_RAFT_GIT` must be an etcd-io/raft clone that has the four revisions; a blobless clone of `etcd-io/etcd.git` also resolves them.
