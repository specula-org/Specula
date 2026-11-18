# Specula-CI research prototypes

Prototypes for #188 §3. This branch is not merged into main.

`etcd-v0-v3/` includes the experiment results: reports, per-run summaries and verdicts, comparison results, invariant decisions and scores, the bug-A reproduction, and TLC logs. Omitted: build caches, TLC state directories, per-test raw outputs (aggregated in each `comparison.json`), copied inputs and spec suites, input traces, and agent transcripts. TLC logs keep the statistics and the counterexample action sequence but not the per-state dumps; `events.json`/`summary.json` next to each log hold the condensed counterexample, and rerunning the command in `run.json`/`receipt.json` regenerates the full dump. `blind-incremental-bugs/` has no run outputs.

- `etcd-v0-v3/`: etcd/raft V0–V3 evolution experiment. Overview in `PLAN.md` and `REPORT-20260923.md` (Chinese).
  - 3.1 Action validation: `agent-runs/action-framework-final/`
  - 3.2 Invariant evolution: `agent-runs/inv-evidence/`, `agent-runs/inv-*/TASK.md`
    - Ablation of the judgment step with Claude Opus 5.5 (A0 product rules, A1 separating state, A2 executed evidence, A3 two-axis classification): `inv-ablation/`
    - The same judgment with a requirement-evidence ledger (`REQ-EVIDENCE` comments) in the input model: `inv-evidence-ledger/`
  - 3.3 Update-focused model checking: `experiments/campaign-prefix/`, `agent-runs/progress-probe-V03/`
    - Same-budget comparison of the bug B probe with ordinary model checking: `prefix-ablation/`
- `update-coverage/`: checks that the checking configs reach the update's affected actions with the suite's checks enabled (§3.3), with results on etcd V01–V03 and a MongoDB case study.
- `prefix-branch/`: branches from a recorded run into the update's affected actions instead of starting at Init (§3.3), with results on etcd V01–V03 from the 153-event prefix and from all 11 recordings of the V02 CI run. `choose.py` ranks branch points.
- `env-update/`: finds the actions the focused update model leaves out, summarizes what they do as `EnvUpdate`, and checks the summary (§3.3), with results on etcd V01–V03 and a check of its action split on the 10 blind-study V0 suites.
- `inv-e2e/`: end-to-end blind test of the §3.2 invariant evidence in the full incremental workflow (v0 base skill, v1 divergence evidence, v2 plus the requirement-evidence ledger), with pilot results on case-006.
- `blind-incremental-bugs/`: blind study of historical bug-introducing updates (§2.2): protocol, neutral cohort, runner tools.

Scripts still use the original absolute paths.
