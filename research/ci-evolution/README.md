# Specula-CI research prototypes

Prototypes for #188 §3. This branch is not merged into main.

`etcd-v0-v3/` includes the experiment results: reports, per-run summaries and verdicts, comparison results, invariant decisions and scores, the bug-A reproduction, and TLC logs. Omitted: build caches, TLC state directories, per-test raw outputs (aggregated in each `comparison.json`), copied inputs and spec suites, input traces, and agent transcripts. TLC logs keep the statistics and the counterexample action sequence but not the per-state dumps; `events.json`/`summary.json` next to each log hold the condensed counterexample, and rerunning the command in `run.json`/`receipt.json` regenerates the full dump. `blind-incremental-bugs/` has no run outputs.

- `etcd-v0-v3/`: etcd/raft V0–V3 evolution experiment. Overview in `PLAN.md` and `REPORT-20260923.md` (Chinese).
  - 3.1 Action validation: `agent-runs/action-framework-final/`
  - 3.2 Invariant evolution: `agent-runs/inv-evidence/`, `agent-runs/inv-*/TASK.md`
  - 3.3 Update-focused model checking: `experiments/campaign-prefix/`, `agent-runs/progress-probe-V03/`
    - Same-budget comparison of the bug B probe with ordinary model checking: `prefix-ablation/`
- `blind-incremental-bugs/`: blind study of historical bug-introducing updates (§2.2): protocol, neutral cohort, runner tools.

Scripts still use the original absolute paths.
