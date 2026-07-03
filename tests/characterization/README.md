# Characterization oracle (migration step 0)

Pins the **current** behavior of the bash orchestration layer as normalized
golden snapshots, so the Python rewrites (steps 1/3/5/6 in `MIGRATION-PLAN.md`)
can be diffed against a fixed baseline. The question each case answers:
*"does my Python behave like the bash it replaced?"*

Stdlib-only on purpose — no pytest/pip needed (the repo `.venv` is currently
broken; step 2 wires this into pytest/CI). Runs under any `python3`.

## Run

```bash
python3 tests/characterization/oracle.py --check      # diff vs golden (exit 1 on mismatch)
python3 tests/characterization/oracle.py --update      # (re)write golden after an INTENTIONAL change
python3 tests/characterization/oracle.py --list        # list case names
python3 tests/characterization/oracle.py --check -k adapter   # filter by substring
```

Once pytest works: `pytest tests/characterization/` runs the same cases.

## What each case guards

| Case | Serves step | Pins |
|------|-------------|------|
| `adapter_normal` | 1 (adapter) | JSON → `.log` (result text) + `.usage.json` (field rename `modelUsage`→`model_usage`, `num_turns` kept when `session_id` empty), exit 0 |
| `adapter_ratelimit` | 1 | `"hit your limit"` → **exit 75** (EX_TEMPFAIL, the retry signal the pipeline depends on) |
| `adapter_malformed` | 1 | non-JSON → `.log` raw fallback + `.usage.json` = `{"error": "parse_failed"}` |
| `adapter_with_session` | 1 | non-empty `session_id` → num_turns fixup: reads the session JSONL, overrides `num_turns` with the assistant-message count, records `num_turns_reported` + `num_tool_uses` |
| `adapter_inline_prompt` | 1 | `--prompt=...` (mktemp path) instead of `--prompt-file` still produces the right output |
| `adapter_claude_missing` | 1 | `claude` not on PATH → spawn fails; bash writes the shell error into `RAW_JSON` and carries on (exit 0 + error in `.log` + `parse_failed`), and the port mirrors it (a divergence a reviewer caught; now pinned) |
| `adapter_nonutf8` | 1 | non-UTF-8 claude output → U+FFFD in `.log` + `parse_failed`, normal exit path — a **deliberate deviation** (bash died on the decode error: non-zero exit, no `.usage.json`, rate-limit exit-75 lost); python-truth golden, the pre-cutover bash fails it |
| `adapter_cmd_*` (×4) | 1 | command construction — how `--effort`/`--model`/`--max-budget` become the `claude` argv, incl. the skip-on-`default`/`0`/empty branches and the `${VAR:-}` rule (exported-but-empty `CLAUDE_EFFORT` still means `--effort max`) |
| `adapter_configdir_*` (×3) | 1 | alias → `CLAUDE_CONFIG_DIR` export (`$HOME/.<alias>`): exported-but-empty env, empty `--claude-alias=` flag, and an ambient `CLAUDE_CONFIG_DIR` the adapter must override (alias is authoritative) |
| `adapter_err_*` (×5) | 1 | validation contract — exit 1 + exact stderr for missing `--log`, both/neither prompt, missing prompt file, unknown option |
| `dryrun_*` (×12) | 3 (phase framework) | arg parse, path calc, exact agent command (`--log/--background`), full generated prompt — incl. the `--repair`/`--recheck` mode variants, the hidden-dir repo skip (real 1-commit repo pins the check line too), the only-dotdirs `$PWD` fallthrough, a 5th `\|` field folding into the reference (bash `IFS='\|' read` remainder rule), and `--max-turns=abc` passing through verbatim (deprecated, never numeric-validated) |
| `bad_artifact_code_analysis` | 3 | bad `--artifact` path degrades to `OK <name> (? commits)` + exit 0 (bash `cd … \|\| echo "?"`), never a traceback |
| `bad_max_parallel_code_analysis` | 3 | non-numeric `--max-parallel` → one-line error + exit 1 — a **deliberate deviation** (bash accepted it, then hung forever in the throttle loop; empty crashed its arithmetic mid-run); python-truth golden |
| `gate_*` (×5) | 3 | each downstream phase's **precondition gate** — the input contract it enforces before running (e.g. spec-gen needs `modeling-brief.md`; exit 1 + "Missing prerequisites" message) |
| `check_ok_*` (×2) | 3 | the `--check` success path — per-phase OK message (`All repos OK.` for code_analysis, `All prerequisites OK.` for the rest) |
| `help_*` (×7) | 3 | `--help` prints the full bash usage text (options, examples) verbatim; review needs its phase arg first |
| `review_*` (×4) | 3 | the review launcher (no `--dry-run`): banner/per-name lines/summary + the exact inline prompt captured from the agent's stdin, incl. the summary's populated branch |
| `review_ratelimit` | 3 | adapter failure propagation: rate limit → adapter exit 75 → launcher aborts with 75, diagnostics on stderr, no PID line (the bash `set -e` + `pid=$(…)` contract) |
| `summary_*` (×7) | 3 | the post-launch full-run path — summarize()'s populated branch (wc-l counts) + the per-phase `Monitor: tail -f …` hint, which dry-run/gate never reach; the nonutf8 variant pins byte-safe, wc-l-style counting (no trailing newline → 2, splitlines would say 3) |
| `pipeline_seq_*` (×4) | 5 (orchestrator) | `launch_pipeline.sh` phase order + review/harness/repair-loop gating under `--skip-*` combos, incl. the `--enable-reviews` branch (REVIEW banners + `launch_review.sh` command lines; reviews are off by default so no other case reaches it). The review command line puts the `<phase>` arg first — a **deliberate deviation**: the pre-cutover bash emitted `--agent=…/--claude-alias=…` before the phase, so `launch_review.sh` (which reads phase from `$1`) parsed phase as `--agent=…` and every real (non-dry-run) `--enable-reviews` run died with `Unknown phase`; python-truth golden, the pre-cutover bash fails it |
| `pipeline_full_run` | 5 | full pipeline (fake agent, all phases): the `main 2>&1 \| tee pipeline.log` plumbing (log asserted byte-identical to stdout), real subprocess sequencing under `set -e`, and generate_summary's populated branches (wc-l counts, du-h log sizes, written/empty/SKIPPED review lines) |
| `pipeline_repair_loop` | 5 | a live repair round: crash-recovery reset (IN_REPAIR→OPEN + History bullet), phase 3 `--repair` + phase 4 `--recheck` invocations, no-progress detection ("stopping to avoid spin"), regenerated ledger (`\|` in bug_id escaped) |
| `pipeline_repair_all_terminal` | 5 | only RESOLVED/DEFERRED requests: the loop exits after 0 rounds; summary tallies `N resolved, M deferred` via the whole-file status grep |
| `pipeline_single_target_cd` | 5 | single target with a `case-studies/<name>/` dir → cd before the phases: summary lands in the case dir while `pipeline.log` stays in the launch cwd (tee opens pre-cd); quota gate silent when `usage.sh` is absent (copied-tree hermetic setup) |
| `repair_state_machine` | 5 | repair-loop primitives `rr_field`/`rr_status`/`rr_set_status` — the mutator that rewrites `status:` in-place and appends a History bullet, across OPEN→IN_REPAIR→RESOLVED |
| `repair_rr_edges` | 5 | RR helper edge table: `status:` past the 25-line frontmatter window (read empty, bullet still appended), missing trailing newline repaired before append, duplicate status lines → first match wins |
| `quota_*` (×8) | 5 | real `wait_for_quota` decision (usage source + `sleep` stubbed): 5h-before-7d, strict `>` (at-limit passes), over→bounded wait then abort, fetch-fail/parse-fail→WARN+proceed, no `resets_at`→600s, past `resets_at`→60s floor (recorded-sleep variants), two-layer `QUOTA_5H`/`QUOTA_7D` |
| `help_pipeline` | 5 | pipeline `--help` prints the full bash usage text verbatim (pre-tee: no `.specula-output/` side effects) |

## How it stays deterministic

- Each case runs in an isolated tmp cwd (dry-run writes `.specula-output/`, so
  never run these from the repo root).
- A stub `claude` on `PATH` emits a fixture JSON, so the adapter's
  post-processing runs with no network / no real API.
- `normalize()` replaces volatile substrings — abs paths → `<ROOT>`/`<HOME>`,
  tmp dirs → `<TMP>`/`<WORK>`/`<ARTIFACT>`, `[HH:MM:SS]` → `[TIME]`.

## Techniques worth knowing

- **Adapter impl switch** (`SPECULA_ADAPTER_IMPL=python`): the adapter cases run
  the bash adapter by default; set this env var to run the Python port
  (`scripts/launch/adapters/claude_code.py`) and diff it against the same
  bash-captured goldens — this is the step-1 parity check. After the strangler
  cutover `claude-code.sh` is a shim to the port, so the default run exercises
  Python too. Set `SPECULA_ADAPTER_IMPL=<path-to-a-bash-script>` to run an
  explicit script — e.g. the pre-cutover bash original (`git show <rev>:…`) to
  capture ground-truth goldens or re-confirm bash ≡ python.
- **Launcher impl switch** (`SPECULA_LAUNCHER_IMPL`): same idea for the phase
  launchers and the pipeline. `python` runs `phaselib.py <key>` /
  `pipelinelib.py` directly; a path runs that bash script (materialize the
  pre-cutover original with `git show <rev>:scripts/launch/launch_pipeline.sh`
  into `scripts/launch/` so its `SCRIPT_DIR`-relative lookups resolve — one
  case at a time, the path overrides every case).
- **Dual-implementation helper drivers** (`repair_*`, `quota_*`): the helpers
  aren't standalone commands, so each case has two equivalent drivers. Bash:
  strip the trailing `main` invocation from the pipeline source, `source` it,
  call the helpers. Python: import `pipelinelib`, call the same-named ports,
  print the same lines — the shared golden is the parity proof. For quota both
  override the usage source (→ a fake that emits a fixture) and stub `sleep`
  (optionally recording the computed wait), so the *real* decision logic runs
  on fixed input without network or blocking. `_pipeline_helper_impl` picks
  bash while `launch_pipeline.sh` still has the bash body, python once it's a
  shim, honoring `SPECULA_LAUNCHER_IMPL` overrides.

## Adding cases (remaining step-0 work)

Register a zero-arg callable in `oracle.CASES` that returns a normalized string,
then `--update` (`-k` with an exact case name updates only that case). 77 cases
so far. When a new golden pins behavior the original
bash also had, verify parity against the pre-cutover script:
`SPECULA_LAUNCHER_IMPL=<path-to-old-bash> oracle.py --check -k <case>` (materialize
the old launcher tree with `git archive $(git merge-base HEAD origin/main) scripts/launch`).
