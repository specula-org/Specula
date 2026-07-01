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
| `adapter_cmd_*` (×3) | 1 | command construction — how `--effort`/`--model`/`--max-budget` become the `claude` argv, incl. the skip-on-`default`/`0`/empty branches |
| `adapter_err_*` (×5) | 1 | validation contract — exit 1 + exact stderr for missing `--log`, both/neither prompt, missing prompt file, unknown option |
| `dryrun_code_analysis` | 3 (phase framework) | arg parse, path calc, exact agent command (`--log/--background`), full generated `.prompt.md` |
| `gate_*` (×5) | 3 | each downstream phase's **precondition gate** — the input contract it enforces before running (e.g. spec-gen needs `modeling-brief.md`; exit 1 + "Missing prerequisites" message) |
| `pipeline_seq_*` (×3) | 5 (orchestrator) | `launch_pipeline.sh` phase order + review/harness/repair-loop gating under `--skip-*` combos |
| `repair_state_machine` | 5 | repair-loop primitives `rr_field`/`rr_status`/`rr_set_status` — the embedded-python mutator that rewrites `status:` in-place and appends a History bullet, across OPEN→IN_REPAIR→RESOLVED |
| `quota_*` (×3) | 5 | real `wait_for_quota` decision (usage source + `sleep` stubbed): 5h-before-7d, strict `>` threshold, over→bounded wait then abort, two-layer `QUOTA_5H`/`QUOTA_7D` |

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
- **Sourcing bash functions in isolation** (`repair_*`, `quota_*`): `oracle.py`
  strips the trailing `main` invocation from `launch_pipeline.sh`, sources the
  rest, and drives individual helpers. For quota it also overrides `USAGE_SCRIPT`
  (→ a fake that emits a fixture) and stubs `sleep`, so the *real* decision logic
  runs on fixed input without network or blocking.

## Adding cases (remaining step-0 work)

Register a zero-arg callable in `oracle.CASES` that returns a normalized string,
then `--update`. 26 cases so far. Still optional (lower value — the pattern is
proven by `dryrun_code_analysis` and the contracts by `gate_*`): the 5 downstream
phases' *happy-path* dry-runs (seed a `.specula-output/` fixture with
`modeling-brief.md`, `spec/*.tla`, etc. so they reach the dry-run print) and the
`launch_review.sh` launcher (reviews are off by default).
