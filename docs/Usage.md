# Usage Guide

## Getting Started

### Supported platforms

- **Linux:** supported directly.
- **macOS:** supported. Specula's long-running-job helpers use GNU `timeout` and `tail --pid`; install GNU coreutils and put its `gnubin` directory on `PATH` (for Homebrew: `brew install coreutils`, then add `$(brew --prefix coreutils)/libexec/gnubin` to `PATH`).
- **Windows:** use [WSL2](https://learn.microsoft.com/windows/wsl/install) and run Specula inside its Linux environment. Native Windows terminals are not supported because the launchers and setup use Bash and other POSIX tools.

When using WSL2, install the prerequisites and agent CLI inside WSL2, then clone and run Specula there. The target repository must also be accessible from that environment.

### Requirements

The dependencies below are not installed by `specula setup`; install them separately as needed.

| Dependency | Used for |
|---|---|
| [uv](https://docs.astral.sh/uv/) | Installing the `specula` command |
| Python 3.10+ with `pip` and `venv` | CLI, launchers, MCP tool environments |
| JDK 21+ and Maven | TLC, SANY, and building the CFA tool |
| Git and Bash | Source/history analysis, worktrees, and launch scripts |
| Standard POSIX utilities (`tee`, `tail`, `du`, and others) | Logging and process coordination |
| `curl` or `wget` | Downloading TLA+ JARs during setup |
| GitHub CLI (`gh`) | Issue and repository research |
| Claude Code, Codex, GitHub Copilot CLI, OpenCode, or Pi | Agent execution |
| Target language toolchain and test dependencies | Harness generation and bug reproduction |

The first setup needs network access to GitHub, PyPI, and Maven Central. Agent runs also need access to the selected model provider and any remote repositories the analysis uses. Claude subscription quota monitoring specifically uses `curl`; if it is unavailable, the quota check warns and fails open rather than stopping the pipeline.

Specula relies on the selected agent to analyze code and reason about counterexamples, so use a strong reasoning model at high effort. Harness generation builds and instruments the target project; verify that the target builds normally before starting a full pipeline.

Some frontier models apply stricter cyber-safety access checks during the `confirm` step, because Phase 4 asks the agent to validate and reproduce real bugs in source code. If those checks block your run, use a model/provider with the required cyber access, or a model that does not block this defensive reproduction workflow, for Phase 4; earlier phases can still use frontier reasoning models.

Model checking can be long-running and memory-intensive. On machines with limited memory, you can run more TLC simulations or configure TLC to offload state data to disk. Limited memory may constrain model checking, but it does not prevent you from using Specula, and we plan to improve resource handling and provide more support for resource-constrained machines in future releases.

### Optional sandbox dependencies

The agent sandbox is **disabled by default** and its dependencies are **not installed** by `specula setup`. Normal runs do not need SRT or Bubblewrap.

To enable the sandbox for Claude Code or Codex, install Node.js 20.11+ and SRT:

```bash
npm install -g @anthropic-ai/sandbox-runtime
```

Linux and WSL2 also require:

- `bubblewrap` (the executable is named `bwrap`)
- `socat`
- `ripgrep`
- unprivileged user namespaces enabled

macOS uses the built-in Seatbelt sandbox instead of Bubblewrap. The sandbox is a guardrail rather than a security boundary; its default policy restricts writes but leaves reads and network access open.

Enable it per run with `SPECULA_SANDBOX=on`. A full pipeline also needs write access to the target checkout and its build caches, for example:

```bash
export SPECULA_SANDBOX=on
export SPECULA_SANDBOX_EXTRA_WRITE="/path/to/source:$HOME/.cache"
specula run --artifact=/path/to/source "name|owner/repository|language|reference"
```

If neither `.specula/sandbox.json` in the launch directory nor `~/.specula/sandbox.json` exists, the first sandboxed run copies the default policy to `~/.specula/sandbox.json`. Review the [sandbox guide](../scripts/launch/sandbox/README.md) before enabling it or tightening read/network access.

Clone Specula, install the CLI, and run its interactive setup:

```bash
git clone https://github.com/specula-org/Specula.git
cd Specula
uv tool install -e .
specula setup
```

Install with `-e` (editable): the `specula` command dispatches to scripts inside the checkout, so it must stay linked to it.

Setup downloads the TLA+ JARs, builds the CFA tool, prepares the MCP tool environments, and offers integration for each supported agent CLI found on `PATH`. It reports and skips any missing agent CLI instead of prompting for it. Setup prompts for global or project-local skill installation when that choice applies.

For Codex, choose `y` to install skills and register MCP servers separately. Choose `plugin` to bundle the skills and MCP tools as `specula-codex@specula`, with cleaner namespacing and easier removal. Codex currently installs plugins into the active Codex profile, making them available across all projects that use that profile; setup asks for confirmation before making this profile-wide change. Codex does not currently support project-scoped plugin installation. Rerun `specula setup` and choose `plugin` again to update it.

More precisely, setup manages:

| Component | Setup behavior |
|---|---|
| `tla2tools.jar` and Community Modules | Downloads them into `lib/` if missing |
| CFA transformer | Builds it with Maven |
| MCP Python packages | Creates tool-specific virtual environments and installs `mcp` and `jsonschema` where required |
| Claude Code | Installs skills and registers all three MCP servers |
| Codex | `y` installs skills and MCP servers separately; `plugin` generates or updates `specula-codex@specula` for the active Codex profile |
| GitHub Copilot CLI | Installs skills and, with Copilot CLI 1.0.21+, registers all three MCP servers |

For Codex, the global/local choice applies only to skills installed separately with `y`; separate MCP registration and plugin installation use the active Codex profile. Copilot MCP registration is user-level and follows `COPILOT_HOME`; its global/local setup choice also controls only where skills are installed. Setup leaves an existing same-named MCP server unchanged and reports the conflict instead of overwriting it. Older Copilot CLI versions still install the skills, but MCP registration is skipped with an upgrade warning.

Setup does **not** install `uv`, Python, a JDK, Maven, Git, `gh`, an agent CLI, target-language dependencies, GNU coreutils, or the optional sandbox dependencies. It does not install the `specula` command either; that is the `uv tool install -e .` step above.

The setup is safe to rerun when updating the checkout. Confirm the CLI afterward:

```bash
specula --help
```

### First run

From the Specula checkout, point Specula at the source repository to analyze:

```bash
specula run \
  --artifact=/absolute/path/to/source \
  "name|github-owner/repository|language|reference"
```

For example:

```bash
specula run \
  --artifact=/work/cometbft \
  "cometbft|cometbft/cometbft|Go|Tendermint BFT"
```

Quote the target descriptor because `|` has special meaning in the shell. Its fields identify the output name, GitHub repository, primary language, and reference algorithm or design document.

With the default isolated workspace, an external source checkout must be supplied with `--artifact`. Alternatively, Specula finds canonical checkouts under `case-studies/<name>/artifact/`.

Select an agent, model, and reasoning effort when needed:

```bash
specula run \
  --agent=codex \
  --model=MODEL_NAME \
  --effort=high \
  --artifact=/absolute/path/to/source \
  "name|owner/repository|language|reference"
```

Supported adapters are `claude-code` (default), `codex`, `copilot-cli`, `opencode`, and `pi`. Model names and effort values are interpreted by the selected agent. OpenCode and Pi model names use `provider/model` syntax.

## Agents and Authentication

| Agent | `--agent` value | Authentication |
|---|---|---|
| Claude Code | `claude-code` | Existing Claude CLI profile; select another with `--claude-alias=NAME` |
| Codex | `codex` | Existing Codex CLI login or configuration |
| GitHub Copilot CLI | `copilot-cli` | Existing Copilot CLI login or token configuration |
| OpenCode | `opencode` | Existing provider authentication configured in the native OpenCode CLI |
| Pi | `pi` | Existing provider authentication configured in the native Pi CLI |

Specula launches the installed agent CLI directly and uses its existing credentials. Authenticate the CLI before starting a pipeline. Claude Code runs default to maximum reasoning effort; Codex and Copilot use their configured defaults unless `--effort` is supplied.

Specula runs Copilot CLI with `--autopilot` and fails before launching a task when the installed CLI does not advertise that capability. Resume-aware pipeline launches require Copilot CLI 1.0.51 or newer plus JSON output; Specula captures the full session UUID and uses `--resume`, refusing ambiguous or missing-session recovery instead of using `--session-id`, which can create an empty session for a stale UUID. Passing `--effort` to Copilot requires Copilot CLI 1.0.4 or newer. OpenCode forwards it as a variant, while Pi forwards it as a thinking level.

`--max-turns` maps to Copilot's autopilot continuation limit. Claude Code, Codex, OpenCode, and Pi accept the option for adapter compatibility but do not enforce it. The reviews between steps pass a fixed value of 30 instead of the pipeline option; all four adapters still ignore it. OpenCode and Pi do not support Specula's agent-side stop gate.

`--policy-retries=N` sets the provider-policy continuation budget for each logical phase agent or confirmation turn. The default is `20`, so one logical turn may advance through at most 20 revised continuation levels after its initial request; `0` disables policy recovery. Automatic rate-limit retries preserve the current level and exact session when available, without resetting or consuming another policy continuation.

`--transient-resumes=N` sets the continuation budget for narrowly classified capacity, provider 5xx, and transport failures. The default is `20`; `0` disables transient recovery. When an adapter has captured the native session identifier, Specula resumes that exact session with a short continuation instead of replaying the original task; if the CLI failed before emitting an ID, it safely retries the original prompt. Corrupt or mismatched state fails closed, and failed invocation logs are retained with `.attempt-N` names before the current log is replaced.

An exact resume preserves the provider-persisted conversation and the files already written in the retained workspace. It cannot restore the terminated CLI process's in-memory state or an in-flight child process, and a provider may omit a partial response that was never committed to the native session.

## Output Structure

Runs are isolated by default under:

```text
runs/<run-id>/
├── run.json
├── tlc-resources.json
├── pipeline.log
├── pipeline-summary.md
└── <name>/
    ├── .specula-output/
    ├── source/          # --keep-original only
    └── changes.patch   # --keep-original only
```

The `.specula-output/` directory contains the modeling brief, specifications, harness, traces, reproduction tests, reports, and per-step logs. `runs/latest` points to the newest run.

By default, Specula works directly in the source passed through `--artifact`, so harness or reproduction work may modify it. Use `--keep-original` to run every phase on a private copy instead. The original checkout stays unchanged, and the final filesystem changes are written to `changes.patch`.

The patch includes every non-`.git` change, including ignored, untracked, and generated files and executable-bit changes. Expect roughly one extra copy of the checkout and Git history. Unsafe layouts such as external symlinks, linked worktrees, submodules, nested repositories, or externally shared Git objects are rejected. Without the optional sandbox, this does not prevent a command from deliberately writing to the original absolute path.

`--keep-original` requires the isolated layout and conflicts with `--no-isolate`. Without it, `--no-isolate` selects the legacy layout: a single target writes step outputs under `$PWD/.specula-output/`, or under `case-studies/<name>/.specula-output/` when that canonical case study exists; multiple targets use `$PWD/<name>/.specula-output/`. For a canonical single target, `pipeline.log` remains under the launch directory's `.specula-output/` while the step outputs and summary use the case-study directory.

TLC can use substantial memory and temporary disk space during model checking. The bundled `scripts/tlc/run_model_check.sh` stores states under `TMPDIR` (or `/tmp`) by default; set `TLC_STATE_DIR` to a larger or faster filesystem when necessary.

TLC memory is admitted against one aggregate budget per Specula run. By default, the first TLC snapshots effective available memory and fixes the budget at 80% for that run. Each live TLC reserves its declared heap plus direct-memory limits (`-m + -M`); a concurrent launch that would exceed the remaining budget is rejected before Java starts and reports the run total, this agent's existing reservation, and the remainder.

Set an explicit bound when you want to divide a machine among several independent runs:

```bash
specula run --tlc-memory-limit=64G ...
```

An explicit bound is authoritative and intentionally does not subtract unrelated system use, so leave any desired OS/JVM-native headroom yourself. The bound covers TLC heap and direct memory, not thread stacks, metaspace, JIT, GC, or other native overhead. For an individual phase or interactive agent session, use `SPECULA_TLC_MEMORY_LIMIT=64G`. Direct multi-target phase commands automatically share one command-scoped budget. When invoking the TLC wrapper outside a Specula launcher, calls from the same working directory share the fallback scope; set an absolute, session-specific `SPECULA_TLC_SCOPE` when unrelated sessions use that directory, and reuse it for every concurrent TLC in the same session.

TLC workers remain unbounded by default: `-w auto` uses every CPU visible to each JVM and the wrapper only reports the resulting aggregate. Set `--tlc-worker-limit=N` (or `SPECULA_TLC_WORKER_LIMIT=N`) only when you want an explicit aggregate worker bound; the wrapper rejects rather than silently shrinking an over-budget request.

## Resuming a Run

Use a stable ID when a run may need to be resumed:

```bash
specula run <name> \
  --run-id=my-run \
  --artifact=/path/to/source \
  "name|owner/repository|language|reference"
```

Attach to the same run and skip completed steps. This resumes at validation:

```bash
specula run <name> \
  --run-id=my-run \
  --skip-analysis \
  --skip-specgen \
  --skip-harness \
  --artifact=/path/to/source \
  "name|owner/repository|language|reference"
```

Specula reuses `runs/<run-id>/<name>/.specula-output/`. Pass the target, artifact, agent, model, and effort again when resuming. A `--keep-original` run automatically resumes against its existing private source even when that flag and the original artifact are omitted. The run's TLC memory and worker limits are restored from `tlc-resources.json`; `run.json` remains an audit record, not arguments for the new invocation.

## Individual Steps

Most users should run `specula run`, which executes every step in order. The commands below are for running or debugging one step at a time.

| Command | What it does | Required input | Main output |
|---|---|---|---|
| `analyze` | Launches an agent to inspect the source, mine Git history and issues, identify evidence-backed modeling Scenarios, and decide what should be modeled | Target source and the four-field target descriptor | `modeling-brief.md`, `analysis-report.md` |
| `specgen` | Converts the modeling brief into code-faithful TLA+ specifications | Source and `modeling-brief.md` | `spec/base.tla`, `spec/MC.tla`, `spec/Trace.tla`, configs, and `instrumentation-spec.md` |
| `harness` | Instruments the implementation and runs test scenarios to collect execution traces | Source and generated specifications | `harness/` and `traces/*.ndjson` |
| `validate` | Checks real traces against the specification, runs TLC, and investigates counterexamples | Source, specifications, harness, and traces | `spec/bug-report.md`, `spec/findings.json`, TLC output, and `spec/changelog.md` |
| `confirm` | Audits and reproduces each candidate bug against the real implementation | Source, modeling brief, and bug report | `confirmed-bugs.md`, reproduction tests, and any repair requests |
| `classify` | Assigns severity to reproduced bugs and finding-tier entries; records other dispositions without severity | `confirmed-bugs.md` | `bug-severity.md` |

For example, run only the code analysis with Codex:

```bash
specula analyze \
  --agent=codex \
  --artifact=/path/to/source \
  "name|owner/repository|language|reference"
```

This writes `.specula-output/modeling-brief.md` and `.specula-output/analysis-report.md` in the current directory. By interface, downstream commands take only the target `name`. Continue passing `--artifact` to `specgen`, `harness`, `validate`, and `confirm` so they can access the source; `classify` reads only the generated report and does not accept `--artifact`:

```bash
specula specgen --agent=codex --artifact=/path/to/source name
```

A single-target individual command uses `.specula-output/` in the current directory; a multi-target command uses `<name>/.specula-output/` for each target. When `SPECULA_RUN_DIR` is set, every target uses `$SPECULA_RUN_DIR/<name>/.specula-output/`. After an adapter exits successfully, each nonterminal step reuses the next step's existing prerequisite check before returning; the downstream command repeats that same check when it starts, so a wait between steps cannot turn an earlier success into an unchecked handoff.

Use `--check` to run a lightweight path-level preflight without starting an agent. It checks the paths currently gated by that step, but does not validate file contents; warnings such as zero trace files remain non-fatal:

```bash
specula validate --check --artifact=/path/to/source name
```

## CLI Reference

### `specula run`

Run the complete analysis-to-classification pipeline:

```bash
specula run [options] "name|owner/repository|language|reference"
```

| Option | Purpose |
|---|---|
| `--dry-run` | Print the step commands without starting agents |
| `--agent=NAME` | Select `claude-code`, `codex`, `copilot-cli`, `opencode`, or `pi` |
| `--model=NAME` | Override the configured model |
| `--effort=LEVEL` | Override reasoning effort |
| `--artifact=PATH` | Set the target source checkout |
| `--keep-original` | Run against a full private source copy and write `changes.patch` |
| `--tlc-memory-limit=SIZE` | Set the run-wide aggregate TLC heap + direct-memory budget; default is 80% of effective available memory at the first TLC start |
| `--tlc-worker-limit=N` | Optionally bound aggregate TLC exploration workers; omitted means report-only |
| `--max-parallel=N` | Set a hard concurrency limit. If omitted, ordinary steps run 1 target agent at a time and per-finding confirmation runs up to 4 Reproducer agents at a time |
| `--max-turns=N` | Set Copilot's autopilot continuation limit; accepted but ignored by Claude Code, Codex, OpenCode, and Pi |
| `--policy-retries=N` | Set provider-policy continuation retries for each phase agent or confirmation turn after its initial adapter invocation (default `20`; `0` disables recovery) |
| `--transient-resumes=N` | Set native-session continuation retries for retryable provider or transport failures (default `20`; `0` disables recovery) |
| `--enable-reviews` | Enable reviews between steps |
| `--legacy-confirm` | Use one confirmation agent instead of per-finding agents |
| `--skip-analysis`, `--skip-specgen`, `--skip-harness` | Reuse earlier outputs |
| `--skip-validate`, `--skip-confirmation`, `--skip-classification` | Reuse later outputs |
| `--confirm-debate` | Add the adversarial confirmation debate in parallel Phase 4 mode |
| `--skip-repair-loop` | Disable the confirmation back-edge repair loop |
| `--max-repair-rounds=N` | Set the global repair-loop round cap (default `10`; `0` means unlimited) |
| `--skip-analysis`, `--skip-specgen`, `--skip-harness` | Reuse early-phase outputs |
| `--skip-validate`, `--skip-confirmation`, `--skip-classification` | Reuse later-phase outputs |
| `--run-id=ID` | Create or attach to an isolated run |
| `--no-isolate` | Use the legacy output layout described above |

`--dry-run` still creates the isolated run metadata, log, and summary files. The confirmation repair loop is enabled by default. `--max-repair-rounds=N` caps rounds across the whole loop, not attempts per request; when the cap is reached, remaining open requests are deferred. For the individual `specula confirm` command, the corresponding debate flags are `--debate` and `--rounds=N` (range `1` through `5`).

Use command-specific help for the authoritative option list:

```bash
specula run --help
specula validate --help
specula confirm --help
```

## Batch Runs

Create a tab-separated queue with one target per line and optional pipeline flags after a literal tab:

```text
alpha|owner/alpha|Go|Raft
beta|owner/beta|Rust|Concurrent queue<TAB>--agent=codex --effort=high
```

Run it with:

```bash
specula batch --queue /path/to/tasks.queue --workers 3
```

The scheduler clones missing repositories under `case-studies/` and creates an isolated workspace for every task. See all scheduler options with `specula batch --help`.

The scheduler owns `--run-id`, `--isolate`, and `--no-isolate` so that each task keeps a separate workspace. Do not include these flags in a queue; Specula rejects the queue and reports the affected line and flag.

## Progress and Logs

Agent activity is printed during each step and written to its log. Set `SPECULA_PROGRESS=off` to disable live reporting. After a run, start with `pipeline-summary.md` for deliverable status and log locations.
