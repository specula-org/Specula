# Usage Guide

## Getting Started

### Supported platforms

- **Linux:** supported directly.
- **macOS:** supported. Specula's long-running-job helpers use GNU `timeout` and `tail --pid`; install GNU coreutils and put its `gnubin` directory on `PATH` (for Homebrew: `brew install coreutils`, then add `$(brew --prefix coreutils)/libexec/gnubin` to `PATH`).
- **Windows:** use [WSL2](https://learn.microsoft.com/windows/wsl/install) and run Specula inside its Linux environment. Native Windows terminals are not supported because the launchers and setup use Bash and other POSIX tools.

When using WSL2, install the prerequisites and agent CLI inside WSL2, then clone and run Specula there. The target repository must also be accessible from that environment.

### Requirements

| Dependency | Used for | Installed by `specula setup`? |
|---|---|---|
| [uv](https://docs.astral.sh/uv/) | Installing the `specula` command | No |
| Python 3.10+ with `pip` and `venv` | CLI, launchers, MCP tool environments | No |
| JDK 21+ and Maven | TLC, SANY, and building the CFA tool | No |
| Git and Bash | Source/history analysis, worktrees, and launch scripts | No |
| Standard POSIX utilities (`tee`, `tail`, `du`, and others) | Logging and process coordination | No |
| `curl` or `wget` | Downloading TLA+ JARs during setup | No |
| GitHub CLI (`gh`) | Issue and repository research | No |
| Claude Code, Codex, or GitHub Copilot CLI | Agent execution | No |
| Target language toolchain and test dependencies | Harness generation and bug reproduction | No |

The first setup needs network access to GitHub, PyPI, and Maven Central. Agent runs also need access to the selected model provider and any remote repositories the analysis uses. Claude subscription quota monitoring specifically uses `curl`; if it is unavailable, the quota check warns and fails open rather than stopping the pipeline.

Specula relies on the selected agent to analyze code and reason about counterexamples, so use a strong reasoning model at high effort. Harness generation builds and instruments the target project; verify that the target builds normally before starting a full pipeline.

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

For Codex, choose `y` to install skills and register MCP servers separately. Choose `plugin` to bundle the skills and MCP tools as `specula-codex@specula`, with cleaner namespacing and easier removal. Rerun `specula setup` and choose `plugin` again to update it.

More precisely, setup manages:

| Component | Setup behavior |
|---|---|
| `tla2tools.jar` and Community Modules | Downloads them into `lib/` if missing |
| CFA transformer | Builds it with Maven |
| MCP Python packages | Creates tool-specific virtual environments and installs `mcp` and `jsonschema` where required |
| Claude Code | Installs skills and registers all three MCP servers |
| Codex | `y` installs skills and MCP servers separately; `plugin` generates or updates `specula-codex@specula` |
| GitHub Copilot CLI | Installs skills and, with Copilot CLI 1.0.21+, registers all three MCP servers |

Copilot MCP registration is user-level and follows `COPILOT_HOME`; the global/local setup choice controls only where skills are installed. Setup leaves an existing same-named MCP server unchanged and reports the conflict instead of overwriting it. Older Copilot CLI versions still install the skills, but MCP registration is skipped with an upgrade warning.

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

Supported adapters are `claude-code` (default), `codex`, and `copilot-cli`. Model names and effort values are interpreted by the selected agent.

## Agents and Authentication

| Agent | `--agent` value | Authentication |
|---|---|---|
| Claude Code | `claude-code` | Existing Claude CLI profile; select another with `--claude-alias=NAME` |
| Codex | `codex` | Existing Codex CLI login or configuration |
| GitHub Copilot CLI | `copilot-cli` | Existing Copilot CLI login or token configuration |

Specula launches the installed agent CLI directly and uses its existing credentials. Authenticate the CLI before starting a pipeline. Claude Code runs default to maximum reasoning effort; Codex and Copilot use their configured defaults unless `--effort` is supplied.

Passing `--effort` to Copilot requires Copilot CLI 1.0.4 or newer. `--max-turns` maps to Copilot's autopilot continuation limit. Claude Code and Codex accept the option for adapter compatibility but do not enforce it. The reviews between steps pass a fixed value of 30 instead of the pipeline option; Claude Code and Codex still ignore it.

## Output Structure

Runs are isolated by default under:

```text
runs/<run-id>/
├── run.json
├── pipeline.log
├── pipeline-summary.md
└── <name>/.specula-output/
```

The `.specula-output/` directory contains the modeling brief, specifications, harness, traces, reproduction tests, reports, and per-step logs. `runs/latest` points to the newest run.

The source supplied through `--artifact` is not copied into the isolated workspace. Harness and reproduction work may build or modify that checkout. `--no-isolate` selects the legacy layout: a single target writes step outputs under `$PWD/.specula-output/`, or under `case-studies/<name>/.specula-output/` when that canonical case study exists; multiple targets use `$PWD/<name>/.specula-output/`. For a canonical single target, `pipeline.log` remains under the launch directory's `.specula-output/` while the step outputs and summary use the case-study directory.

TLC can use substantial memory and temporary disk space during model checking. The bundled `scripts/tlc/run_model_check.sh` stores states under `TMPDIR` (or `/tmp`) by default; set `TLC_STATE_DIR` to a larger or faster filesystem when necessary.

## Resuming a Run

Use a stable ID when a run may need to be resumed:

```bash
specula run \
  --run-id=my-run \
  --artifact=/path/to/source \
  "name|owner/repository|language|reference"
```

Attach to the same run and skip completed steps. This resumes at validation:

```bash
specula run \
  --run-id=my-run \
  --skip-analysis \
  --skip-specgen \
  --skip-harness \
  --artifact=/path/to/source \
  "name|owner/repository|language|reference"
```

Specula reuses `runs/<run-id>/<name>/.specula-output/`. Pass the target, artifact, agent, model, and effort again when resuming; `run.json` is an audit record, not a source of arguments for the new invocation.

## Individual Steps

Most users should run `specula run`, which executes every step in order. The commands below are for running or debugging one step at a time.

| Command | What it does | Required input | Main output |
|---|---|---|---|
| `analyze` | Launches an agent to inspect the source, mine Git history and issues, identify bug families, and decide what should be modeled | Target source and the four-field target descriptor | `modeling-brief.md`, `analysis-report.md` |
| `specgen` | Converts the modeling brief into code-faithful TLA+ specifications | Source and `modeling-brief.md` | `spec/base.tla`, `spec/MC.tla`, `spec/Trace.tla`, configs, and `instrumentation-spec.md` |
| `harness` | Instruments the implementation and runs scenarios to collect execution traces | Source and generated specifications | `harness/` and `traces/*.ndjson` |
| `validate` | Checks real traces against the specification, runs TLC, and investigates counterexamples | Source, specifications, harness, and traces | `spec/bug-report.md`, `spec/findings.json`, TLC output, and `spec/changelog.md` |
| `confirm` | Audits and reproduces each candidate bug against the real implementation | Source, modeling brief, and bug report | `spec/confirmed-bugs.md`, reproduction tests, and any repair requests |
| `classify` | Assigns severity to reproduced bugs and finding-tier entries; records other dispositions without severity | `spec/confirmed-bugs.md` | `spec/bug-severity.md` |

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

A single-target individual command uses `.specula-output/` in the current directory; a multi-target command uses `<name>/.specula-output/` for each target. When `SPECULA_RUN_DIR` is set, every target uses `$SPECULA_RUN_DIR/<name>/.specula-output/`. A downstream command stops if its required files from the preceding step are missing.

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
| `--agent=NAME` | Select `claude-code`, `codex`, or `copilot-cli` |
| `--model=NAME` | Override the configured model |
| `--effort=LEVEL` | Override reasoning effort |
| `--artifact=PATH` | Set the target source checkout |
| `--max-parallel=N` | Set a hard concurrency limit. If omitted, ordinary steps run 1 target agent at a time and per-finding confirmation runs up to 4 Reproducer agents at a time |
| `--max-turns=N` | Set Copilot's autopilot continuation limit; accepted but ignored by Claude Code and Codex |
| `--enable-reviews` | Enable reviews between steps |
| `--legacy-confirm` | Use one confirmation agent instead of per-finding agents |
| `--skip-analysis`, `--skip-specgen`, `--skip-harness` | Reuse earlier outputs |
| `--skip-validation`, `--skip-confirmation`, `--skip-classification` | Reuse later outputs |
| `--confirm-debate` | Add the adversarial confirmation debate in parallel Phase 4 mode |
| `--skip-repair-loop` | Disable the confirmation back-edge repair loop |
| `--max-repair-rounds=N` | Set the global repair-loop round cap (default `10`; `0` means unlimited) |
| `--skip-analysis`, `--skip-specgen`, `--skip-harness` | Reuse early-phase outputs |
| `--skip-validation`, `--skip-confirmation`, `--skip-classification` | Reuse later-phase outputs |
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
