# Specula: Scaling formal specifications for autonomous model checking of system code

Specula is a push-button agentic system that finds deep bugs in concurrent and distributed system code. It uses LLM-based coding agents to write TLA+ specifications of your system: invariants that capture its correctness properties, and formal models that describe the implementation at the right level of abstraction. It then model-checks the specifications and reproduces every violation at the code level.

We have applied Specula to 48 open-source system projects written in seven languages (including MongoDB, etcd-raft, CometBFT, GCC libgomp, and SONiC), where it found 249 bugs, including deadlocks and hangs, data loss and corruption, crashes, and loss of availability. See the [running list of bugs](https://docs.google.com/spreadsheets/d/1AVXdKjNfD4952hZqyB-_wTdrzeTw0SD73f3F0zWJ0as) found by Specula.

## How Specula works

Formal specifications are historically expensive: specifying a real system by hand takes months of expert effort. Asking an LLM to write them directly does not work either; the specifications it produces are imprecise, hallucinated, or oversimplified, and agents asked to repair them tend to game the process. Specula makes coding agents produce specifications that are precise, conformant to the code, and effective for bug finding.

**Invariants grounded in evidence.** Agents mine the system's artifacts (code and comments, issue trackers, commit history, tests, and documentation) for the correctness properties the system must hold, at both the protocol level and the code level. Every invariant must cite concrete evidence from these sources, which keeps it auditable and curbs hallucination.

**Models at the right abstraction.** Agents generate a TLA+ model that follows the control flow of the code, then derive focused variants that target the system's most suspicious behaviors. This keeps the state space tractable for model checking while concentrating the search where bugs are likely.

**Model-code conformance.** Specula automatically instruments the system, collects execution traces, and validates that the model can replay every traced behavior. Trace validation is paired with model checking, so agents cannot "fix" a failure by overfitting the model to traces: the model must admit real behavior and satisfy the invariants at the same time.

**Bugs reproduced, not just reported.** Every invariant violation is replayed at the code level. The agent turns the model's counterexample into a test that triggers the bug in the real system through its public interfaces; shortcuts such as injecting illegal state or calling private internals are forbidden.

**Iteration until convergence.** Invariants, models, and instrumentation all start imperfect. Specula runs repair loops in which agents collect new evidence (a counterexample, a model-code gap, a failed reproduction) and improve the specification, until traces validate and model checking is clean, or a real bug is found.

Specula applies to system code in any programming language, since the code is abstracted into TLA+ models.

## Quick Start

Specula runs as a set of code agent skills and MCP tools. It currently supports [Claude Code](https://docs.anthropic.com/en/docs/claude-code), [Codex](https://openai.com/codex/), and [GitHub Copilot CLI](https://docs.github.com/en/copilot), with more agents to be supported in the future.

### Prerequisites

- Python 3.10+ with pip
- [uv](https://docs.astral.sh/uv/)
- Java 21+ with Maven
- GitHub CLI `gh`
- A supported code agent (Claude Code, Codex, or Copilot CLI); you can contribute an adapter for your favourite agent [here](./scripts/launch/adapters)!
- **A model with strong reasoning capability, configured at high reasoning effort.** Specula relies on the model to read code, infer protocol invariants, and reason about counterexamples; lower reasoning settings noticeably reduce bug yield.

> **Windows:** run Specula inside [WSL2](https://learn.microsoft.com/windows/wsl/install) (the Linux environment built into Windows), where everything below works exactly as on Linux. Native Windows (outside WSL2) is not supported.

### Setup

```bash
git clone https://github.com/specula-org/Specula.git && cd Specula
uv tool install -e .   # installs the `specula` command
specula setup          # installs the agent skills and MCP tools, builds the bundled tools
```

<details>
<summary>Alternative: Manual Agent Setup</summary>

You will need to set up the Specula Agent Skills and MCP with your coding agent.

- To set up skills, symlink [the Specula `skills` folder](https://github.com/specula-org/Specula/tree/main/skills) to the appropriate folder read by your coding agent. For Claude, this is `~/.claude/skills` or `.claude/skills`. For Codex, this is `~/.codex/skills` or `.agents/skills`. For Copilot CLI, this is `.github/skills`.
- To set up the MCP, add the `trace_debugger`, `spec_analyzer`, and `inv_checking_tool` MCPs [here](https://github.com/specula-org/Specula/tree/main/tools/) to your agent config. Be sure to build the CFA tool [here](./tools/cfa) with Maven before adding the `spec_analyzer`.

```bash
# for trace debugger MCP
cd tools/trace_debugger
python3 -m venv .venv
. .venv/bin/activate
pip install -r requirements.txt

# for Claude Code
claude mcp add --transport stdio --scope project \
    --env SPECULA_ROOT=$PWD \
    tracedebugger -- \
    $PWD/tools/trace_debugger/.venv/bin/python \
    $PWD/tools/trace_debugger/mcp_server.py

# for Codex
codex mcp add tracedebugger \
	--env SPECULA_ROOT=$PWD -- \
	$PWD/tools/trace_debugger/.venv/bin/python \
	$PWD/tools/trace_debugger/mcp_server.py
```

</details>

### Scripted Mode

Point Specula at the source repository to analyze, with a name for the run:

```bash
specula run --artifact=/path/to/source mysystem
```

Outputs land under `runs/<run-id>/` in the Specula checkout. See the [Usage Guide](./docs/Usage.md) for detailed configuration: giving the agents more context about the target, agent and model selection, running steps individually, resuming a run, output layout, and batch runs.

### Interactive Mode

Open your coding agent in the Specula directory. The workflow is a sequence of skills, each producing input for the next:

`/code-analysis` → `/spec-generation` → `/harness-generation` → `/validation-workflow` → `/bug-confirmation`

(Codex will use `$code-analysis`, `$spec-generation`, etc.)

**To start**, tell the agent your target and invoke the first skill:

```
This project is a Go implementation of Tendermint BFT consensus (cometbft/cometbft).
The reference algorithm is the Tendermint paper (arXiv:1807.04938). Run /code-analysis.
```

Each skill produces output files (e.g., `modeling-brief.md`, `base.tla`, traces) in `.specula-output/` that the next skill consumes. When one skill completes, invoke the next. You can also run any skill independently, for example `/validation-workflow` on an existing spec.

## License and Contributing

See [LICENSE](LICENSE) for details. Also see [CONTRIBUTING](./CONTRIBUTING.md) for contributor sign-off requirements.
