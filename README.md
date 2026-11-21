<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="pics/logo.png">
    <img alt="specular" src="pics/logo.png" width=40%>
  </picture>
</p>

<h2 align="center">
Scaling formal specs for autonomous bug finding
</h2>

<p align="center">
  <a href="https://arxiv.org/abs/2607.25333">
    <img src="https://img.shields.io/badge/arXiv-2607.25333-b31b1b.svg" alt="arXiv: 2607.25333">
  </a>
  <a href="https://github.com/specular-org/Specular/actions/workflows/ci.yml">
    <img src="https://github.com/specular-org/Specular/actions/workflows/ci.yml/badge.svg?branch=main" alt="CI">
  </a>
  <a href="https://github.com/specular-org/Specular/blob/main/LICENSE">
    <img src="https://img.shields.io/badge/license-Apache--2.0-blue.svg" alt="License: Apache 2.0">
  </a>
</p>

> **Specula is now Specular.** To update an existing install, follow [Switching from Specula](docs/Usage.md#switching-from-specula).

Specular (formerly Specula) finds deep bugs in concurrent and distributed system code. 
It uses coding agents to write TLA+ specs of the target system, including invariants that capture the system's correctness properties and formal models that describe the system implementation. It then model-checks the specs and reproduces violations at the code level. Specular has been used to find deep bugs in many open-source projects. For more details, see our [paper](https://arxiv.org/abs/2607.25333).

We maintain [a list of bugs found by Specular](https://docs.google.com/spreadsheets/d/1AVXdKjNfD4952hZqyB-_wTdrzeTw0SD73f3F0zWJ0as). We would love to hear about the bugs you find using Specular.

Browse the [case-study archive](https://github.com/specular-org/specula-case-studies) for reports, models, and reproduction evidence. The `case-studies` submodule pins the archive and its [system and run indexes](https://github.com/specular-org/specula-case-studies/blob/2797de3e0801442d3451f26491ccfe876aaf2f2f/catalog/README.md) for this checkout.

## Prerequisites

- Python 3.10+ with pip
- [uv](https://docs.astral.sh/uv/)
- Java 21+ with Maven
- GitHub CLI `gh`
- Supported agents (Claude Code, Codex, Copilot CLI, OpenCode, or Pi). Please contribute [adapters](./scripts/launch/adapters) for new agents.
- Coding agent. (Specular uses coding agents to read code, infer invariants, and reason about counterexamples.)
- **Machine:** We recommend at least 32 GB of RAM and 100 GB of free disk space; more RAM is preferable. See the [Usage Guide](./docs/Usage.md).

> **Windows:** run Specular inside [WSL2](https://learn.microsoft.com/windows/wsl/install). Native Windows (outside WSL2) is not supported yet.

## Recommended Coding Agents

We recommend using the following coding agents, which we actively test:
* Claude Code with Claude Opus 5.5 or Fable 5.2
* Codex with GPT-6-Astra or GPT-6.1-Sol

Other strong coding agents may work, but we do not test them regularly during our development. We recently tested Claude Code with the latest GLM, Kimi, and DeepSeek models (see [Usage Guide](./docs/Usage.md)).

**For the latest OpenAI and Anthropic models**, apply for Trusted Access through [OpenAI](https://chatgpt.com/cyber) and [Anthropic](https://portal.anthropic.com/programs/cvp), respectively. Without the required access, providers may block bug-reproduction requests during confirmation. If you cannot obtain access, use [hybrid configuration](./docs/Usage.md#hybrid-agent-configuration) to select another agent or model for that phase.

## Setup

```bash
git clone https://github.com/specular-org/Specular.git && cd Specular
uv tool install -e .   # installs the `specular` command
specular setup          # installs the agent skills and MCP tools, builds the bundled tools
```

<details>
<summary>Manual Setup</summary>

You need to set up the Specular Agent Skills and MCP with your coding agent.

- Symlink [the Specular `skills` directory](https://github.com/specular-org/Specular/tree/main/skills) to the one read by your coding agent, e.g., `~/.claude/skills` or `.claude/skills` for Claude Code, `~/.codex/skills` or `.agents/skills` for Codex, and `.github/skills` for Copilot CLI.
- Add the `trace_debugger`, `spec_analyzer`, and `inv_checking_tool` [MCP tools](https://github.com/specular-org/Specular/tree/main/tools/) to your agent config. Please [build the CFA tool](./tools/cfa) with Maven before adding `spec_analyzer`.

```bash
# for trace debugger MCP
cd tools/trace_debugger
python3 -m venv .venv
. .venv/bin/activate
pip install -r requirements.txt
cd ../..  # return to the Specular repository root

# for Claude Code
claude mcp add --transport stdio --scope project \
    tracedebugger \
    --env "SPECULAR_ROOT=$PWD" -- \
    "$PWD/tools/trace_debugger/.venv/bin/python" \
    "$PWD/tools/trace_debugger/mcp_server.py"

# for Codex
codex mcp add tracedebugger \
	--env "SPECULAR_ROOT=$PWD" -- \
	"$PWD/tools/trace_debugger/.venv/bin/python" \
	"$PWD/tools/trace_debugger/mcp_server.py"

# for GitHub Copilot CLI 1.0.21+
copilot mcp add tracedebugger \
    --env "SPECULAR_ROOT=$PWD" -- \
    "$PWD/tools/trace_debugger/.venv/bin/python" \
    "$PWD/tools/trace_debugger/mcp_server.py"
```

Automatic MCP configuration is skipped for older Copilot CLI versions; upgrade to the latest version to enable it.

</details>

## Auto Mode

```bash
specular run mysys \
  --artifact=/path/to/repo \
  --guidance=/absolute/path/to/mysys-guidance.md
```

The `mysys-guidance.md` is optional but recommended.
It is a configuration file that guides Specular to focus on target modules and scenarios,
	with consistent modeling scope across runs.
We provide a [template](./docs/modeling-guidance-template.md) and an
[example](./docs/modeling-guidance-example.md).

Outputs are stored in `runs/<run-id>`. 
After a run, start with `runs/latest/pipeline-summary.md`.

Add `--keep-original` to leave the source checkout untouched. Specular runs the
same agents against a full private copy and writes a reviewable source diff to
`runs/<run-id>/mysys/changes.patch`. Ignored build output is omitted, while
binary and trace contents remain in the private source instead of being
inlined. Specular does not apply the diff to the original checkout.

The detailed usage and configurations can be found in the [Usage Guide](./docs/Usage.md).

## Continuous Verification

Initialize a persistent model and harness, then check later source changes incrementally:

```bash
specular run --ci-init --ci-dir=/work/mysys-ci \
  --artifact=/path/to/repo --guidance=/path/to/mysys-guidance.md mysys
specular run --incremental --ci-dir=/work/mysys-ci
```

Keep the CI directory outside the source checkout. See [Add Specular to CI](docs/Usage.md#add-specular-to-ci) for setup, results, and the GitHub Actions workflow. Existing TLA+ models and verification assets can be imported with [Bring Your Own Model](docs/Usage.md#bring-your-own-model-byom).

## Interactive Mode

Open your coding agent in the Specular directory. The workflow is a sequence of skills, each producing input for the next:

`code-analysis` → `spec-generation` → `harness-generation` → `validation-workflow` → `bug-confirmation`

(Codex uses `$code-analysis`, `$spec-generation`, etc. after choosing `y` in `specular setup`, or `$specular-codex:code-analysis`, `$specular-codex:spec-generation`, etc. in plugin mode.)

To start, tell the agent your target and invoke the first skill:

```
This project is a Go implementation of Tendermint BFT consensus (cometbft/cometbft).
The reference algorithm is the Tendermint paper (arXiv:1807.04938). Run /code-analysis.
```

Each skill produces output files (e.g., `modeling-brief.md`, `base.tla`, traces) in `.specular-output` that the next skill will consume. 
When one skill completes, invoke the next. You can also run any skill independently, e.g., `validation-workflow` on an existing spec.

## Changelog

See [CHANGELOG.md](CHANGELOG.md) for release history and notable changes.

## Who uses Specular?

Specular is used by researchers and engineers at organizations including:

<p align="center">
  <a href="https://www.google.com"><img src="docs/logos/google.png" height="37" alt="Google"></a>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;
  <a href="https://www.microsoft.com"><img src="docs/logos/microsoft.png" height="26" alt="Microsoft"></a>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;
  <a href="https://www.amazon.com#gh-light-mode-only"><img src="docs/logos/amazon.png" height="35" alt="Amazon"></a><a href="https://www.amazon.com#gh-dark-mode-only"><img src="docs/logos/amazon-dark.png" height="35" alt="Amazon"></a>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;
  <a href="https://www.nvidia.com#gh-light-mode-only"><img src="docs/logos/nvidia.png" height="25" alt="NVIDIA"></a><a href="https://www.nvidia.com#gh-dark-mode-only"><img src="docs/logos/nvidia-dark.png" height="25" alt="NVIDIA"></a>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;
  <a href="https://www.oracle.com"><img src="docs/logos/oracle.png" height="16" alt="Oracle"></a>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;
  <a href="https://www.huawei.com#gh-light-mode-only"><img src="docs/logos/huawei.png" height="48" alt="Huawei"></a><a href="https://www.huawei.com#gh-dark-mode-only"><img src="docs/logos/huawei-dark.png" height="48" alt="Huawei"></a>
</p>

<p align="center">
  <a href="https://www.alibabagroup.com#gh-light-mode-only"><img src="docs/logos/alibaba.png" height="18" alt="Alibaba Group"></a><a href="https://www.alibabagroup.com#gh-dark-mode-only"><img src="docs/logos/alibaba-dark.png" height="18" alt="Alibaba Group"></a>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;
  <a href="https://www.uber.com#gh-light-mode-only"><img src="docs/logos/uber.png" height="22" alt="Uber"></a><a href="https://www.uber.com#gh-dark-mode-only"><img src="docs/logos/uber-dark.png" height="22" alt="Uber"></a>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;
  <a href="https://www.antgroup.com#gh-light-mode-only"><img src="docs/logos/ant-group.png" height="39" alt="Ant Group"></a><a href="https://www.antgroup.com#gh-dark-mode-only"><img src="docs/logos/ant-group-dark.png" height="39" alt="Ant Group"></a>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;
  <a href="https://www.mongodb.com#gh-light-mode-only"><img src="docs/logos/mongodb.png" height="30" alt="MongoDB"></a><a href="https://www.mongodb.com#gh-dark-mode-only"><img src="docs/logos/mongodb-dark.png" height="30" alt="MongoDB"></a>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;
  <a href="https://www.datadoghq.com#gh-light-mode-only"><img src="docs/logos/datadog.png" height="29" alt="Datadog"></a><a href="https://www.datadoghq.com#gh-dark-mode-only"><img src="docs/logos/datadog-dark.png" height="29" alt="Datadog"></a>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;
  <a href="https://www.cloudera.com"><img src="docs/logos/cloudera.png" height="16" alt="Cloudera"></a>
</p>

<p align="center">
  <a href="https://shopee.com"><img src="docs/logos/shopee.png" height="35" alt="Shopee"></a>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;
  <a href="https://milvus.io"><img src="docs/logos/milvus.png" height="27" alt="Milvus"></a>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;
  <a href="https://ozone.apache.org#gh-light-mode-only"><img src="docs/logos/ozone.png" height="25" alt="Apache Ozone"></a><a href="https://ozone.apache.org#gh-dark-mode-only"><img src="docs/logos/ozone-dark.png" height="25" alt="Apache Ozone"></a>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;
  <a href="https://ratis.apache.org#gh-light-mode-only"><img src="docs/logos/ratis.png" height="27" alt="Apache Ratis"></a><a href="https://ratis.apache.org#gh-dark-mode-only"><img src="docs/logos/ratis-dark.png" height="27" alt="Apache Ratis"></a>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;
  <a href="https://asterinas.github.io"><img src="docs/logos/asterinas.png" height="31" alt="Asterinas"></a>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;
  <a href="https://sregym.com"><img src="docs/logos/sregym.png" height="31" alt="SREGym"></a>
</p>

<p align="center">
  <a href="https://illinois.edu#gh-light-mode-only"><img src="docs/logos/uiuc.png" height="32" alt="University of Illinois Urbana-Champaign"></a><a href="https://illinois.edu#gh-dark-mode-only"><img src="docs/logos/uiuc-dark.png" height="32" alt="University of Illinois Urbana-Champaign"></a>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;
  <a href="https://www.berkeley.edu#gh-light-mode-only"><img src="docs/logos/berkeley.png" height="35" alt="UC Berkeley"></a><a href="https://www.berkeley.edu#gh-dark-mode-only"><img src="docs/logos/berkeley-dark.png" height="35" alt="UC Berkeley"></a>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;
  <a href="https://www.purdue.edu#gh-light-mode-only"><img src="docs/logos/purdue.png" height="36" alt="Purdue University"></a><a href="https://www.purdue.edu#gh-dark-mode-only"><img src="docs/logos/purdue-dark.png" height="36" alt="Purdue University"></a>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;
  <a href="https://www.nyu.edu#gh-light-mode-only"><img src="docs/logos/nyu.png" height="38" alt="New York University"></a><a href="https://www.nyu.edu#gh-dark-mode-only"><img src="docs/logos/nyu-dark.png" height="38" alt="New York University"></a>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;
  <a href="https://www.virginia.edu#gh-light-mode-only"><img src="docs/logos/uva.png" height="36" alt="University of Virginia"></a><a href="https://www.virginia.edu#gh-dark-mode-only"><img src="docs/logos/uva-dark.png" height="36" alt="University of Virginia"></a>
</p>

## Acknowledgement

We are grateful to the generous support from
* TLA+ Foundation
* OpenAI
* Anthropic (AI for Science Program)
* Qingrong Chen

## License

[Apache License 2.0](LICENSE).
