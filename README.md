# Specula: A Framework for Finding Bugs in System Implementations Using TLA+

Specula is an AI-powered framework that uses TLA+ formal verification to find bugs in system implementations. By leveraging AI to accelerate the modeling process — from code analysis to spec generation to trace validation — Specula significantly reduces the cost and effort of formal verification while finding more bugs, including subtle ones that are difficult to discover through traditional methods.

Specula has found **23 new bugs** across multiple production systems (continuously updating; see the [full bug tracker](https://docs.google.com/spreadsheets/d/1AVXdKjNfD4952hZqyB-_wTdrzeTw0SD73f3F0zWJ0as/edit?gid=996176958#gid=996176958) for details). Case study artifacts are available in the [specula-case-studies](https://github.com/specula-org/specula-case-studies) repository.

## Architecture

![Specula Workflow](docs/images/workflow.svg)

Specula is a multi-phase, agentic workflow. Each phase is driven by a dedicated skill that encodes methodology and reference materials, and is executed by a code agent.

<summary><b>Architecture Details</b></summary>

1. **Code Analysis.** Deep static analysis of the target codebase: map core modules, mine git history and GitHub issues for historical bugs, and compare the implementation against the reference paper and common related implementations to identify deviations. Group findings into Bug Families by shared mechanism, and produce a Modeling Brief that drives spec generation.

2. **Spec Generation.** Translate the Modeling Brief into a TLA+ specification suite: a base spec faithful to the implementation's actual control flow (not the reference algorithm), a model checking wrapper with counter-bounded actions, a trace validation spec, and an instrumentation mapping.

3. **Trace Validation & Model Checking.** Two sub-workflows that alternate:
   - **Trace Validation** — Verify that the spec can reproduce every state transition observed in a real execution trace, catching spec-implementation inconsistencies before model checking.
   - **Model Checking** — Explore the full state space to find invariant violations. Analyze counterexamples to determine if they represent real implementation bugs, spec bugs, or known issues.

</details>

## Quickstart

Specula runs as a set of code agent skills and MCP tools. It currently supports [Claude Code](https://docs.anthropic.com/en/docs/claude-code) and [Codex](https://openai.com/index/codex/), with more agents to be supported in the future.

### Prerequisites

- A supported code agent (Claude Code or Codex) installed
- Java 21+ (for TLC model checker)

### Setup

```bash
git clone https://github.com/specula-org/Specula.git && cd Specula
bash scripts/setup.sh
```

### Running the Pipeline

**Full pipeline** (all three phases, one or more systems):

```bash
bash scripts/launch_pipeline.sh "cometbft|cometbft/cometbft|Go|Tendermint BFT"
```

**Individual phases:**

```bash
# Phase 1: Code Analysis
bash scripts/launch_code_analysis.sh "cometbft|cometbft/cometbft|Go|Tendermint BFT"

# Phase 2: Spec Generation
bash scripts/launch_spec_generation.sh cometbft

# Phase 3: Validation
bash scripts/launch_spec_validation.sh cometbft
```

## Previous Version

The original Specula (v1) was a 4-step code-to-spec synthesis pipeline. That version is preserved on the [`archive/v1`](../../tree/archive/v1) branch.

## License

See [LICENSE](LICENSE) for details.
