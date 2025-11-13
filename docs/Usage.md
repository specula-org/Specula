# Specula Framework Usage Documentation

This document provides detailed usage instructions for each component of the Specula framework. 

## Table of Contents

1. [Prerequisites](#prerequisites)
2. [Step 1: Code-to-Spec Translation](#step-1-code-to-spec-translation)
3. [Step 2: TLA+ Specification Transformation](#step-2-tla-specification-transformation)
4. [Step 3: Runtime Error Correction](#step-3-runtime-error-correction)
5. [Step 4: Trace Validation](#step-4-trace-validation)
6. [Configuration Management](#configuration-management)
7. [Troubleshooting](#troubleshooting)

## Prerequisites

<details><summary><b>Environment requirements</b></summary>

Environment requirements:
- Python 3.8+
- Java 11+ (for TLA+ tools and CFA analysis)
- Maven (for CFA tool compilation)
- Go 1.18+ (optional, for etcd example)
- LLM API access (OpenAI, Anthropic, etc.)
</details>

To set up Specula:
```bash
# Run Specula's setup script
bash scripts/setup.sh

# Verify TLA+ tools are installed
ls lib/tla2tools.jar
```

Also ensure you provide an API key:
```bash
# For OpenAI
export OPENAI_API_KEY="your-api-key"

# For Anthropic Claude
export ANTHROPIC_API_KEY="your-api-key"

# For DeepSeek
export DEEPSEEK_API_KEY="your-api-key"

# For Gemini 
export GEMINI_API_KEY="your-api-key"
```

## Step 1: Code-to-Spec Translation

The first step translates source code into initial TLA+ specifications using Large Language Models, creating what we call a "translated spec". 

```bash
./specula step1 <input_file> <output_directory> [options]
```

A syntax correction substep is integrated into Step 1 and uses Retrieval-Augmented Generation to automatically detect and fix compilation errors. Specula includes a specialized knowledge base that encodes common TLA+ syntax knowledge and error patterns.

### Generation Modes

There are several generation modes that control the output spec.

#### 1. Direct Translation Mode

Translates source code directly to TLA+ specification:

```bash
./specula step1 examples/etcd/source/raft.go output/etcd/spec/step1/ --mode direct
```

#### 2. Draft-Based Translation Mode (Recommended)

Generates a natural language analysis draft first, then translates to TLA+:

```bash
./specula step1 examples/etcd/source/raft.go output/etcd/spec/step1/ --mode draft-based
```

#### 3. Draft-Only Mode

Generates only the natural language analysis draft:

```bash
./specula step1 examples/etcd/source/raft.go output/etcd/spec/step1/ --mode draft-only
```

#### 4. Existing Draft Mode

Uses a pre-existing draft file for translation:

```bash
./specula step1 examples/etcd/source/raft.go output/etcd/spec/step1/ --mode existing-draft --draft examples/etcd/spec/step1/draft_analysis.txt
```

#### 5. Correction-Only Mode

Corrects an existing TLA+ specification:

```bash
./specula step1 examples/etcd/spec/step1/Raft.tla output/etcd/spec/step1_corrected/ --mode correct-only
```

### Other Usage Examples

**Use custom model:**
```bash
./specula step1 examples/etcd/source/raft.go output/ --model claude-3-5-sonnet-20241022 --temperature 0.2
```

**Print debug logs:**
```bash
./specula step1 examples/etcd/source/raft.go output/ --log-level DEBUG
```

**Disable RAG for error correction:**
```bash
./specula step1 examples/etcd/source/raft.go output/ --no-rag
```

<details><summary><h3 style="display:inline-block">CLI Options</h3></summary>

| Option | Description | Default |
|--------|-------------|---------|
| `--config` | Configuration file path | `config.yaml` |
| `--mode` | Generation mode | From config |
| `--draft` | Path to existing draft file (required for existing-draft mode) | None |
| `--model` | Override LLM model from config | From config |
| `--max-tokens` | Override max tokens from config | From config |
| `--temperature` | Override temperature from config | From config |
| `--no-rag` | Disable RAG-enhanced error correction | False |
| `--log-level` | Set logging level | INFO |
| `--interactive` | Enable HITL checkpoints for syntax correction | False |

</details>
<details><summary><h3 style="display:inline-block">Output files</h3></summary>

- `<ModuleName>.tla`: Generated TLA+ specification (translated spec)
- `draft_analysis.txt`: Natural language analysis (draft-based mode)
- `generation_summary.json`: Generation metadata and statistics
- `corrected_spec/`: Directory containing syntax-corrected specifications
- `attempt_N/`: Intermediate correction attempts
- If `--interactive` is passed:
  - `correctionSummary.txt`: Natural-language summary of correction attempts
  - `remainingErrors.txt`: Unaddressed errors that aren't yet automatically fixed

</details>

## Step 2: TLA+ Specification Transformation

The second step transforms the translated spec into structured, declarative TLA+ specifications that are suitable for model checking and formal verification using Control Flow Analysis (CFA).

Example:
```bash
# ./specula step2 <input_spec.tla> <output_spec.tla>
./specula step2 output/etcd/spec/step1/corrected_spec/Raft.tla output/etcd/spec/step2/Raft.tla
```

<details><summary><h3 style="display:inline-block">CFA Algorithm Modes</h3></summary>

The CFA tool supports different algorithm modes for specific analysis needs:

#### Complete Analysis (Default)

Runs all algorithms including static analysis, unchanged variable analysis, and undefined variable analysis:

```bash
./specula step2 input_spec.tla output_spec.tla
# or explicitly:
java -jar tools/cfa/target/cfa-transformer-1.0.jar input_spec.tla output_spec.tla --algorithm all
```

#### Static Analysis Only

Performs only static analysis for single assignment constraints:

```bash
java -jar tools/cfa/target/cfa-transformer-1.0.jar input_spec.tla output_spec.tla --algorithm sa
```

#### Unchanged Variable Analysis Only

Analyzes only unchanged variables and adds appropriate `UNCHANGED` statements:

```bash
java -jar tools/cfa/target/cfa-transformer-1.0.jar input_spec.tla output_spec.tla --algorithm uc
```

#### Undefined Variable Analysis Only

Analyzes only undefined variables and adds necessary state annotations (using `'`):

```bash
java -jar tools/cfa/target/cfa-transformer-1.0.jar input_spec.tla output_spec.tla --algorithm ud
```

#### Process Cutting Analysis Only

Performs only process cutting analysis for optimizing specifications:

```bash
java -jar tools/cfa/target/cfa-transformer-1.0.jar input_spec.tla output_spec.tla --algorithm pc
```
</details>

<details><summary><h3 style="display:inline-block">CLI Options</h3></summary>

| Option | Description | Default |
|--------|-------------|---------|
| `--algorithm` | Algorithm mode: `all`, `sa`, `uc`, `ud`, `pc` | `all` |
| `--debug` | Print IN/OUT variables for debugging | False |
| `--show-tree` | Display parse tree GUI | False |

</details>

<details><summary><h3 style="display:inline-block">Functionality and Notes</h3></summary>

The CFA tool solves four main problems:

1. Single Assignment Constraint (SA): In atomic actions, a variable can be assigned at most once
2. UNCHANGED Requirement (UC): Adds explicit `UNCHANGED` statements for unmodified variables
3. State Annotation (UD): Adds explicit annotations for variables using modified states (using `'`)
4. Process Cutting (PC): Optimizes specifications by cutting unnecessary processes

### Notes

- The CFA tool is implemented in Java and requires Maven compilation
- Input specifications should use imperative control flow
- Output specifications use declarative TLA+ constructs
- This tool is currently in development and may require manual specification adjustments

</details>

<details><summary><h3 style="display:inline-block">Debugging CFA and Development</h3></summary>

To manually compile CFA for development:
```bash
cd tools/cfa
mvn clean compile
mvn package
```

After building, enable debug mode to view detailed analysis information:
```bash
./tools/cfa/run.sh input_spec.tla output_spec.tla --debug
```
</details>

## Step 3: Runtime Error Correction

The third step automatically detects and fixes runtime errors using TLC model checking.

```bash
# ./specula step3 <input_spec.tla> <output_directory> [options]
./specula step3 output/etcd/spec/step2/Raft.tla output/etcd/spec/step3/
```

Custom configuration can also be specified:
```bash
./specula step3 output/etcd/spec/step2/Raft.tla output/ --max-attempts 5 --tlc-timeout 120
```

<details><summary><h3 style="display:inline-block">How It Works</h3></summary>

Runtime error correction works by:
1. Automatically generating TLC configuration file
2. Running TLC on the input specification
3. Analyzing TLC error output
4. Iteratively using LLM to fix errors based on TLC feedback
5. Re-running TLC to verify corrections and looping
</details>

<details><summary><h3 style="display:inline-block">CLI Options</h3></summary>

| Option | Description | Default |
|--------|-------------|---------|
| `--config` | Configuration file path | `config.yaml` |
| `--max-attempts` | Maximum correction attempts | From config |
| `--tlc-timeout` | TLC execution timeout (seconds) | From config |
| `--log-level` | Set logging level | INFO |
| `--interactive` | Enable interactive HITL checkpoints correction | False |

</details>

<details><summary><h3 style="display:inline-block">Output files</h3></summary>

- `<ModuleName>.cfg`: Generated TLC configuration
- `initial/<ModuleName>.tla`: Copy of input specification
- `attempt_N/<ModuleName>.tla`: Correction attempts
- `corrected_spec/<ModuleName>.tla`: Final runtime-corrected specification
- `runtime_correction_summary.json`: Correction process summary

</details>

## Step 4: Trace Validation

The fourth step ensures that the synthesized TLA+ specs conform with the source code to avoid model-code gaps. It consists of two components: trace validation driver generation and automated instrumentation.

Raft-based runs can use the combined `step4` subcommand as syntactic sugar over the separate `step4.1` and `step4.2` commands. Otherwise, read on for their respective usage.
```bash
./specula step4 \
    --tla examples/etcd/spec/step3/Raft.tla \
    --cfg examples/etcd/spec/step3/Raft.cfg \
    --auto-config output/etcd/spec/step4/raft_config.yaml \
    --stub-template templates/instrumentation/go_trace_stub.template \
    --output examples/etcd/output/instrumented_raft.go \
    output/etcd/spec/step4/spec/
    examples/etcd/config/raft_config.yaml \
    examples/etcd/source/raft.go \
    --verbose
```

### Step 4.1: Trace Validation Driver Generation

This subphase generates specialized TLA+ modules for trace validation.

```bash
# with existing config file
./specula step4.1 <config_file.yaml> <output_directory>
# to automatically generate config
./specula step4.1 --tla <spec.tla> --cfg <config.cfg> --auto-config <config_output.yaml> <output_directory>
```

For example:
```bash
# Using existing configuration
./specula step4.1 examples/etcd/config/raft_config.yaml output/etcd/spec/step4/spec/

# Auto-generate configuration
./specula step4.1 --tla output/etcd/spec/step3/corrected_spec/Raft.tla --cfg output/etcd/spec/step3/Raft.cfg --auto-config output/etcd/config/auto_raft_config.yaml output/etcd/spec/step4/spec/
```

<details><summary><h4 style="display:inline-block">Config File Format</h3></summary>

```yaml
spec_name: "Raft"
constants:
  - name: "Server"
    value: "{\"n1\", \"n2\", \"n3\"}"
  - name: "Value"
    value: "{1, 2, 3}"
variables:
  - name: "currentTerm"
    default_type: "node_map_int"
  - name: "state"
    default_type: "custom"
    default_value: "[n \\in TraceServer |-> StateFollower]"
actions:
  - name: "RequestVote"
    parameters:
      - name: "server"
        source: "Server"
  - name: "BecomeLeader"
    parameters: []
```
</details>

<details><summary><h4 style="display:inline-block">Output Files</h4></summary>

- `specTrace.tla`: Trace validation specification
- `specTrace.cfg`: TLC configuration for trace validation

</details>

### Step 4.2: Automated Instrumentation

Automatically instruments source code for trace collection to generate code-level traces which are used to validate the model-level traces. Currently, Go, Python, and Rust are supported. See [Instrumentation Templates](../templates/README.md) for the template format.

```bash
# ./specula step4.2 <config_file> <source_file> [options]

# to validate instrumentation possibilities
./specula step4.2 examples/etcd/config/raft_config.yaml examples/etcd/source/raft.go --validate-only --verbose

# to generate instrumentation template
./specula step4.2 examples/etcd/config/raft_config.yaml examples/etcd/source/raft.go --generate-template templates/go_custom.template

# to instrument source code
./specula step4.2 examples/etcd/config/raft_config.yaml examples/etcd/source/raft.go --stub-template templates/instrumentation/go_trace_stub.template --output output/etcd/instrumented_raft.go --verbose
```

<details><summary><h4 style="display:inline-block">CLI Options</h4></summary>

| Option | Description |
|--------|-------------|
| `--language` | Programming language (auto-detected if not specified) |
| `--stub-template` | Instrumentation stub template file |
| `--output, -o` | Output file for instrumented code |
| `--validate-only` | Only validate, do not instrument |
| `--generate-template` | Generate template file for specified language |
| `--verbose, -v` | Verbose output |

</details>

## Configuration Management

The framework uses a global `config.yaml` file. For example:

```yaml
# LLM Configuration
llm:
  provider: "anthropic"  # "openai", "anthropic", "deepseek", "gemini
  model: "claude-3-5-sonnet-20241022"
  max_tokens: 8192
  temperature: 0.1
  timeout: 300

# TLA+ Validator Configuration
tla_validator:
  tools_path: "lib/tla2tools.jar"
  timeout: 60

# Generation Configuration
generation:
  max_correction_attempts: 3
  mode: "draft-based"

# Path Configuration
paths:
  prompts_dir: "src/prompts"
  knowledge_base: "src/rag/initial_errors.json"
  output_dir: "output"

# Logging Configuration
logging:
  level: "INFO"
  format: "[%(levelname)s] %(message)s"

# Experiments Configuration
experiments:
  max_workers: 5
  
# Prompt File Paths
prompts:
  baseline: "src/prompts/baseline_correction.txt"
  rag: "src/prompts/rag_correction.txt"
```

Specula also relies on certain environment variables:
```bash
# API Keys; provide whatever matches your selected model
export OPENAI_API_KEY="your-openai-key"
export ANTHROPIC_API_KEY="your-anthropic-key"
export DEEPSEEK_API_KEY="your-deepseek-key"
export GEMINI_API_KEY="your-gemini-key"

# Optional Configuration
export SPECULA_CONFIG_PATH="custom_config.yaml"
export SPECULA_LOG_LEVEL="DEBUG"
```

## Troubleshooting

### TLA+ Tools Not Found

```bash
# Verify TLA+ tools
java -cp lib/tla2tools.jar tla2sany.SANY -help

# If failed, re-run setup
bash scripts/setup.sh
```

### CFA Tool Compilation Failure

```bash
cd tools/cfa
mvn clean compile
```

### LLM API Connection Issues

```bash
# Verify API key
echo $ANTHROPIC_API_KEY

# Test LLM connection
python3 -c "from src.llm.client import get_llm_client; client = get_llm_client(); print(client.model)"
```

