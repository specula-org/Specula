# Specula Framework Usage Documentation

This document provides detailed usage instructions for each component of the Specula framework. Specula is an automated framework for synthesizing TLA+ specifications that accurately describe the core logic and behavior of software system implementations through a multi-step workflow.

## Table of Contents

1. [Prerequisites](#prerequisites)
2. [Step 1: Code-to-Spec Translation](#step-1-code-to-spec-translation)
3. [Step 2: TLA+ Specification Transformation](#step-2-tla-specification-transformation)
4. [Step 3: Runtime Error Correction](#step-3-runtime-error-correction)
5. [Step 4: Trace Validation](#step-4-trace-validation)
6. [Processor Modes](#processor-modes)
7. [Configuration Management](#configuration-management)
8. [Troubleshooting](#troubleshooting)

## Prerequisites

Before using Specula, ensure you have completed the environment setup:

```bash
# Run the setup script
bash scripts/setup.sh

# Verify TLA+ tools are installed
ls lib/tla2tools.jar
```

### Environment Requirements

- **Python 3.8+**
- **Java 11+** (for TLA+ tools and CFA analysis)
- **Maven** (for CFA tool compilation)
- **Go 1.18+** (optional, for etcd example)
- **LLM API access** (OpenAI, Anthropic, etc.)

### API Key Configuration

```bash
# For OpenAI
export OPENAI_API_KEY="your-api-key"

# For Anthropic Claude
export ANTHROPIC_API_KEY="your-api-key"

# For DeepSeek
export DEEPSEEK_API_KEY="your-api-key"
```

## Step 1: Code-to-Spec Translation

The first step translates source code into initial TLA+ specifications using Large Language Models, creating what we call a "translated spec".

### Basic Usage

```bash
./specula step1 <input_file> <output_directory> [options]
```

### Generation Modes

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

### Command-Line Options

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

### Step 1.a: Syntax Correction

This substep is integrated into Step 1 and uses a Retrieval-Augmented Generation (RAG) mechanism to automatically detect and fix compilation errors. Specula includes a specialized knowledge base that encodes TLA+ syntax knowledge and error patterns.

### Output Files

- `<ModuleName>.tla`: Generated TLA+ specification (translated spec)
- `draft_analysis.txt`: Natural language analysis (draft-based mode)
- `generation_summary.json`: Generation metadata and statistics
- `corrected_spec/`: Directory containing syntax-corrected specifications
- `attempt_N/`: Intermediate correction attempts

### Usage Examples

**Generate specification with custom model:**
```bash
./specula step1 examples/etcd/source/raft.go output/ --model claude-3-5-sonnet-20241022 --temperature 0.2
```

**Debug generation process:**
```bash
./specula step1 examples/etcd/source/raft.go output/ --log-level DEBUG
```

**Disable RAG correction:**
```bash
./specula step1 examples/etcd/source/raft.go output/ --no-rag
```

## Step 2: TLA+ Specification Transformation

The second step transforms the translated spec into structured, declarative TLA+ specifications that are suitable for model checking and formal verification using Control Flow Analysis (CFA).

### Basic Usage

```bash
./specula step2 <input_spec.tla> <output_spec.tla>
```

### Example

```bash
./specula step2 output/etcd/spec/step1/corrected_spec/Raft.tla output/etcd/spec/step2/Raft.tla
```

### CFA Algorithm Modes

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

### CFA Tool Command-Line Options

| Option | Description | Default |
|--------|-------------|---------|
| `--algorithm` | Algorithm mode: `all`, `sa`, `uc`, `ud`, `pc` | `all` |
| `--debug` | Print IN/OUT variables for debugging | False |
| `--show-tree` | Display parse tree GUI | False |

### Debug Mode

Enable debug mode to view detailed analysis information:

```bash
java -jar tools/cfa/target/cfa-transformer-1.0.jar input_spec.tla output_spec.tla --debug
```

### Functionality

The CFA tool solves four main problems:

1. **Single Assignment Constraint (SA)**: In atomic actions, a variable can be assigned at most once
2. **UNCHANGED Requirement (UC)**: Adds explicit `UNCHANGED` statements for unmodified variables
3. **State Annotation (UD)**: Adds explicit annotations for variables using modified states (using `'`)
4. **Process Cutting (PC)**: Optimizes specifications by cutting unnecessary processes

### Notes

- The CFA tool is implemented in Java and requires Maven compilation
- Input specifications should use imperative control flow
- Output specifications use declarative TLA+ constructs
- Algorithm modes allow focusing on specific transformation aspects
- This tool is currently in development and may require manual specification adjustments

### Manual CFA Tool Compilation

```bash
cd tools/cfa
mvn clean compile
mvn package
```

## Step 3: Runtime Error Correction

The third step automatically detects and fixes runtime errors using TLC model checking.

### Basic Usage

```bash
./specula step3 <input_spec.tla> <output_directory> [options]
```

### Example

```bash
./specula step3 output/etcd/spec/step2/Raft.tla output/etcd/spec/step3/
```

### Command-Line Options

| Option | Description | Default |
|--------|-------------|---------|
| `--config` | Configuration file path | `config.yaml` |
| `--max-attempts` | Maximum correction attempts | From config |
| `--tlc-timeout` | TLC execution timeout (seconds) | From config |
| `--log-level` | Set logging level | INFO |

### Process Flow

1. **Configuration Generation**: Automatically generates TLC configuration file
2. **Initial Model Checking**: Runs TLC on the input specification
3. **Error Analysis**: Analyzes TLC error output
4. **Iterative Correction**: Uses LLM to fix errors based on TLC feedback
5. **Validation**: Re-runs TLC to verify corrections

### Output Files

- `<ModuleName>.cfg`: Generated TLC configuration
- `initial/<ModuleName>.tla`: Copy of input specification
- `attempt_N/<ModuleName>.tla`: Correction attempts
- `corrected_spec/<ModuleName>.tla`: Final runtime-corrected specification
- `runtime_correction_summary.json`: Correction process summary

### Custom Configuration Example

```bash
./specula step3 output/etcd/spec/step2/Raft.tla output/ --max-attempts 5 --tlc-timeout 120
```

## Step 4: Trace Validation

The fourth step ensures that the synthesized TLA+ specs conform with the source code to avoid model-code gaps. It consists of two components: trace validation driver generation and automated instrumentation.

### Step 4.1: Trace Validation Driver Generation

Generates specialized TLA+ modules for trace validation.

#### Basic Usage

```bash
./specula step4.1 <config_file.yaml> <output_directory>
```

#### Auto-Generate Configuration from TLA+ Specification

```bash
./specula step4.1 --tla <spec.tla> --cfg <config.cfg> --auto-config <config_output.yaml> <output_directory>
```

#### Examples

```bash
# Using existing configuration
./specula step4.1 examples/etcd/config/raft_config.yaml output/etcd/spec/step4/spec/

# Auto-generate configuration
./specula step4.1 --tla output/etcd/spec/step3/corrected_spec/Raft.tla --cfg output/etcd/spec/step3/Raft.cfg --auto-config output/etcd/config/auto_raft_config.yaml output/etcd/spec/step4/spec/
```

#### Configuration File Format

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

#### Output Files

- `specTrace.tla`: Trace validation specification
- `specTrace.cfg`: TLC configuration for trace validation

### Step 4.2: Automated Instrumentation

Automatically instruments source code for trace collection to generate code-level traces which are used to validate the model-level traces.

#### Basic Usage

```bash
./specula step4.2 <config_file> <source_file> [options]
```

#### Command-Line Options

| Option | Description |
|--------|-------------|
| `--language` | Programming language (auto-detected if not specified) |
| `--stub-template` | Instrumentation stub template file |
| `--output, -o` | Output file for instrumented code |
| `--validate-only` | Only validate, do not instrument |
| `--generate-template` | Generate template file for specified language |
| `--verbose, -v` | Verbose output |

#### Supported Languages

- **Go** (`.go` files)
- **Python** (`.py` files)
- **Rust** (`.rs` files)

#### Usage Examples

**Validate instrumentation possibilities:**
```bash
./specula step4.2 examples/etcd/config/raft_config.yaml examples/etcd/source/raft.go --validate-only --verbose
```

**Generate instrumentation template:**
```bash
./specula step4.2 examples/etcd/config/raft_config.yaml examples/etcd/source/raft.go --generate-template templates/go_custom.template
```

**Instrument source code:**
```bash
./specula step4.2 examples/etcd/config/raft_config.yaml examples/etcd/source/raft.go --stub-template templates/instrumentation/go_trace_stub.template --output output/etcd/instrumented_raft.go --verbose
```

#### Template Format

Instrumentation templates use `ACTION_NAME` placeholder:

```go
// Go template example
traceAction("ACTION_NAME", map[string]interface{}{
    "node_id": r.id,
    "term": r.Term,
    "state": r.state.String(),
})
```

```python
# Python template example
trace_action("ACTION_NAME", {
    "node_id": self.node_id,
    "state": self.state,
    "term": self.term
})
```


## Configuration Management

### Global Configuration File

The framework uses a global `config.yaml` file:

```yaml
# LLM Configuration
llm:
  provider: "anthropic"  # "openai", "anthropic", "deepseek"
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

### Environment Variables

```bash
# API Keys
export OPENAI_API_KEY="your-openai-key"
export ANTHROPIC_API_KEY="your-anthropic-key"
export DEEPSEEK_API_KEY="your-deepseek-key"

# Optional Configuration
export SPECULA_CONFIG_PATH="custom_config.yaml"
export SPECULA_LOG_LEVEL="DEBUG"
```

## Troubleshooting

### Common Issues

#### 1. TLA+ Tools Not Found

```bash
# Verify TLA+ tools
java -cp lib/tla2tools.jar tla2sany.SANY --help

# If failed, re-run setup
bash scripts/setup.sh
```

#### 2. CFA Tool Compilation Failure

```bash
cd tools/cfa
mvn clean compile
```

#### 3. LLM API Connection Issues

```bash
# Verify API key
echo $ANTHROPIC_API_KEY

# Test LLM connection
python3 -c "from src.llm.client import get_llm_client; client = get_llm_client(); print(client.model)"
```

