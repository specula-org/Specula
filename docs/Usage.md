# Specula+ Usage Documentation

This document provides detailed usage instructions for each component of the Specula+ framework. The framework operates through a five-step pipeline, each with specific tools and configurations.

## Table of Contents

1. [Prerequisites](#prerequisites)
2. [Step 1: Initial Specification Generation](#step-1-initial-specification-generation)
3. [Step 2: Syntax Correction](#step-2-syntax-correction)
4. [Step 3: Control Flow Analysis](#step-3-control-flow-analysis)
5. [Step 4: Runtime Error Correction](#step-4-runtime-error-correction)
6. [Step 5: Trace Validation Framework](#step-5-trace-validation-framework)
7. [Configuration Management](#configuration-management)

## Prerequisites

Before using Specula+, ensure you have completed the setup process:

```bash
# Run the setup script
bash scripts/setup.sh

# Verify TLA+ tools are installed
ls lib/tla2tools.jar
```

The framework requires:
- Python 3.8+
- Java 8+ (for TLA+ tools)
- Access to LLM APIs (OpenAI, Anthropic, etc.)

## Step 1: Initial Specification Generation

The `iispec_generator` module translates source code into initial TLA+ specifications using Large Language Models.

### Basic Usage

```bash
python3 -m src.core.iispec_generator <input_file> <output_directory> [options]
```

### Modes of Operation

#### 1. Direct Translation Mode

Translates source code directly to TLA+ without intermediate analysis:

```bash
python3 -m src.core.iispec_generator examples/etcd/source/raft.go examples/etcd/spec/step1/ --mode direct
```

#### 2. Draft-Based Translation Mode

Generates a natural language draft first, then translates to TLA+:

```bash
python3 -m src.core.iispec_generator examples/etcd/source/raft.go examples/etcd/spec/step1/ --mode draft-based
```

#### 3. Draft-Only Mode

Generates only the natural language analysis draft:

```bash
python3 -m src.core.iispec_generator examples/etcd/source/raft.go examples/etcd/spec/step1/ --mode draft-only
```

#### 4. Existing Draft Mode

Uses a pre-existing draft file for translation:

```bash
python3 -m src.core.iispec_generator examples/etcd/source/raft.go examples/etcd/spec/step1/ --mode existing-draft --draft examples/etcd/spec/step1/draft_analysis.txt
```

#### 5. Correction-Only Mode

Corrects an existing TLA+ specification:

```bash
python3 -m src.core.iispec_generator examples/etcd/spec/step1/Raft.tla examples/etcd/spec/step1_corrected/ --mode correct-only
```

### Command-Line Options

| Option | Description | Default |
|--------|-------------|---------|
| `--config` | Configuration file path | `config.yaml` |
| `--mode` | Generation mode (direct, draft-based, correct-only, draft-only, existing-draft) | From config |
| `--draft` | Path to existing draft file (required for existing-draft mode) | None |
| `--model` | Override LLM model from config | From config |
| `--max-tokens` | Override max tokens from config | From config |
| `--temperature` | Override temperature from config | From config |
| `--log-level` | Set logging level (DEBUG, INFO, WARNING, ERROR) | INFO |

### Output Files

- `<ModuleName>.tla`: Generated TLA+ specification
- `draft_analysis.txt`: Natural language analysis (draft-based mode)
- `generation_summary.json`: Generation metadata and statistics
- `<ModuleName>_correction_attempt_N.tla`: Intermediate correction attempts

### Example Usage Scenarios

**Generate specification with custom model:**
```bash
python3 -m src.core.iispec_generator examples/etcd/source/raft.go output/ --model claude-3-5-sonnet-20241022 --temperature 0.2
```

**Debug generation process:**
```bash
python3 -m src.core.iispec_generator examples/etcd/source/raft.go output/ --log-level DEBUG
```

## Step 2: Syntax Correction

The `processor` module provides automated syntax correction using RAG-enhanced error correction.

### Basic Usage

```bash
python3 -m src.core.processor <input_file> <output_directory> [options]
```

### Experimental Comparison Mode

Runs three-experiment comparison (baseline, baseline correction, RAG correction):

```bash
python3 -m src.core.processor --mode experiments examples/etcd/config/raft_actions.yaml output/experiments/
```

### Output Structure

```
output_directory/
├── spec_0.tla              # Generated specifications
├── corrected_spec_0.tla    # RAG-corrected versions
├── stats.json              # Processing statistics
└── experiment_results/     # Experiment mode outputs
```

## Step 3: Control Flow Analysis

The CFA tool transforms imperative-style TLA+ specifications into structured, declarative formats.

### Basic Usage

```bash
./tools/cfa/run.sh <input_spec.tla> <output_spec.tla>
```

### Example

```bash
./tools/cfa/run.sh examples/etcd/spec/step2/Raft.tla examples/etcd/spec/step3/Raft.tla
```

### Notes

- The CFA tool is implemented in Java and requires compilation
- Input specifications should use imperative control flow (labels, gotos)
- Output specifications use declarative TLA+ constructs
- This tool is currently in development and may require manual specification adjustments

## Step 4: Runtime Error Correction

The `runtime_corrector` module automatically detects and fixes runtime errors using TLC model checking.

### Basic Usage

```bash
python3 -m src.core.runtime_corrector <input_spec.tla> <output_directory> [options]
```

### Example

```bash
python3 -m src.core.runtime_corrector examples/etcd/spec/step3/Raft.tla examples/etcd/spec/step4/
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
- `<ModuleName>_initial.tla`: Copy of input specification
- `<ModuleName>_attempt_N.tla`: Correction attempts
- `<ModuleName>_corrected.tla`: Final corrected specification
- `runtime_correction_summary.json`: Correction process summary

### Example with Custom Configuration

```bash
python3 -m src.core.runtime_corrector examples/etcd/spec/step3/Raft.tla output/ --max-attempts 5 --tlc-timeout 120
```

## Step 5: Trace Validation Framework

Step 5 consists of two components: trace validation driver generation and automated instrumentation.

### Step 5.1: Trace Validation Driver Generation

The `spectrace_generator` generates specialized TLA+ modules for trace validation.

#### Basic Usage

```bash
python3 -m src.core.spectrace_generator <config_file.yaml> <output_directory>
```

#### Example

```bash
python3 -m src.core.spectrace_generator examples/etcd/config/raft_config.yaml examples/etcd/spec/step5/spec/
```

#### Configuration File Format

```yaml
spec_name: "Raft"
constants:
  - name: "Servers"
    value: "{\"n1\", \"n2\", \"n3\"}"
  - name: "MaxTerm"
    value: "3"
variables:
  - name: "currentTerm"
    default_type: "node_map_int"
  - name: "state"
    default_type: "node_map_int"
actions:
  - name: "RequestVote"
    parameters:
      - name: "server"
        source: "Servers"
  - name: "BecomeLeader"
    parameters: []
```

#### Output Files

- `specTrace.tla`: Trace validation specification
- `specTrace.cfg`: TLC configuration for trace validation

### Step 5.2: Automated Instrumentation

The `instrumentation` module automatically instruments source code for trace collection.

#### Basic Usage

```bash
python3 -m src.core.instrumentation <config_file> <source_file> [options]
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

#### Example Usage

**Validate instrumentation possibilities:**
```bash
python3 -m src.core.instrumentation examples/etcd/config/raft_config.yaml examples/etcd/source/raft.go --validate-only --verbose
```

**Generate instrumentation template:**
```bash
python3 -m src.core.instrumentation examples/etcd/config/raft_config.yaml examples/etcd/source/raft.go --generate-template templates/go_custom.template
```

**Instrument source code:**
```bash
python3 -m src.core.instrumentation \
    examples/etcd/config/raft_config.yaml \
    examples/etcd/source/raft.go \
    --stub-template templates/instrumentation/go_trace_stub.template \
    --output examples/etcd/output/instrumented_raft.go \
    --verbose
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

#### Configuration File for Instrumentation

```yaml
actions:
  - name: "RequestVote"
    function: "requestVote"  # Function name in source code
  - name: "BecomeLeader"
    function: "becomeLeader"
```

## Configuration Management

### Global Configuration File

The framework uses a global `config.yaml` file:

```yaml
# LLM Configuration
llm:
  base_url: "https://api.openai.com"
  model: "claude-3-5-sonnet-20241022"
  max_tokens: 8192
  temperature: 0.1
  timeout: 300

# TLA+ Validator Configuration
tla_validator:
  tools_path: "lib/tla2tools.jar"
  timeout: 30

# Generation Configuration
generation:
  max_correction_attempts: 3
  mode: "draft-based"

# Path Configuration
paths:
  prompts_dir: "src/prompts"
  output_dir: "output"
  knowledge_base: "data/knowledge_base.json"

# Logging Configuration
logging:
  level: "INFO"
  format: "[%(levelname)s] %(message)s"
```

### Environment Variables

The framework requires API credentials and supports additional environment variables for configuration:

#### Required API Configuration

Specula+ currently supports **Claude (Anthropic)** and **Deepseek** APIs. You must configure one of the following:

**For Claude API:**
```bash
export ANTHROPIC_API_KEY="your_anthropic_api_key_here"
```

**For Deepseek API:**
```bash
export DEEPSEEK_API_KEY="your_deepseek_api_key_here"
```

#### Optional Environment Variables

```bash
# Trace validation
export TRACE_PATH=path/to/trace.ndjson

# TLA+ tools path override
export TLA_TOOLS_PATH=lib/tla2tools.jar

# API base URL override (if using custom endpoints)
export ANTHROPIC_BASE_URL="https://api.anthropic.com"
export DEEPSEEK_BASE_URL="https://api.deepseek.com"
```

#### Configuration Priority

The framework uses the following priority order for API configuration:
1. Environment variables (highest priority)
2. `config.yaml` file settings
3. Default values (lowest priority)

#### API Provider Selection

Configure your preferred API provider in `config.yaml`:

```yaml
llm:
  # For Claude
  base_url: "https://api.anthropic.com"
  model: "claude-3-5-sonnet-20241022"
  
  # For Deepseek
  # base_url: "https://api.deepseek.com"
  # model: "deepseek-chat"
```

### Debug Mode

Enable verbose logging for detailed diagnostic information:

```bash
python3 -m src.core.iispec_generator input.go output/ --log-level DEBUG
```

### Validation Commands

Verify setup and configuration:

```bash
# Test TLA+ tools
java -cp lib/tla2tools.jar tla2sany.SANY --help

# Validate configuration
python3 -c "from src.utils.config import get_config; print(get_config())"

# Test LLM connection
python3 -c "from src.llm.client import get_llm_client; client = get_llm_client(); print(client.model)"
```

For additional support, refer to the main README.md file or check the project's issue tracker.
