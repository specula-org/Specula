# TLAGEN: A Framework for Generating High-Quality TLA+ Specifications from Source Code

This document provides an overview of the TLAGEN framework, a pipeline for generating, correcting, and analyzing TLA+ specifications derived directly from source code.

We will use the Go implementation of the Raft consensus algorithm from `etcd` as a running example to demonstrate the workflow, from raw source code to a high-quality, validated specification.

## Quick Setup

### Prerequisites

- **Java 8+** (for TLA+ tools)
- **Python 3.8+** 
- **Go 1.18+** (for etcd example)
- **Linux/macOS** (tested on Ubuntu 20.04+)

### One-Step Setup

```bash
# Clone and setup everything
bash scripts/setup.sh
```

The setup script will:
- Install required Python packages
- Download TLA+ tools (tla2tools.jar, CommunityModules-deps.jar)
- Verify Java installation
- Set up the environment

## Configuration

TLAGEN uses a global configuration file `config.yaml` to control the framework behavior:

```yaml
# LLM Model Configuration
llm:
  base_url: "https://api.openai.com"
  model: "claude-opus-4-20250514"  # Options: claude-3-5-sonnet-20241022, etc.
  max_tokens: 32000
  temperature: 0.1
  timeout: 3000
  use_streaming: true

# TLA+ Validator Configuration
tla_validator:
  tools_path: "lib/tla2tools.jar"
  timeout: 30

# Generation Configuration
generation:
  max_correction_attempts: 3
  mode: "draft-based"  # "direct" or "draft-based"
  
# Path Configuration
paths:
  prompts_dir: "src/prompts"
  output_dir: "output"
  
# Logging Configuration
logging:
  level: "INFO"
  format: "[%(levelname)s] %(message)s"
```

**Key sections:**
- `llm`: LLM API configuration for Steps 1, 2, 4 (spec generation and correction)
- `tla_validator`: TLA+ tools configuration for syntax and runtime validation
- `generation`: Control generation behavior and error correction attempts
- `paths`: Directory paths for prompts and outputs
- `logging`: Debug and logging settings

## The Pipeline: From Etcd Code to a Validated Specification

The framework follows a multi-step process to progressively refine the TLA+ specification.

### Step 1: Initial Intermediate Specification (IISpec) Generation

This is the first step, where we translate source code into an initial TLA+ specification.

*   **Process**: The `iispec_generator` script uses an LLM to perform a "reverse formalization," converting the logic from the source code into an imperative, intermediate TLA+ specification (IISpec).
*   **Input**: Go source code for Raft (`examples/etcd/source/raft.go`).
*   **Output**: An initial TLA+ specification (`examples/etcd/spec/step1/Raft.tla`).
*   **Command**:
```bash
    # Ensure the output directory exists
    mkdir -p examples/etcd/spec/step1/

    # Generate the initial specification from the source code
    python3 -m src.core.iispec_generator examples/etcd/source/raft.go examples/etcd/spec/step1/ --mode draft-based
```

### Step 2: Automated Syntax Correction

The initial specification often contains syntax errors. This step automatically fixes them.

*   **Process**: The generation script from Step 1 has a built-in correction loop. It repeatedly uses the TLA+ SANY parser to find syntax errors and leverages a simple Retrieval-Augmented Generation (RAG) mechanism to fix them. The process continues until the specification is syntactically valid.
*   **Input**: The initial, potentially erroneous `Raft.tla` generated internally during Step 1.
*   **Output**: A syntactically valid `examples/etcd/spec/step1/Raft.tla`.
*   **Command**: This step is automatically integrated into the command from Step 1. The final file `examples/etcd/spec/step2/Raft.tla` is the result of this correction process.

### Step 3: Control Flow Analysis (CFA) Transformation

This step converts the imperative-style IISpec into a standard, structured TLA+ specification.

*   **Process**: The CFA tool parses the imperative control flow (e.g., labels, gotos) in the IISpec and transforms it into a declarative, state-based TLA+ format (`StructSpec`).
*   **Input**: The syntactically valid IISpec (`examples/etcd/spec/step2/Raft.tla`).
*   **Output**: A structured TLA+ specification (`examples/etcd/spec/step3/Raft.tla`).
A trace configuration file (`examples/etcd/spec/step2/raft_config.yaml`) describing the specification structure.
*   **Command**:
```bash
    # Run the CFA transformation script.
    ./tools/cfa/run.sh examples/etcd/spec/step2/Raft.tla examples/etcd/spec/step3/Raft.tla
```
*   **Note**: The CFA transformation tool is a work in progress. Its parser is not yet fully robust and may require manual adjustments to the input specification to run successfully. This will be improved in future work.

### Step 4: Agent-based Runtime Correction

This step automatically detects and fixes runtime errors in TLA+ specifications using model checking.

*   **Process**: The `runtime_corrector` script generates a TLC configuration file, runs the TLC model checker to detect runtime errors, and uses LLM-based correction to iteratively fix the specification until all errors are resolved.
*   **Input**: A syntactically valid TLA+ specification (e.g., `examples/etcd/spec/step3/Raft.tla` from Step 3).
*   **Output**: 
    - A TLC configuration file (`examples/etcd/spec/step4/Raft.cfg`)
    - A runtime-corrected TLA+ specification (`examples/etcd/spec/step4/Raft.tla`)
*   **Command**:
```bash
    # Run agent-based runtime correction
    python3 -m src.core.runtime_corrector examples/etcd/spec/step3/Raft.tla examples/etcd/spec/step4/
```

### Step 5: Trace Validation Framework

This step generates trace validation drivers that can validate TLA+ specifications against execution traces from the original system.

#### Step 5.1: Trace Validation Driver Generation

*   **Process**: The `trace_generator` script generates specialized TLA+ modules that can accept and validate execution traces. It takes a configuration file describing the spec's structure (constants, variables, and actions) and automatically generates the trace validation driver files.
*   **Input**: A trace configuration file (`examples/etcd/spec/step5/raft_config.yaml`) describing the specification structure.
*   **Output**: 
    - Trace validation TLA+ specification (`examples/etcd/spec/step5/spec/specTrace.tla`)
    - Trace validation TLC configuration file (`examples/etcd/spec/step5/spec/specTrace.cfg`)
*   **Command**:
```bash
    # Generate trace validation driver from configuration
    python3 -m src.core.trace_generator examples/etcd/spec/step5/raft_config.yaml examples/etcd/spec/step5/spec/
```

#### Step 5.2: Automated Instrumentation

*   **Process**: The `instrumentation` script automatically instruments the original source code to inject trace collection points. It supports multiple programming languages (Go, Python, Rust) and uses template-based code injection to generate execution traces that can be consumed by the trace validation driver generated in Step 5.1.
*   **Input**: 
    - Original source code (`examples/etcd/source/raft.go`)
    - Configuration file (`examples/etcd/config/raft_config.yaml`) mapping TLA+ actions to source functions
    - Language-specific instrumentation template (`templates/instrumentation/go_trace_stub.template`)
*   **Output**: 
    - Instrumented source code (`examples/etcd/output/instrumented_raft.go`)
    - System execution traces (`examples/etcd/runners/raft_simulator/raft_trace.ndjson`)
*   **Commands**:
```bash
    # Step 5.2a: Instrument the source code
    python3 -m src.core.instrumentation \
        examples/etcd/config/raft_config.yaml \
        examples/etcd/source/raft.go \
        --output examples/etcd/output/instrumented_raft.go \
        --verbose

    # Step 5.2b: Run instrumented system to generate traces
    cd examples/etcd/runners/raft_simulator
    go run main.go

    # Step 5.2c: Convert system traces to TLA+ format
    cd examples/etcd
    python3 scripts/trace_converter.py \
        runners/raft_simulator/raft_trace.ndjson \
        spec/step5/spec/trace.ndjson \
        --servers n1 n2 n3

    # Step 5.2d: Validate traces with TLA+ model checker
    cd spec/step5/spec
    export TRACE_PATH=trace.ndjson
    java -cp "../../../lib/tla2tools.jar" tlc2.TLC \
        -config specTrace.cfg specTrace.tla
```

#### Complete Workflow Example

For a complete demonstration of the entire pipeline:

```bash
# Quick instrumentation test
cd examples/etcd
bash scripts/run_instrumentation_test.sh

# Full workflow with TLA+ verification
bash scripts/run_full_test_with_verification.sh
```

## Project Structure

```
tlagen/
├── src/core/                    # Core framework modules
│   ├── iispec_generator.py      # Step 1: Initial spec generation
│   ├── processor.py             # Step 2: Syntax correction (integrated)
│   ├── runtime_corrector.py     # Step 4: Runtime error correction
│   ├── trace_generator.py       # Step 5.1: Trace validation driver
│   └── instrumentation.py       # Step 5.2: Code instrumentation
├── templates/instrumentation/   # Language-specific templates
│   ├── go_trace_stub.template   # Go instrumentation template
│   ├── python_trace_stub.template
│   └── rust_trace_stub.template
├── examples/etcd/              # Complete etcd example
│   ├── config/raft_config.yaml # Configuration file
│   ├── source/raft.go          # Original source code
│   ├── output/                 # Instrumented code output
│   ├── runners/raft_simulator/ # Test runner
│   ├── spec/step1-5/           # Generated TLA+ specifications
│   └── scripts/                # Automation scripts
├── tools/cfa/                  # Step 3: Control flow analysis
├── lib/                        # TLA+ tools (auto-downloaded)
│   ├── tla2tools.jar
│   └── CommunityModules-deps.jar
└── scripts/setup.sh            # Environment setup
```
