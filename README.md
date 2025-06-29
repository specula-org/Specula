# Specula: A Framework for Synthesizing High-Quality TLA+ Specifications from Source Code

Specula is an automated framework for synthesizing TLA+ specifications that accurately describe the core logic and behavior of a software system implementation. Specula generates the specifications **directly from source code** and it **automatically validates the conformance** of specifications with the source code. The synthesized TLA+ specification can be used for formal verification of the system designs and for model-driven testing of the implementation.

Specula leverages Large Language Models (LLMs) during the synthesis. We use claude-opus-4.0; the model is configurable (see [Configuration](https://github.com/specula-org/Specula?tab=readme-ov-file#configuration))

Specula is implemented as a multi-step workflow.

1. **Code-to-Spec Translation.** Specula uses LLMs to translate source code into the TLA+ format, referred to as “translated spec”, which captures the logical structure of the source code. Note that the translated spec is not a typical specification, but an intermediate representation for subsequent transformation.
   - **1.1 Syntax Correction.** The translated spec may contain syntax errors and thus fail compilation. Specula uses a Retrieval-Augmented Generation (RAG) mechanism to automatically detect and fix compilation errors. Specula includes a specialized knowledge base that encodes TLA+ syntax knowledge and error patterns.
2. **TLA+ Spec Transformation.** Specula transforms the translated spec into structured, declarative TLA+ specs that are suitable for model checking and formal verification. Specula performs a customized control-flow analysis that transforms the imperative translated spec into the corresponding declarative TLA+ spec
3. **Error Correction.** The TLA+ spec output from Step 2 may not be perfect. Specula employs tools to automatically detect and correct errors by attempting to run TLC-based model checking on the TLA+ spec. Any runtime error will be automatically fixed by Specula. 
4. **Trace Validation.** Specula ensures that the synthesized TLA+ specs conforms with the source code to avoid model-code gaps. It automatically instruments the code during Step 2 (when translating code into the TLA+ format). Specula includes a deterministic execution engine to generate code-level traces which are used to validate the model-level traces and ensure their conformance.

The following figure illustrates the above workflow.

![Specula Workflow](docs/images/diagram.png)

We have used Specula to synthesize the TLA+ specifications of [etcd’s Raft implementation](https://github.com/etcd-io/raft/blob/main/raft.go) (written in Go) and Asterinas’s [SpinLock implementation](https://github.com/asterinas/asterinas/blob/main/ostd/src/sync/spin.rs) (written in Rust). We are actively using Specula to synthesize more TLA+ specifications from source code.

## Setup

### Prerequisites

- **Java 11+** (for TLA+ tools)
- **Python 3.8+** 
- **Go 1.18+** (for etcd example)
- **Linux/macOS** (tested on Ubuntu 20.04+)

### Push-Button Installation

```bash
# Clone and setup everything
bash scripts/setup.sh
```

The setup script will:
- Install required Python packages
- Download TLA+ tools (tla2tools.jar, CommunityModules-deps.jar)
- Verify Java installation
- Set up the environment

### Configuration

Specula uses a global configuration file `config.yaml` to control the framework behavior:

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
...
```

**Key sections:**
- `llm`: LLM API configuration for Steps 1, 2, 4 (spec generation and correction)
- `tla_validator`: TLA+ tools configuration for syntax and runtime validation
- `generation`: Control generation behavior and error correction attempts
- `paths`: Directory paths for prompts and outputs
- `logging`: Debug and logging settings

## Usage

For detailed usage instructions, command-line options, and comprehensive examples of each component, please refer to the [Usage Documentation](docs/Usage.md). The usage guide provides step-by-step instructions for all five pipeline stages and configuration management tips.

## Demo

We present an end-to-end demonstration of how to use Specula to generate TLA+ specification for etcd’s Raft implementation (in Go).

### 0. Configure your API:
```
export ANTHROPIC_API_KEY=YOUR_API_KEY
```

### 1. Code-to-Spec Translation

*   **Process**: The `iispec_generator` script uses an LLM to perform a "reverse formalization," converting the logic from the source code into an imperative, intermediate TLA+ specification (IISpec).
*   **Input**: Go source code for Raft (`examples/etcd/source/raft.go`).
*   **Output**: 
    - An initial TLA+ specification (`output/etcd/spec/step1/Raft.tla`).
    - A draft (`output/etcd/spec/step1/draft_analysis.txt`)
*   **Command**:
```bash
    # Generate the initial specification from the source code 
    ./specula iispec_generator examples/etcd/source/raft.go output/etcd/spec/step1/ --mode draft-based
```

### 1.1 Syntax Correction

*   **Process**: The generation script from Step 1 has a built-in correction loop. It repeatedly uses the TLA+ SANY parser to find syntax errors and leverages a simple Retrieval-Augmented Generation (RAG) mechanism to fix them. The process continues until the specification is syntactically valid.
*   **Input**: The initial, potentially erroneous `Raft.tla` generated internally during Step 1.
*   **Output**: A syntactically valid `output/etcd/spec/step1/Raft.tla`.
*   **Command**: This step is automatically integrated into the command from Step 1. The final file `examples/etcd/spec/step2/Raft.tla` is the result of this correction process.
*   **Note**: For highly complex specifications or when using models with limited capabilities, the iterative correction process may not achieve full success, requiring manual intervention.

### 2. TLA+ Specification Transformation

*   **Process**: The CFA tool parses the imperative control flow (e.g., labels, gotos) in the IISpec and transforms it into a declarative, state-based TLA+ format (`StructSpec`).
*   **Input**: The syntactically valid IISpec (`examples/etcd/spec/step2/Raft.tla`).
*   **Output**: A structured TLA+ specification (`output/etcd/spec/step3/Raft.tla`).
*   **Command**:
```bash
    # Run the CFA transformation script.
    ./tools/cfa/run.sh tools/cfa/input/example/Raft.tla output/etcd/spec/step3/Raft.tla
```
*   **Note**: The CFA transformation tool is a work in progress. Its parser is not yet fully robust and may require manual adjustments to the input specification to run successfully. This will be improved in future work.

### 3. Agent-based Error Correction

*   **Process**: The `runtime_corrector` script generates a TLC configuration file, runs the TLC model checker to detect runtime errors, and uses LLM-based correction to iteratively fix the specification until all errors are resolved.
*   **Input**: A syntactically valid TLA+ specification (e.g., `examples/etcd/spec/step3/Raft.tla` from Step 3).
*   **Output**: 
    - A TLC configuration file (`output/etcd/spec/step4/Raft.cfg`)
    - A runtime-corrected TLA+ specification (`output/etcd/spec/step4/Raft.tla`)
*   **Command**:
```bash
    # Run agent-based runtime correction
    ./specula runtime_corrector examples/etcd/spec/step3/Raft.tla output/etcd/spec/step4/
```
*   **Note**: For highly complex specifications or when using models with limited capabilities, the iterative correction process may not achieve full success, requiring manual intervention.

### 4. Trace Validation

Generate specialized TLA+ modules (`specTrace.tla` and `specTrace.cfg`) that can validate execution traces against the synthesized spec. The `spectrace_generator.py` script orchestrates this:

#### Configuration Generation

*   **Process**: The script uses an LLM to analyze the TLA+ specification from the previous step, automatically generating a YAML configuration file that describes the spec's structure (constants, variables, actions, and interactions). This configuration is then used to create the final trace validation driver.
*   **Input**: The runtime-corrected specification from Step 4 (`examples/etcd/spec/step4/Raft.tla` and `Raft.cfg`).
*   **Output**:
    - An automatically generated trace configuration file (`output/etcd/spec/step5/raft_config.yaml`).
    - Trace validation TLA+ specification (`output/etcd/spec/step5/spec/specTrace.tla`).
    - Trace validation TLC configuration file (`output/etcd/spec/step5/spec/specTrace.cfg`).
*   **Command**:
```bash
    # Auto-generate config and then the trace validation driver
    ./specula spectrace_generator \
        --tla examples/etcd/spec/step4/Raft.tla \
        --cfg examples/etcd/spec/step4/Raft.cfg \
        --auto-config output/etcd/spec/step5/raft_config.yaml \
        output/etcd/spec/step5/spec/
```
#### Instrumentation

*   **Process**: The `instrumentation` script automatically instruments the original source code to inject trace collection points. It supports multiple programming languages (Go, Python, Rust) and uses template-based code injection to generate execution traces that can be consumed by the trace validation driver generated in Step 5.1.
*   **Input**: 
    - Original source code from [etcd/raft repository](https://github.com/etcd-io/raft.git)
    - Configuration file (`examples/etcd/config/raft_config.yaml`) mapping TLA+ actions to source functions
    - Language-specific instrumentation template (`templates/instrumentation/go_trace_stub.template`)
*   **Output**: 
    - Instrumented source code (`examples/etcd/output/instrumented_raft.go`)
    - System execution traces (`examples/etcd/runners/raft_simulator/raft_trace.ndjson`)
*   **Commands**:
```bash
    # Step 5.2a: Instrument the source code
    ./specula instrumentation \
        examples/etcd/config/raft_config.yaml \
        examples/etcd/source/raft.go \
        --stub-template templates/instrumentation/go_trace_stub.template \
        --output examples/etcd/output/instrumented_raft.go \
        --verbose
    # Step 5.2b: Run instrumented system to generate traces
    cd examples/etcd/runners/raft_simulator
    go run main.go
    # Step 5.2c: Convert system traces to TLA+ format
    cd ../..
    python3 scripts/trace_converter.py \
        runners/raft_simulator/raft_trace.ndjson \
        spec/step5/spec/trace.ndjson \
        --servers n1 n2 n3
    # Step 5.2d: Validate traces with TLA+ model checker
    cd spec/step5/spec
    export TRACE_PATH=trace.ndjson
    java -cp "../../../../../lib/tla2tools.jar" tlc2.TLC \
        -config specTrace.cfg specTrace.tla
```

#### Putting It All Together 

```bash
cd examples/etcd
bash scripts/run_full_test_with_verification.sh  # Will auto-clone if needed
```

### Final Output

We put a generated TLA+ specification for etcd's Raft implementation at [Raft.tla](examples/etcd/spec/step5/spec/Raft.tla).
You can generate yourself!

