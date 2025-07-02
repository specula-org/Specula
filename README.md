# Specula: A Framework for Synthesizing High-Quality TLA+ Specifications from Source Code

Specula is an automated framework for synthesizing TLA+ specifications that accurately describe the core logic and behavior of a software system implementation. Specula generates the specifications **directly from source code** and it **automatically validates the conformance** of specifications with the code. The synthesized TLA+ specification can be used for formal verification of the system designs and for model-driven testing of the implementation.

Specula leverages Large Language Models (LLMs) for synthesis. 
We currently use claude-opus-4.0 and claude-sonnet-4.0 (the model can be [configured](https://github.com/specula-org/Specula?tab=readme-ov-file#configuration)).

Specula is implemented as a multi-step workflow.

1. **Code-to-Spec Translation.** Specula uses LLMs to translate source code into the TLA+ format, referred to as “translated spec”, which captures the logical structure of the source code. Note that the translated spec is not a typical specification, but an intermediate representation for subsequent transformation.
   - **1.a Syntax Correction.** The translated spec may contain syntax errors and thus fail compilation. Specula uses a Retrieval-Augmented Generation (RAG) mechanism to automatically detect and fix compilation errors. Specula includes a specialized knowledge base that encodes TLA+ syntax knowledge and error patterns.
2. **TLA+ Spec Transformation.** Specula transforms the translated spec into structured, declarative TLA+ specs that are suitable for model checking and formal verification. Specula performs a customized control-flow analysis that transforms the imperative translated spec into the corresponding declarative TLA+ spec
3. **Error Correction.** The TLA+ spec output from Step 2 may not be perfect. Specula employs tools to automatically detect and correct errors by attempting to run TLC-based model checking on the TLA+ spec. Any runtime error will be automatically fixed by Specula. 
4. **Trace Validation.** Specula ensures that the synthesized TLA+ specs conforms with the source code to avoid model-code gaps. It automatically instruments the code. Specula includes a deterministic execution engine to generate code-level traces which are used to validate the model-level traces and ensure their conformance.

The following figure illustrates the above workflow.

![Specula Workflow](docs/images/diagram.png)

We have used Specula to synthesize the TLA+ specifications of [etcd’s Raft implementation](https://github.com/etcd-io/raft/blob/main/raft.go) (written in Go) and Asterinas’s [SpinLock implementation](https://github.com/asterinas/asterinas/blob/main/ostd/src/sync/spin.rs) (written in Rust). We are actively using Specula to synthesize more TLA+ specifications from source code.

Specula is under active development. It may require some manual effort to tweak the TLA+ specification in certain steps of the workflow during error correction (Step 1.a and 3) and trace validation (Step 4). In practice, the amount of effort is small. For example, we changed approximately 20 lines of specifications during the entire workflow. 

## Setup

### Prerequisites

* Java 11+ (for TLA+ tools)
* Python 3.8+ 
* Linux and MacOS (tested on Ubuntu 20.04+)
* Go 1.18+ (for etcd's Raft example)

**Push-Button Installation**

```bash
bash scripts/setup.sh
```

### Configuration

Specula uses a global configuration file `config.yaml`.

```yaml
# LLM model configuration
llm:
  base_url: "https://api.openai.com"
  model: "claude-opus-4-20250514"  # Options: claude-3-5-sonnet-20241022, etc.
  max_tokens: 32000
  temperature: 0.1
  timeout: 3000
  use_streaming: true

# TLA+ tools configuration for syntax and runtime validation
tla_validator:
  tools_path: "lib/tla2tools.jar"
  timeout: 30

# Generation configuration
generation:
  max_correction_attempts: 3
  mode: "draft-based"  # "direct" or "draft-based"
  
# Directories for prompts and outputs
paths:
  prompts_dir: "src/prompts"
  output_dir: "output"
  
# Debugging and logging
logging:
  level: "INFO"
  format: "[%(levelname)s] %(message)s"
...
```

## Usage

Please refer to [Usage](https://github.com/specula-org/Specula/blob/main/docs/Usage.md) for detailed usage, which provides step-by-step instructions of the workflow and configuration tips.

## Case Study (etcd Raft)

We present an end-to-end demonstration of how to use Specula to generate TLA+ specification for etcd’s Raft implementation (in Go).

<a href="https://www.youtube.com/watch?v=b-QBO860zZY" title="Click to watch the demo on YouTube">
  <img src="docs/images/specula_demo_thumbnail.png" alt="Specula Demo Video" width="750">
</a>

### 0. Configure your API:
```
export ANTHROPIC_API_KEY=YOUR_API_KEY
```

### 1. Code-to-Spec Translation

*   **Input**: Go source code for Raft (`examples/etcd/source/raft.go`).
*   **Output**: 
    - An initial TLA+ specification (`output/etcd/spec/step1/Raft.tla`).
    - A draft (`output/etcd/spec/step1/draft_analysis.txt`)
```bash
    ./specula step1 examples/etcd/source/raft.go output/etcd/spec/step1/ --mode draft-based
```

### 1.a Syntax Correction

*   **Input**. The translated `Raft.tla` generated from last step.
*   **Output**. A syntactically correct `output/etcd/spec/step1/corrected_spec/Raft.tla`.
This step is integrated in the command of Step 1.
*   **Note**: 
    - This step may need manual effort to fix syntax errors (e.g., for highly complex specifications or weak models).
    - Please ensure that the size of the input specification does not exceed the token limit.

### 2. TLA+ Specification Transformation

*   **Input**. The translated spec  (`examples/etcd/spec/step1/corrected_spec/Raft.tla`).
*   **Output**. A structured TLA+ specification (`output/etcd/spec/step2/Raft.tla`).
```bash
    ./specula step2 tools/cfa/input/example/Raft.tla output/etcd/spec/step2/Raft.tla
```
*   **Note**. The CFA transformation tool is a work in progress. Its parser is not yet fully robust and may require manual adjustments to the input specification to run successfully. This will be improved in future work.

### 3. Runtime Error Correction

*   **Input**. A TLA+ specification (e.g., `examples/etcd/spec/step2/Raft.tla` from Step 2).
*   **Output**.
    - A TLC configuration file (`output/etcd/spec/step3/Raft.cfg`)
    - A runtime-corrected TLA+ specification (`output/etcd/spec/step3/Raft.tla`)
```bash
    ./specula step3 examples/etcd/spec/step2/Raft.tla output/etcd/spec/step3/
```
*   **Note**: 
    - This step may need manual effort to fix syntax errors (e.g., for highly complex specifications or weak models).
    - Please ensure that the size of the input specification does not exceed the token limit.
### 4. Trace Validation

Generate TLA+ modules (`specTrace.tla` and `specTrace.cfg`) to validate execution traces against the synthesized TLA+ spec. 

#### Configuration Generation

*   **Input**. The TLA+ specification from Step 3 (`examples/etcd/spec/step3/Raft.tla` and `Raft.cfg`).
*   **Output**.
    - An automatically generated trace configuration file (`output/etcd/spec/step4/raft_config.yaml`).
    - Trace validation TLA+ specification (`output/etcd/spec/step4/spec/specTrace.tla`).
    - Trace validation TLC configuration file (`output/etcd/spec/step4/spec/specTrace.cfg`).
```bash
    ./specula step4.1 \
        --tla examples/etcd/spec/step3/Raft.tla \
        --cfg examples/etcd/spec/step3/Raft.cfg \
        --auto-config output/etcd/spec/step4/raft_config.yaml \
        output/etcd/spec/step4/spec/
```
#### Instrumentation

*   **Input**.
    - Original source code from [etcd/raft repository](https://github.com/etcd-io/raft.git)
    - Configuration file (`examples/etcd/config/raft_config.yaml`) mapping TLA+ actions to source functions
    - Language-specific instrumentation template (`templates/instrumentation/go_trace_stub.template`)
*   **Output**. 
    - Instrumented source code (`examples/etcd/output/instrumented_raft.go`)
    - System execution traces (`examples/etcd/runners/raft_simulator/raft_trace.ndjson`)
```bash
    # Step 4.2a: Instrument the source code
    ./specula step4.2 \
        examples/etcd/config/raft_config.yaml \
        examples/etcd/source/raft.go \
        --stub-template templates/instrumentation/go_trace_stub.template \
        --output examples/etcd/output/instrumented_raft.go \
        --verbose
    # Step 4.2b: Run instrumented system to generate traces
    cd examples/etcd/runners/raft_simulator
    go run main.go
    # Step 4.2c: Convert system traces to TLA+ format
    cd ../..
    python3 scripts/trace_converter.py \
        runners/raft_simulator/raft_trace.ndjson \
        spec/step4/spec/trace.ndjson \
        --servers n1 n2 n3
    # Step 4.2d: Validate traces with TLA+ model checker
    cd spec/step4/spec
    export TRACE_PATH=trace.ndjson
    java -cp "../../../../../lib/tla2tools.jar" tlc2.TLC \
        -config specTrace.cfg specTrace.tla
```

#### Putting It All Together 

```bash
cd examples/etcd
bash scripts/run_full_test_with_verification.sh 
```

### Final Output

We put a generated TLA+ specification for etcd's Raft implementation at [Raft.tla](examples/etcd/spec/step4/spec/Raft.tla).
You can generate yourself!

## Cost Analysis

The following table summarizes the cost breakdown for synthesizing TLA+ specifications from etcd's Raft implementation:

| Step | Sub-step | LLM Model | Input Tokens | Output Tokens | LLM Cost (USD) | Manual Effort | Total Step Cost |
|------|----------|-----------|--------------|---------------|----------------|---------------|-----------------|
| **1. Code-to-Spec Translation** | Generation | Claude-Opus-4.0 | 50,000 | 12,000 | $1.65 | 0 min | **$1.65** |
| | Syntax Correction | Claude-Sonnet-4.0 | 12,000 | 10,000 | $0.19* | < 10 min | **$0.19 * 5** |
| **2. TLA+ Transformation** | CFA Processing | None | - | - | $0.00 | < 10 min | **$0.00** |
| **3. Runtime Error Correction** | Error Fixing | Claude-Sonnet-4.0 | 10,000 | 10,000 | $0.18* | < 15 min |  **$0.18 * 5** |
| **4. Trace Validation** | Config Generation | Claude-Sonnet-4.0 | 10,000 | 700 | $0.04 | 0 min | **$0.04** |
| | Trace Validation | None | - | - | $0.00 | ~1 hours | |
| **Total** | | | **170,000** | **112,700** |  | **~1.5 hours** | **$3.54** |

**Notes:**
- *Correction costs are per iteration. Multiple iterations may be required for complex specifications.
- **LLM Pricing**: Claude-Opus-4.0 (\$15/M input, \$75/M output), Claude-Sonnet-4.0 (\$3/M input, \$15/M output)
- **Manual effort** includes syntax error fixes, consistency validation, and trace alignment
- **Total cost** represents a typical successful run; actual costs may vary based on specification complexity

**Cost Efficiency**: The entire workflow costs approximately $3.5 in LLM usage and requires approximately 1.5 hours of manual effort to generate a complete, formally verified TLA+ specification from source code.