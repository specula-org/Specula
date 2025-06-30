## ETCD Example

We present an end-to-end demonstration of how to use Specula to generate TLA+ specification for etcd’s Raft implementation (in Go).

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
    ./specula iispec_generator examples/etcd/source/raft.go output/etcd/spec/step1/ --mode draft-based
```

### 1.a Syntax Correction

*   **Input**. The translated `Raft.tla` generated from last step.
*   **Output**. A syntactically correct `output/etcd/spec/step1/corrected_spec/Raft.tla`.
This step is integrated in the command of Step 1. The final file `examples/etcd/spec/step1/corrected_spec/Raft.tla` is the output.
*   **Note**: This step may need manual effort to fix syntax errors (e.g., for highly complex specifications or weak models).

### 2. TLA+ Specification Transformation

*   **Input**. The translated spec  (`examples/etcd/spec/step1/Raft.tla`).
*   **Output**. A structured TLA+ specification (`output/etcd/spec/step2/Raft.tla`).
```bash
    ./tools/cfa/run.sh tools/cfa/input/example/Raft.tla output/etcd/spec/step2/Raft.tla
```
*   **Note**. The CFA transformation tool is a work in progress. Its parser is not yet fully robust and may require manual adjustments to the input specification to run successfully. This will be improved in future work.

### 3. Runtime Error Correction

*   **Input**. A TLA+ specification (e.g., `examples/etcd/spec/step2/Raft.tla` from Step 2).
*   **Output**.
    - A TLC configuration file (`output/etcd/spec/step3/Raft.cfg`)
    - A runtime-corrected TLA+ specification (`output/etcd/spec/step3/Raft.tla`)
```bash
    ./specula runtime_corrector examples/etcd/spec/step2/Raft.tla output/etcd/spec/step3/
```
*   **Note**: This step may need manual effort to fix syntax errors (e.g., for highly complex specifications or weak models).

### 4. Trace Validation

Generate TLA+ modules (`specTrace.tla` and `specTrace.cfg`) to validate execution traces against the synthesized TLA+ spec. 

#### Configuration Generation

*   **Input**. The TLA+ specification from Step 3 (`examples/etcd/spec/step3/Raft.tla` and `Raft.cfg`).
*   **Output**.
    - An automatically generated trace configuration file (`output/etcd/spec/step4/raft_config.yaml`).
    - Trace validation TLA+ specification (`output/etcd/spec/step4/spec/specTrace.tla`).
    - Trace validation TLC configuration file (`output/etcd/spec/step4/spec/specTrace.cfg`).
```bash
    ./specula spectrace_generator \
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
    ./specula instrumentation \
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

The final, high-quality specification for etcd's Raft implementation, which has been refined through all the steps above, can be found at [Raft.tla](spec/step5/spec/Raft.tla).

