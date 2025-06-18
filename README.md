# TLAGEN: A Framework for Generating High-Quality TLA+ Specifications from Source Code

This document provides an overview of the TLAGEN framework, a pipeline for generating, correcting, and analyzing TLA+ specifications derived directly from source code.

We will use the Go implementation of the Raft consensus algorithm from `etcd` as a running example to demonstrate the workflow, from raw source code to a high-quality, validated specification.

## The Pipeline: From Go Code to a Validated Specification

The framework follows a multi-step process to progressively refine the TLA+ specification.

### Step 1: Initial Intermediate Specification (IISpec) Generation

This is the first step, where we translate source code into an initial TLA+ specification.

*   **Process**: The `iispec_generator` script uses an LLM to perform a "reverse formalization," converting the logic from the source code into an imperative, intermediate TLA+ specification (IISpec).
*   **Input**: Go source code for Raft (`archive/systems/etcd/raft.go`).
*   **Output**: An initial TLA+ specification (`output/etcd/Raft.tla`).
*   **Command**:
    ```bash
    # Ensure the output directory exists
    mkdir -p output/etcd

    # Generate the initial specification from the source code
    python3 -m src.core.iispec_generator archive/systems/etcd/raft.go output/etcd --mode draft-based
    ```

### Step 2: Automated Syntax Correction

The initial specification often contains syntax errors. This step automatically fixes them.

*   **Process**: The generation script from Step 1 has a built-in correction loop. It repeatedly uses the TLA+ SANY parser to find syntax errors and leverages a simple Retrieval-Augmented Generation (RAG) mechanism to fix them. The process continues until the specification is syntactically valid.
*   **Input**: The initial, potentially erroneous `Raft.tla` generated internally during Step 1.
*   **Output**: A syntactically valid `output/etcd/Raft.tla`.
*   **Command**: This step is automatically integrated into the command from Step 1. The final file `output/etcd/Raft.tla` is the result of this correction process.

### Step 3: Control Flow Analysis (CFA) Transformation

This step converts the imperative-style IISpec into a standard, structured TLA+ specification.

*   **Process**: The CFA tool parses the imperative control flow (e.g., labels, gotos) in the IISpec and transforms it into a declarative, state-based TLA+ format (`StructSpec`).
*   **Input**: The syntactically valid IISpec (`output/etcd/Raft.tla`).
*   **Output**: A structured TLA+ specification (`output/etcd/Raft_transformed.tla`).
*   **Command**:
    ```bash
    # The CFA tool requires the input file to be in its specific input directory.
    cp output/etcd/Raft.tla tools/cfa/input/etcd/

    # Run the CFA transformation script.
    ./tools/cfa/run.sh tools/cfa/input/etcd/Raft.tla output/etcd/Raft_transformed.tla
    ```
*   **Note**: The CFA transformation tool is a work in progress. Its parser is not yet fully robust and may require manual adjustments to the input specification to run successfully. This will be improved in future work.

### Step 4: Agent-based Runtime Correction (TODO)

*   **Process**: This planned phase will involve an agent that uses the TLA+ model checker (TLC) to find runtime errors, such as deadlocks or invariant violations, and attempts to automatically correct the specification's logic.

### Step 5: Automated Trace Validation (TODO)

*   **Process**: The final planned phase will validate the corrected TLA+ specification against execution traces gathered from the original system. This ensures that the formal model's behavior accurately reflects the real implementation.
