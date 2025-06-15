# README

## Phase 1: LLM Generation Tool

TODO

## Phase 2: CFA Transformation Tool

This part of the project is a command-line tool that performs Control Flow Analysis (CFA) on a TLA+ specification and transforms it into a structured format.

### 1. Prerequisites

Ensure the following software is installed and available in your system's PATH:

*   **Java Development Kit (JDK)**: Version 11 or higher.
*   **Apache Maven**: Version 3.6 or higher.

You can verify their installation by running `java -version` and `mvn -version`.

### 2. How to Run

The tool can be built and executed using a single script from the project's root directory.

**Step 1: Build and Run the Tool**

Execute the following command in your terminal:

```bash
# Usage: ./phase_2_cfa_transformation/run.sh <input-file> <output-file>
./phase_2_cfa_transformation/run.sh data/iispec/example/test_input.tla results/structspec/test_output.tla
```
This script automates two main actions:

1. It invokes Maven (mvn package) to compile the Java source and package it into a self-contained, executable JAR file.
2. It then runs the newly created JAR, passing the specified input and output file paths as arguments.

### 3. Expected Output
After running the command, you will see build logs from Maven, followed by a confirmation message from the script:
```
=== [Phase 2] CFA Transformation successful. ===
Output written to: results/structspec/test_output.tla
```
The transformed specification will be available at the specified output path.

### Reproducing the `etcd` Transformation

To replicate the conversion of the `etcd` case study from its Imperative-style Specification (`IISpec`) to the corresponding Structured Specification (`StructSpec`), execute the command below from the project's root directory.

```bash
./phase_2_cfa_transformation/run.sh data/iispec/etcd/etcd.tla results/structspec/etcd.tla
```

## Phase 3: RAG Correction Tool

TODO

## Phase 2: CFA Transformation Tool

TODO