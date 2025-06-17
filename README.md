# TLAGEN: TLA+ Generation and Analysis System

A professional, modular system for TLA+ specification generation, control flow analysis, and RAG-enhanced error correction.

## Project Overview

This project consists of multiple phases that work together to provide a comprehensive TLA+ development and analysis pipeline:

1. **Phase 1**: LLM Generation Tool (TODO)
2. **Phase 2**: CFA (Control Flow Analysis) Transformation Tool
3. **Phase 3**: RAG Error Correction System  
4. **Phase 4**: Trace Validation Tool (TODO)

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

1. Set execution permission for the script:
```bash
chmod +x tools/cfa/run.sh
```

2. Execute the following command in your terminal:

```bash
# Usage: ./tools/cfa/run.sh <input-file> <output-file>
./tools/cfa/run.sh tools/cfa/input/example/test_input.tla output/test_output.tla
```
This script automates two main actions:

1. It invokes Maven (mvn package) to compile the Java source and package it into a self-contained, executable JAR file.
2. It then runs the newly created JAR, passing the specified input and output file paths as arguments.

### 3. Expected Output
After running the command, you will see build logs from Maven, followed by a confirmation message from the script:
```
=== [Phase 2] CFA Transformation successful. ===
Output written to: output/test_output.tla
```
The transformed specification will be available at the specified output path.

### 4. Example Results
For quick reference, you can find example transformation results in the `tools/cfa/output` directory. These examples demonstrate the tool's capabilities and can be used as a reference for expected output formats.

To view the example results:
```bash
# View example output
cat tools/cfa/output/test_output.tla
```

### Reproducing the `etcd` Transformation

To replicate the conversion of the `etcd` case study from its Imperative-style Specification (`IISpec`) to the corresponding Structured Specification (`StructSpec`), execute the command below from the project's root directory.

```bash
./tools/cfa/run.sh tools/cfa/input/etcd/etcd.tla output/etcd_transformed.tla
```

## Phase 3: RAG Error Correction System

A professional, modular system that integrates TLA+ action completion with RAG-enhanced error correction. The system automatically extracts TLA+ actions from YAML files, completes missing definitions, validates specifications, and performs intelligent error correction using retrieval-augmented generation.

### 1. Project Structure

```
TLAGEN/
├── src/                          # Main source code
│   ├── core/                     # Core business logic
│   ├── llm/                      # LLM client and API handling
│   ├── rag/                      # RAG retrieval system
│   ├── tla/                      # TLA+ processing utilities
│   ├── utils/                    # Configuration and utilities
│   └── __main__.py              # Main entry point
├── data/                         # Input data, prompts, knowledge base
├── tools/                        # External tools (CFA, etc.)
├── scripts/                      # Setup and utility scripts
├── tests/                        # Test code
├── docs/                         # Documentation
├── config.yaml                  # Main configuration file
└── requirements.txt              # Python dependencies
```

### 2. Prerequisites

Ensure the following software is installed and available in your system:

*   **Python**: Version 3.8 or higher
*   **TLA+ SANY Tools**: For specification validation
*   **DeepSeek API Key**: For LLM-based error correction (optional for validation-only mode)

You can verify Python installation by running `python3 --version`.

### 3. Quick Start

**Step 1: Environment Setup**

1. Navigate to the project root directory:
```bash
cd TLAGEN
```

2. Set up the environment:
```bash
chmod +x scripts/setup.sh
./scripts/setup.sh
```

3. Set your API key (optional, but recommended for full functionality):
```bash
export DEEPSEEK_API_KEY=your_api_key_here
```

4. Check environment configuration:
```bash
python3 -m src --check-env
```

**Step 2: Run the System**

For simple correction mode (recommended for first-time users):
```bash
# Usage: python3 -m src <input-file> <output-directory> <mode>
python3 -m src data/example_input.yaml output simple
```

For comprehensive experiment comparison:
```bash
python3 -m src data/example_input.yaml output experiments
```

### 4. Command Line Options

The system supports both positional and named arguments:

```bash
# Positional arguments (recommended)
python3 -m src input.yaml output_dir simple

# Named arguments (alternative)
python3 -m src --input input.yaml --output output_dir --mode simple

# With custom configuration
python3 -m src input.yaml output_dir simple --config custom_config.yaml

# Set log level
python3 -m src input.yaml output_dir simple --log-level DEBUG

# Environment check
python3 -m src --check-env
```

### 5. Expected Output

After running the simple mode command, you will see structured processing logs:

```
[INFO] Starting simple mode...
[INFO] Processing actions from YAML file...
[INFO] Generated 4 action files
[INFO] Completing action files...
[INFO] Validating and correcting specifications...
[INFO] Simple mode finished successfully.
[INFO] Statistics: {
  "total": 4,
  "passed": 4,
  "failed": 0,
  "success_rate": 1.00
}
```

The generated TLA+ specifications will be available in the specified output directory, along with detailed statistics in `stats.json`.


## Phase 4: Trace Validation Tool

TODO
