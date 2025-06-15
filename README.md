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

1. Set execution permission for the script:
```bash
chmod +x phase_2_cfa_transformation/run.sh
```

2. Execute the following command in your terminal:

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

### 4. Example Results
For quick reference, you can find example transformation results in the `example_result` directory. These examples demonstrate the tool's capabilities and can be used as a reference for expected output formats.

To view the example results:
```bash
# View example output
cat example_result/test_output.tla
```

### Reproducing the `etcd` Transformation

To replicate the conversion of the `etcd` case study from its Imperative-style Specification (`IISpec`) to the corresponding Structured Specification (`StructSpec`), execute the command below from the project's root directory.

```bash
./phase_2_cfa_transformation/run.sh data/iispec/etcd/etcd.tla results/structspec/etcd.tla
```

## Phase 3: RAG Error Correction Tool

This part of the project is a comprehensive system that integrates action completion with RAG-based error correction for TLA+ specifications. It can automatically extract TLA+ actions from YAML files, complete missing variable and function definitions, validate specifications, and perform error correction using RAG-enhanced LLM.

### 1. Prerequisites

Ensure the following software is installed and available in your system:

*   **Python**: Version 3.8 or higher.
*   **TLA+ SANY Tools**: For specification validation.
*   **DeepSeek API Key**: For LLM-based error correction (optional for validation-only mode).

You can verify Python installation by running `python3 --version`.

### 2. How to Run

The tool provides both simple correction mode and comprehensive experiment comparison mode.

**Step 1: Environment Setup**

1. Navigate to the phase 3 directory:
```bash
cd phase_3_rag_correction
```

2. Set up the environment:
```bash
chmod +x setup.sh
./setup.sh
```

3. Set your API key (optional, but recommended for full functionality):
```bash
export DEEPSEEK_API_KEY=your_api_key_here
```

4. Check environment configuration:
```bash
python3 main.py --check-env
```

**Step 2: Run the Tool**

For simple correction mode (recommended for first-time users):
```bash
# Usage: python3 main.py <input-file> <output-directory> <mode>
python3 main.py input/example_input.yaml output simple
```

For comprehensive experiment comparison:
```bash
python3 main.py input/example_input.yaml output experiments
```

### 3. Expected Output

After running the simple mode command, you will see processing logs followed by a completion summary:
```
[START] Running simple mode (action completion + RAG correction)...
[STEP 1] Processing actions from YAML file...
         Generated 4 action files
[STEP 2] Completing action files...
         [OK] Completed: Increment.tla
         [OK] Completed: AddToQueue.tla
         [OK] Completed: ProcessQueue.tla
         [OK] Completed: Action.tla
[STEP 3] Validating TLA+ files and performing RAG correction...
         [OK] Validation passed: Increment.tla
         [FIXING] Attempting RAG correction: Action.tla
         [OK] Correction successful: Action.tla
[COMPLETE] Simple mode finished!
           Total actions: 4
           Completed files: 4
           Validation passed: 4
           Total success rate: 100.00%
```

The generated TLA+ specifications will be available in the `output/` directory, along with detailed statistics in `output/stats.json`.

### 4. Example Results

For quick reference, you can examine the generated output structure:

```bash
# View generated TLA+ files
ls output/example_input_actions/

# Check processing statistics
cat output/stats.json

# View detailed logs (if any errors occurred)
ls output/logs/
```

### 5. Input Format

The tool expects YAML files with TLA+ code snippets in the following format:

```yaml
code:
  - |
    Increment == 
        /\ counter < 100
        /\ counter' = counter + 1
        /\ UNCHANGED <<status, queue>>
  
  - |
    AddToQueue(item) == 
        /\ Len(queue) < 10
        /\ queue' = Append(queue, item)
        /\ UNCHANGED <<counter, status>>
```

### 6. Modes Explained

**Simple Mode**: 
- Extracts TLA+ actions from YAML
- Automatically completes variable and function definitions
- Validates specifications using TLA+ SANY
- Performs RAG-enhanced error correction if needed
- Suitable for individual file processing and debugging

**Experiments Mode**:
- Runs three comparative experiments:
  1. Baseline compilation test
  2. Baseline correction  
  3. RAG-enhanced correction
- Generates detailed comparison reports
- Suitable for research and methodology evaluation

### Reproducing the Example Transformation

To process the provided example and see the complete action completion and error correction workflow:

```bash
cd phase_3_rag_correction
python3 main.py input/example_input.yaml output simple
```

This will demonstrate the system's ability to:
- Extract 4 TLA+ actions from the YAML input
- Automatically add missing MODULE headers, EXTENDS statements, and VARIABLES declarations
- Validate each generated specification
- Apply RAG-based correction for any syntax or semantic errors
- Generate a comprehensive statistics report

## Phase 4: Trace Validation Tool

TODO