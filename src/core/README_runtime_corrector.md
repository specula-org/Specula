# Runtime Corrector (Phase 4)

This script implements the Phase 4 functionality described in the main README: Agent-based Runtime Correction.

## Features

1. **Automatic TLC Configuration Generation**: Uses LLM to generate appropriate `.cfg` files for TLA+ specifications
2. **Runtime Error Detection**: Runs TLC model checker to find runtime errors (deadlocks, invariant violations, etc.)
3. **Iterative Error Correction**: Uses LLM to fix runtime errors based on TLC output
4. **Configurable Parameters**: Supports command-line overrides for model, timeouts, and correction attempts

## Usage

### Basic Usage

```bash
# Set your Anthropic API key
export ANTHROPIC_API_KEY="your_api_key_here"

# Run runtime correction on a TLA+ specification
python3 -m src.core.runtime_corrector input_spec.tla output_directory/

# Example with the Raft specification
python3 -m src.core.runtime_corrector spec/etcd/step2/RaftConsensus.tla spec/etcd/step4/
```

### Advanced Usage with Options

```bash
# Override configuration parameters
python3 -m src.core.runtime_corrector input_spec.tla output_dir/ \
    --model claude-3-5-sonnet-20241022 \
    --max-tokens 32000 \
    --temperature 0.2 \
    --max-attempts 5 \
    --tlc-timeout 120 \
    --log-level DEBUG
```

## How It Works

### Step 1: Configuration Generation
- Analyzes the input TLA+ specification
- Uses LLM with `step3_config_generation.txt` prompt to generate a `.cfg` file
- Creates only SPECIFICATION and CONSTANTS sections with appropriate small values

### Step 2: Initial TLC Run
- Runs TLC model checker on the specification with the generated configuration
- If successful, the process completes
- If errors are found, proceeds to correction

### Step 3: Iterative Error Correction
- For each error found by TLC:
  1. Uses LLM with `step4_runtime_correction.txt` prompt to fix the specification
  2. Saves the corrected version
  3. Re-runs TLC to verify the fix
  4. Continues until all errors are fixed or max attempts reached

## Output Files

The script creates several files in the output directory:

- `{ModuleName}.cfg` - Generated TLC configuration
- `{ModuleName}_initial.tla` - Copy of the input specification
- `{ModuleName}_attempt_N.tla` - Each correction attempt (if needed)
- `{ModuleName}_corrected.tla` - Final corrected specification
- `runtime_correction_summary.json` - Summary of the correction process

## Configuration

The script uses the same `config.yaml` file as other TLAGEN components. Key settings:

```yaml
llm:
  model: "claude-3-5-sonnet-20241022"
  max_tokens: 8192
  temperature: 0.1

tla_validator:
  tools_path: "lib/tla2tools.jar"
  timeout: 60

generation:
  max_correction_attempts: 3
```

## Requirements

- Python 3.7+
- `anthropic` package (`pip install anthropic`)
- `pyyaml` package (`pip install pyyaml`)
- Java runtime for TLC
- TLA+ tools (`lib/tla2tools.jar`)
- Valid Anthropic API key

## Example

```bash
# Example workflow
export ANTHROPIC_API_KEY="sk-ant-..."

# Run runtime correction
python3 -m src.core.runtime_corrector spec/etcd/step2/RaftConsensus.tla spec/etcd/step4/

# Check the results
ls spec/etcd/step4/
# Output:
# RaftConsensus.cfg
# RaftConsensus_initial.tla
# RaftConsensus_corrected.tla
# runtime_correction_summary.json
```

## Troubleshooting

### Common Issues

1. **API Key Not Found**: Set the `ANTHROPIC_API_KEY` environment variable
2. **TLA+ Tools Not Found**: Ensure `lib/tla2tools.jar` exists and is accessible
3. **Java Not Available**: Install Java runtime for TLC execution
4. **Timeout Errors**: Increase `--tlc-timeout` for complex specifications

### Debug Mode

Run with `--log-level DEBUG` to see detailed execution information:

```bash
python3 -m src.core.runtime_corrector input.tla output/ --log-level DEBUG
``` 