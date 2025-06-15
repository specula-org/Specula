# Quick Usage Guide

## Prerequisites

1. **Set API Key**:
   ```bash
   export DEEPSEEK_API_KEY=your_api_key_here
   ```

2. **Install Dependencies**:
   ```bash
   ./setup.sh
   ```

3. **Check Environment**:
   ```bash
   python3 main.py --check-env
   ```

## Basic Usage

### Simple Correction Mode

Process TLA+ code snippets and generate corrected specifications:

```bash
python3 main.py --input example_input.yaml --output ./results --mode simple
```

### Experimental Comparison Mode

Run three comparative experiments (baseline test, baseline correction, RAG correction):

```bash
python3 main.py --input example_input.yaml --output ./results --mode experiments
```

## Input Format

Create a YAML file with your TLA+ code snippets:

```yaml
code:
  - |
    Lock(p) == 
        /\ pc[p] = "lock"
        /\ mutex = FALSE
        /\ mutex' = TRUE
        /\ pc' = [pc EXCEPT ![p] = "cs"]
  
  - |
    Unlock(p) ==
        /\ pc[p] = "cs" 
        /\ mutex = TRUE
        /\ mutex' = FALSE
        /\ pc' = [pc EXCEPT ![p] = "unlock"]
```

## Output

### Simple Mode
- `results/spec_0.tla`, `results/spec_1.tla`, ... - Generated TLA+ specifications
- `results/stats.json` - Processing statistics

### Experiments Mode
- `results/experiment1_TIMESTAMP/` - Baseline compilation test results
- `results/experiment2_TIMESTAMP/` - Baseline correction results  
- `results/experiment3_TIMESTAMP/` - RAG correction results
- `results/comparison_report.json` - Comparative analysis

## Configuration

Modify `config.yaml` to customize:
- API settings (model, temperature, etc.)
- File paths (prompts, knowledge base, etc.)
- Experiment parameters (workers, loop times, etc.)

## Troubleshooting

1. **API Key Issues**: Make sure `DEEPSEEK_API_KEY` is set
2. **TLA+ Tools**: Install TLA+ SANY tools and add to PATH
3. **Dependencies**: Run `pip3 install -r requirements.txt`
4. **File Format**: Ensure input files are valid YAML

## Testing

Run the test suite to verify everything works:

```bash
python3 test_system.py
```

## Help

For detailed help and all options:

```bash
python3 main.py --help
``` 