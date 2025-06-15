# TLA+ RAG Error Correction System

A comprehensive system that integrates action completion with RAG-based error correction for TLA+ specifications.

## 🚀 Quick Start

### Option 1: Run Your Own Experiments
```bash
# Setup environment
./setup.sh

# Simple mode (recommended for first-time users)
python3 main.py examples/input_samples/simple_actions.yaml ./my_results simple

# Full experiment comparison
python3 main.py examples/input_samples/banking_system.yaml ./my_results experiments
```

### Option 2: View Pre-computed Results
If you don't have the required environment or want to see example results immediately:

```bash
# View demo results
ls results/demo_results/
cat results/demo_results/simple_mode_demo/stats.json

# View benchmark comparisons
cat results/benchmark_results/performance_metrics.json

# Read analysis reports
cat results/comparison_analysis/baseline_vs_rag.md
```

## 📁 Project Structure

```
phase_3_rag_correction/
├── src/                          # Source code
├── examples/                     # Sample inputs and tutorials
│   ├── input_samples/           # Ready-to-use YAML files
│   ├── quick_start.yaml         # Minimal example
│   └── complex_example.yaml     # Advanced example
├── results/                      # Pre-computed results and analysis
│   ├── demo_results/            # Example runs for different modes
│   ├── benchmark_results/       # Performance metrics
│   └── comparison_analysis/     # Detailed analysis reports
├── docs/                        # Documentation
├── tests/                       # Test cases
├── config.yaml                  # Configuration
├── main.py                      # Main entry point
├── setup.sh                     # Environment setup
└── requirements.txt             # Dependencies
```

## 🎯 Usage Modes

### Simple Mode
- **Purpose**: Quick action completion + RAG correction
- **Input**: YAML file with TLA+ action specifications
- **Output**: Completed and validated TLA+ files
- **Use Case**: Individual file processing, debugging

### Experiments Mode
- **Purpose**: Comprehensive comparison of three approaches
- **Experiments**:
  1. Baseline compilation test
  2. Baseline correction
  3. RAG-enhanced correction
- **Output**: Detailed comparison reports and statistics
- **Use Case**: Research, benchmarking, methodology evaluation

## 📊 Pre-computed Results

### Demo Results (`results/demo_results/`)
- **simple_mode_demo/**: Example run of simple mode
- **experiments_mode_demo/**: Example run of experiments mode
- Each contains:
  - `stats.json`: Success rates and metrics
  - `generated_specs/`: Output TLA+ files
  - `logs/`: Detailed execution logs

### Benchmark Results (`results/benchmark_results/`)
- **performance_metrics.json**: Execution times, memory usage
- **accuracy_analysis.json**: Correction success rates
- **error_correction_rates.json**: Detailed error type analysis

### Comparison Analysis (`results/comparison_analysis/`)
- **baseline_vs_rag.md**: Methodology comparison
- **methodology_comparison.md**: Technical analysis
- **charts_and_graphs/**: Visual comparisons

## 🔧 Environment Requirements

### Required
- Python 3.8+
- TLA+ SANY tools
- DEEPSEEK_API_KEY (for LLM correction)

### Optional (for viewing results only)
- Any text editor or JSON viewer
- Markdown viewer for analysis reports

## 📖 Examples

### Example 1: Banking System
```bash
# Run your own experiment
python3 main.py examples/input_samples/banking_system.yaml ./results simple

# Or view pre-computed results
cat results/demo_results/banking_system_demo/stats.json
```

### Example 2: Distributed Consensus
```bash
# Full comparison experiment
python3 main.py examples/input_samples/distributed_consensus.yaml ./results experiments

# Compare with our benchmark
diff ./results/comparison_report.json results/benchmark_results/consensus_benchmark.json
```

## 🆘 Troubleshooting

### No Environment Setup
If you can't set up the environment:
1. Browse `results/demo_results/` for example outputs
2. Read `results/comparison_analysis/` for methodology insights
3. Check `docs/examples_walkthrough.md` for detailed explanations

### API Key Issues
If you don't have DEEPSEEK_API_KEY:
1. Simple mode will still work (validation only)
2. View `results/demo_results/` to see correction examples
3. Read `docs/troubleshooting.md` for alternatives

## 📚 Documentation

- **docs/user_guide.md**: Comprehensive usage guide
- **docs/api_reference.md**: Technical API documentation
- **docs/examples_walkthrough.md**: Step-by-step examples
- **docs/troubleshooting.md**: Common issues and solutions

## 🤝 Contributing

1. Run your experiments and compare with benchmark results
2. Add new examples to `examples/input_samples/`
3. Share interesting results in `results/user_contributions/`

## 📄 License

[Your License Here]

---

**Note**: This system is designed to be accessible whether you want to run experiments yourself or just explore the methodology through our pre-computed results.
