# TLAGEN Examples

This directory contains examples and templates to help you get started with TLAGEN. These are **reference implementations** that demonstrate the framework's capabilities and serve as starting points for your own customizations.

## 📁 Directory Structure

```
examples/
├── etcd/                    # Complete ETCD/Raft example
│   ├── config/              # TLA+ action configuration
│   ├── source/              # Original source code
│   ├── output/              # Generated instrumented code
│   └── scripts/             # Automation scripts
└── runners/                 # Example test runners
    └── raft_simulator/      # Raft state machine simulator
```

## 🎯 ETCD Example

The ETCD example demonstrates the complete workflow for a real-world distributed system.

### Files Overview

- **`config/raft_config.yaml`**: Defines the mapping between TLA+ actions and Go functions
- **`source/raft.go`**: Original etcd/raft source code
- **`output/`**: Directory for generated instrumented code
- **`scripts/run_instrumentation_test.sh`**: Complete automation script

### Usage

```bash
cd etcd
./scripts/run_instrumentation_test.sh
```

This will:
1. Use the Go instrumentation template
2. Instrument the raft.go source code
3. Run the simulator to generate traces
4. Show results and generated files

## 🏃 Test Runners

The `runners/` directory contains example test runners that demonstrate different approaches to generating execution traces.

### Raft Simulator

A lightweight Raft state machine simulator that:
- Simulates basic Raft operations (tickElection, tickHeartbeat, Step)
- Generates random state transitions
- Produces NDJSON trace files
- Serves as a template for building real test harnesses

**Key Features:**
- Simple Go implementation
- Configurable through environment variables
- Generates structured trace data
- Easy to extend and customize

## 🔧 Customization Guide

### For Your Own System

1. **Create a new directory** under `examples/` for your system
2. **Copy the etcd structure** as a starting point:
   ```bash
   cp -r examples/etcd examples/my_system
   ```
3. **Update the configuration** in `config/` to match your TLA+ actions
4. **Replace the source code** in `source/` with your system's code
5. **Modify the automation script** in `scripts/` for your specific needs

### For Different Languages

1. **Use appropriate templates** from `templates/instrumentation/`
2. **Modify the test runner** to match your language's execution model
3. **Update trace generation** to match your system's data structures

### For Custom Test Scenarios

1. **Copy the raft_simulator** as a base:
   ```bash
   cp -r examples/runners/raft_simulator examples/runners/my_runner
   ```
2. **Modify the state machine logic** to match your system
3. **Add your specific test scenarios** and randomization strategies
4. **Update trace data format** as needed

## ⚠️ Important Notes

- **These are examples, not production code**: The runners and scripts are meant to demonstrate concepts, not to be used directly in production
- **Customization required**: You'll need to adapt these examples to your specific system and requirements
- **Template nature**: Think of these as templates or starting points rather than finished solutions

## 🚀 Next Steps

1. **Start with the ETCD example** to understand the workflow
2. **Examine the simulator code** to understand trace generation
3. **Create your own example** based on these templates
4. **Extend the framework** with your own improvements

---

**Remember**: The goal is to provide you with working examples that you can understand, modify, and extend for your own use cases. 