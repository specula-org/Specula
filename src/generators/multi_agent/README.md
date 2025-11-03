# Multi-Agent TLA+ Generator

A multi-agent framework for generating TLA+ specifications from source code.

## Architecture

```
Multi-Agent Pipeline:
  Source Code
      ↓
  [1] ArchitectureAnalyzer   
      ↓
  [2] SkeletonGenerator      
      ↓
  [3] SubsystemTranslator     
      ↓
  [4] SpecIntegrator         
      ↓
  [5] ConsistencyValidator   
```

## Directory Structure

```
src/generators/multi_agent/
├── orchestrator.py              # Main pipeline controller
├── base_agent.py                # Base class for all agents
│
├── agents/                      # 5 specialized agents
│   ├── architecture_analyzer.py # Analyze code structure & design data
│   ├── skeleton_generator.py    # Generate TLA+ skeleton
│   ├── subsystem_translator.py  # Translate subsystems to TLA+
│   ├── spec_integrator.py       # Integrate all subsystems
│   └── consistency_validator.py # Validate final spec
│
└── utils/
    └── checkpoint.py            # (Future) Checkpoint management
```
