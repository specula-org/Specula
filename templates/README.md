# Specula Templates

This directory contains instrumentation templates, designed to be customized for your specific use cases.

## Directory Structure

```
templates/
└── instrumentation/
    ├── go_trace_stub.template      # Go language instrumentation template
    ├── python_trace_stub.template  # Python language instrumentation template
    └── rust_trace_stub.template    # Rust language instrumentation template
```

## Instrumentation Templates

Instrumentation templates define the code that gets injected into your source code functions to generate execution traces. Each template is language-specific and follows the conventions of that language.

Templates use the placeholder `ACTION_NAME` which gets replaced with the actual TLA+ action name during instrumentation.

### Go Template (`go_trace_stub.template`)

```go
traceAction("ACTION_NAME", map[string]interface{}{
	"node_id": r.id,
	"term": r.Term,
	"state": r.state.String(),
})
```

### Python Template (`python_trace_stub.template`)

```python
trace_action("ACTION_NAME", {
    "node_id": self.node_id,
    "state": self.state,
    "term": self.term
})
```

### Rust Template (`rust_trace_stub.template`)

```rust
trace_action("ACTION_NAME", &TraceParams {
    node_id: self.node_id,
    state: self.state.clone(),
    term: self.term,
});
```

## Customization

To create a custom template to integrate with an existing logging system:
1. Copy an existing template as a starting point
2. Modify the emitted data structure to match your system's state
3. Update function calls to match your trace collection mechanism

> [!NOTE]  
> Specula trace validation currently only supports high-level action information, or `state` and `term` trace data. We are actively adding support for finer-grained validation.

### Examples

**Custom Go Template with JSON logging:**
```go
log.Printf(`{"action":"%s","timestamp":%d,"data":%s}`, 
    "ACTION_NAME", 
    time.Now().UnixNano(), 
    mustMarshal(map[string]interface{}{
        "node_id": r.id,
        "term": r.Term,
    }))
```

**Custom Python Template with structured logging:**
```python
logger.info("trace_event", extra={
    "action": "ACTION_NAME",
    "timestamp": time.time_ns(),
    "node_id": self.node_id,
    "state": self.state
})
```

**Custom Rust Template with serde:**
```rust
let trace_data = TraceEvent {
    action: "ACTION_NAME",
    timestamp: SystemTime::now(),
    node_id: self.node_id,
    state: self.state.clone(),
};
trace_logger.log(&trace_data);
```

### Template Variables

You can use these variables in your templates:

- `ACTION_NAME`: Replaced with the actual TLA+ action name
- Custom placeholders (for now, this requires modifying the instrumentation tool)

## Usage

The instrumentation tool can auto-detect the appropriate template based on the source file extension, or you can specify it explicitly.

```bash
# Use a built-in template
python3 src/core/instrumentation.py \
    config.yaml source.go \
    --stub-template templates/instrumentation/go_trace_stub.template \
    --output instrumented.go

# Generate a template for customization
python3 src/core/instrumentation.py \
    config.yaml source.py \
    --generate-template my_custom_template.txt \
    --language python
```
## Best Practices

- Focus only on essential trace data to improve validation results
- Use appropriate naming and data structures to cue LLM context
- Avoid runtime-expensive operations in trace code
- Keep templates under version control with your project

## Troubleshooting

- Check that template syntax matches your language
- Ensure template variables exist in target functions
- Some templates may require additional library imports (e.g. `serde` or `logging`)
- To debug custom templates: test incrementally, and run `--validate-only` before full instrumentation
