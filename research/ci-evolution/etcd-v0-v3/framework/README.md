# Bidirectional action validation prototype

An adapter consumes JSON test records containing `action`, `input`, and optional setup evidence. It returns the same input and an observed `output`. Code and model adapters execute their respective original implementation; the coordinator compares projections and retains both records.

Two routes use the same interface:

1. Code-derived input cases → code execution → corresponding model operation → comparison.
2. TLC-generated input/transition cases → implementation replay → comparison.

The first prototype tests the deterministic `StepHup` operation through a projection of role, term, vote, leader, log/application/commit indices, and outgoing election messages. The projection and fixture construction are target-specific. A successful comparison does not establish unobserved fields, all actions, or global reachability. Cases created from snapshots are local fixtures; protocol bug claims additionally require reachable execution evidence.

For a nondeterministic action the interface must return an allowed successor set or a relation-membership verdict. A single concrete run disagreeing with one permitted model successor is insufficient to reject the model. Failure to concretize a model state is recorded separately from a confirmed extra modeled behavior.

All artifacts remain outside the Specula checkout. Historical source files remain unchanged; build overlays and additional `_test.go` files are in `work/` only.
