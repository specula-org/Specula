---
name: incremental-modeling
description: "Incrementally evolve and verify an existing Specular TLA+ suite for a new source revision. Use when an Agent has a prior Specular run plus old and new source, and must decide whether the model changes, update the reference/MC/Trace suite, generate Update.tla, reuse and rebase the prior trace harness for update-focused validation, model-check changed/unchanged interactions, and hand real counterexamples to bug reproduction."
---

Read `guide.md` for the full incremental workflow and its current stage boundaries.
