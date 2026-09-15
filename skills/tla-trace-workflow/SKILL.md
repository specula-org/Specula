---
name: tla-trace-workflow
description: "TLA+ Trace Validation workflow. Use when: (1) validating if a trace matches a TLA+ spec, (2) debugging trace validation failures (TLC reports 'Temporal properties were violated' or validation stops unexpectedly), (3) fixing spec/trace inconsistencies after root cause is identified."
---

When a candidate defect first appears in a CI run, perform the lightweight historical lookup described in the installed **bug-confirmation** skill's `references/issue-reuse.md` before complex analysis or reproduction work. Read only matching unresolved records; reuse completed work only when the mechanism, consequence, dependencies, and premises still apply.

Read `guide.md` for the full workflow methodology.
