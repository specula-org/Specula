---
name: tla-checking-workflow
description: "TLA+ Model Checking workflow. Use when: (1) running TLC model checking or simulation on a TLA+ spec, (2) analyzing counterexamples from invariant violations, (3) determining whether a violation is an invariant mismatch, a spec issue, or a real bug in the system implementation."
---

When a candidate defect first appears in a CI run, perform the lightweight historical lookup described in the installed **bug-confirmation** skill's `references/issue-reuse.md` before complex analysis or reproduction work. Read only matching unresolved records; reuse completed work only when the mechanism, consequence, dependencies, and premises still apply.

Read `guide.md` for the full workflow methodology.
