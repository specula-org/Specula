---
name: validation-workflow
description: "TLA+ Verification workflow (orchestration). Use when: running the full verification loop — iterating between trace validation and model checking until both pass, ensuring spec faithfully models the system."
---

When a candidate defect first appears in a CI run, perform the lightweight historical lookup described in the installed **bug-confirmation** skill's `references/issue-reuse.md` before complex analysis or reproduction work. Read only matching unresolved records; reuse completed work only when the mechanism, consequence, dependencies, and premises still apply.

Read `guide.md` for the full workflow methodology.
