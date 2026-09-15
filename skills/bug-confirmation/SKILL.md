---
name: bug-confirmation
description: "Bug confirmation and reproduction. Use when: (1) a bug has been found by model checking and needs code-level validation, (2) reproducing a bug in the real system to confirm it is not a false positive, (3) assessing whether a TLA+ counterexample maps to a real triggerable scenario."
---

When a candidate defect first appears in a CI run, perform the lightweight historical lookup described in the installed **bug-confirmation** skill's `references/issue-reuse.md` before complex analysis or reproduction work. Read only matching unresolved records; reuse completed work only when the mechanism, consequence, dependencies, and premises still apply.

Read `guide.md` for the full workflow methodology.
