## Parallel Subagents

Your agent CLI may let you delegate work to subagents. Whether you use them, and how many, is your decision: they help where independent work would otherwise run serially or fill this session's context, and they get in the way where the reasoning is coupled.

- Writes stay with you. Only you write the shared artifacts (`modeling-brief.md`, `base.tla`, `MC.tla`, `Trace.tla`, harness code). A subagent investigates and returns conclusions with `file:line` evidence and paths, not edits to shared files.
- Good units to fan out are independent, read-only investigations: deep analysis of one module or file; a batch of issues or commits to verify; the history of one component; the code facts behind one action while you write the spec; the instrumentation points of one component; and, during validation, the diagnosis of one failing trace or the Case A/B/C triage of one counterexample.
- A clean context reviews best where self-assessment is weakest. After you synthesize the Scenarios, a fresh subagent can challenge them (overgeneralization across modules, missing evidence, unsupported claims) before you revise them; after you write the base spec, one can check its fidelity against the code.
- Keep tightly coupled sequential reasoning, a counterexample derivation in progress, and anything that needs this session's accumulated context to yourself. Do not start confirmation or reproduction agents; Specula runs those.
- Run subagents in the foreground: issue independent subagent calls together so they run in parallel, and integrate their results before you end your turn.
