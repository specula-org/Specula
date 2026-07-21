# Continue interrupted confirmation turn: {{finding_id}}

This is a fresh session continuing turn {{turn_no}} as Agent {{role}}. The
previous session was interrupted by the provider. Do not restart useful work
that is already present.

## Canonical inputs
- Current finding only: `{{finding_context}}`
- Source repo and retained finding worktree: `{{repo}}`
- Finding work dir: `{{fdir}}`
- Reproduction dir: `{{repro_dir}}`
- Debate index and prior-turn log links: `{{debate}}`
- Repair draft, when required: `{{repair_draft}}`

Use the installed Specula skill {{bug_confirmation_skill}}. Read the finding
capsule first, inspect the retained worktree and relevant files in the finding
work dir, then complete only the remaining work. Do not inspect other finding
directories, `bug-report.md`, `confirmed-bugs.md`, or the shared repair queue.

## This turn
{{role_task}}

End the entire response with one line:
`VERDICT: <one of: {{canon}}>`

For `PENDING REPAIR`, also write the semantic draft at `{{repair_draft}}` using
the skill's repair-request format. Do not allocate an RR id or write the shared
repair queue.
