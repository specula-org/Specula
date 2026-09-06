# Incremental CI Task: {{target}}

Read the installed Specula skill {{skill}} and its guide. Execute its complete
workflow in one continuous session: generation, trace validation, model checking,
and reproduction when an actual counterexample requires it. Apply the referenced
Specula methods. You own the analysis, planning, repairs, and verification loop.

## Inputs

- Original source update (before instrumentation): {{source_diff}}
- Old source: {{old_source}}
- New source working copy: {{new_source}}
- Prior Specula artifacts: {{old_model}}
- Working artifacts, initially copied from the prior model: {{work_dir}}

Treat old source and artifacts as read-only evidence. Make all changes in the new
source working copy and working artifacts. Rebase the existing harness onto the
new source; do not include instrumentation changes in the source update itself.
Keep the stage artifacts required by the skill as you work. They record evidence,
not automatic stage-completion or conversation-resume checkpoints.

## Finish

Write a concise `{{work_dir}}/ci-report.md` explaining the modeling decision,
model changes or repairs, trace validation, checking coverage, findings and
reproduction outcomes, with paths to actual commands, logs, traces and reports.
Distinguish limited exploration from unresolved required validation. A real code
bug does not by itself invalidate a faithful model or prevent workflow completion.

Only when the skill's applicable completion conditions are satisfied and all
started work has been observed, end your final response with this exact line:

SPECULA_INCREMENTAL_COMPLETE {{run_id}}

If work remains unresolved or execution is interrupted, report what remains and
do not emit that line. The current CI model will remain unchanged. On manual
resume, continue this same conversation and workspace; do not restart completed work.
