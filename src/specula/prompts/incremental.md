# Incremental CI Task: {{target}}

Read the installed Specula skill {{skill}} and its guide. Execute generation, trace validation, and model checking in this continuous session. Collect both code-review candidates and actual model-checking counterexamples using the one-shot formats. You own the analysis, planning, repairs, and verification loop.

For confirmation, save the current `modeling-brief.md`, `spec/bug-report.md`, and `spec/findings.json` when present, then call `request_bug_confirmation`. Reuse applicable persistent findings first. The controller pauses this conversation, runs the existing one-shot confirmation workflow with the configured agent and concurrency, then resumes this exact session with the results. Do not independently reproduce the same candidates or start confirmation agents yourself. If the tool is unavailable, run `python3 "$SPECULA_ROOT/tools/context_control/request.py" --confirm` and follow its returned yield instruction.

For long conversations, follow the skill's context-preservation guidance. The `request_context_compaction` tool can yield an internal turn after you save a handoff; the controller resumes this same session. Such a yield is not completion of the workflow and does not require final reports. Compaction is optional; failure does not prevent continuing the task.

## Inputs

- Original source update (before instrumentation): {{source_diff}}
- Old source: {{old_source}}
- New source working copy: {{new_source}}
- Prior Specula artifacts: {{old_model}}
- Working artifacts, initially copied from the prior model: {{work_dir}}

Treat old source and artifacts as read-only evidence. Make all changes in the new source working copy and working artifacts. Rebase the existing harness onto the new source; do not include instrumentation changes in the source update itself. Keep the stage artifacts required by the skill as you work. They record evidence, not automatic stage-completion or conversation-resume checkpoints.

## Finish

Follow the skill's Readiness and Final Reporting guidance. First briefly check readiness against the existing evidence; if required work remains, continue it before final reporting. This self-check does not need a separate file.

Only once ready, follow this run's output contract:

{{final_reporting}}

Keep the summary concise and link maintained evidence instead of repeating the investigation. Resource summaries and costs are handled by the existing tools.

Only when the skill's applicable completion conditions are satisfied and all started work has been observed, end your final response with this exact line:

SPECULA_INCREMENTAL_COMPLETE {{run_id}}

The controller returns CI failure for `REPRODUCED` and `ENV_LIMITED`, and a nonblocking warning for `MASKED`.

If blocked or interrupted, save brief progress and the next step in the existing records or handoff, not a final CI report, and do not emit that line. The current CI model will remain unchanged. On manual resume, continue this same conversation and workspace, including any partial report; do not restart valid completed work.
