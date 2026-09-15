# Incremental CI Task: {{target}}

Read the installed Specula skill {{skill}} and its guide. Execute its complete workflow in one continuous session: generation, trace validation, model checking, and reproduction when an actual counterexample requires it. Apply the referenced Specula methods. You own the analysis, planning, repairs, and verification loop.

For long conversations, follow the skill's context-preservation guidance. The `request_context_compaction` tool can yield an internal turn after you save a handoff; the controller resumes this same session. Such a yield is not completion of the workflow and does not require final reports. Compaction is optional; failure does not prevent continuing the task.

## Inputs

- Original source update (before instrumentation): {{source_diff}}
- Old source: {{old_source}}
- New source working copy: {{new_source}}
- Prior Specula artifacts: {{old_model}}
- Working artifacts, initially copied from the prior model: {{work_dir}}

At the first candidate defect, run `"$SPECULA_ROOT/specula" issues --work {{work_dir}} lookup` with relevant source/model/invariant queries before complex analysis or reproduction. Follow the bug-confirmation skill’s `references/issue-reuse.md`: read only matching records; reuse applicable conclusions and reanalyze only affected or uncertain issues.

Treat old source and artifacts as read-only evidence. Make all changes in the new source working copy and working artifacts. Rebase the existing harness onto the new source; do not include instrumentation changes in the source update itself. Keep the stage artifacts required by the skill as you work. They record evidence, not automatic stage-completion or conversation-resume checkpoints.

## Finish

Follow the skill's Readiness and Final Reporting guidance. First briefly check readiness against the existing evidence; if required work remains, continue it before final reporting. This self-check does not need a separate file.

Only once ready, write `{{work_dir}}/ci-report.md` as a short result summary with evidence links, and `{{work_dir}}/ci-verdict.json` following the skill's CI Verdict format with run ID `{{run_id}}`. A few lines suffice for an uneventful update. Reuse the maintained stage records rather than rewriting the one-shot reports; resource summaries and costs are handled by the existing tools.

Page through the unresolved issue summaries before finishing. Prior bug and warning findings need either a checked reuse receipt or a current disposition, including for `NO_MODEL_CHANGE` and issues not rediscovered. Keep stable IDs. Record completed new/updated issues with their dependencies and selected evidence; a verified repair is `FIXED` and removes the active record. Legacy issues without dependency metadata require analysis before becoming reusable. The controller merges valid reuse receipts into the verdict and labels them in the report; their original status still affects CI.

Only when the skill's applicable completion conditions are satisfied and all started work has been observed, end your final response with this exact line:

SPECULA_INCREMENTAL_COMPLETE {{run_id}}

The controller returns CI failure for `REPRODUCED` and `ENV_LIMITED`, and a nonblocking warning for `MASKED`.

If blocked or interrupted, save brief progress and the next step in the existing records or handoff, not a final CI report, and do not emit that line. The current CI model will remain unchanged. On manual resume, continue this same conversation and workspace, including any partial report; do not restart valid completed work.
