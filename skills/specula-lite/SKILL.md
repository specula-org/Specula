---
name: specula-lite
description: Find bugs in concurrent or distributed code using TLA+ modeling, model checking, and code-level reproduction. Use for a focused investigation with one coding agent, without trace validation or the full Specula pipeline.
---

# Specula Lite

Investigate the user's code, model its behavior, check properties, attempt code-level reproduction, and deliver an evidence-backed report. This is a long task conducted by the current agent.

## Start with the user

First ask which repository or code they want investigated and what problems they care about. Reflect any details already supplied in the question. Wait for their answer before investigating. A broad answer such as "concurrency bugs in this repository" is sufficient: scan the code, choose a coherent focus, explain the choice, and proceed without another approval round.

## Prepare

Resolve this skill's installed directory as `SKILL_DIR`; it is not the target repository. Run:

```bash
python3 "$SKILL_DIR/scripts/prepare.py"
```

The helper unpacks the bundled Specula references and output reader, reuses Java 21+ when available, and downloads missing tools into the user's cache. It prints JSON with the `guides` directory and tool paths. No Specula installation, agent adapter, MCP registration, Maven, or Python packages are needed. Python 3.10+ is the bootstrap prerequisite; if unavailable, help prepare it using the user's existing environment tooling. Explain a failed prerequisite concretely rather than presenting an unexecuted check as a result.

Create a fresh investigation directory under the target's `.specula-lite/`, keeping models, logs, reproduction tests, and `report.md` together. Record the source revision and local changes relevant to the investigation. Preserve the user's existing work; use a separate source copy/worktree for reproduction changes when necessary. Keep brief progress notes so the same agent can continue after context compaction.

## Rules for using the shared skills

Read the bundled guides as methodology, in the sequence below. `guides` is the directory returned by preparation; paths such as `code_analysis/guide.md` are relative to it. Relative links inside a guide resolve from that guide's directory. Read relevant supporting references as needed, not the entire bundle up front.

**These Lite rules govern the workflow when a shared guide describes the standard pipeline:**

- Use one agent throughout. Perform referenced subagent/Task work yourself, sequentially; do not launch other agents or Specula's pipeline/confirmation dispatchers.
- Skip trace-validation instrumentation, execution-trace collection, harness generation, `Trace.tla`/`Trace.cfg`, and instrumentation specifications. Do not invoke `validation-workflow` or `tla-trace-workflow`. TLC counterexample traces remain essential evidence and are different from implementation traces.
- Use the scripts below and the host's file/shell tools instead of MCP tools, `specula` commands, background-run wrappers, or agent-specific launchers. VAV is optional if already available; do not install the full CFA/Maven stack as a prerequisite for Lite.
- Continue autonomously after the opening answer. Do not wait for the user between phases or stop at the first model counterexample. Investigate and reproduce candidates before completing the report.
- There is no default task deadline or fixed repair-round limit. The shared guides' fixed timeouts, giant simulation counts, and machine-sized resource examples are not Lite defaults. Choose finite model configurations and finite simulation campaigns appropriate to the question; record their bounds and coverage. Investigate hangs and resource failures without treating them as successful checks or confirmed bugs.
- Repair inaccurate models, fault assumptions, or properties in this same session, then recheck. Preserve valid requirements and source correspondence; never weaken a property merely to make TLC pass. No repair-request queue, CI baseline, persistent-finding registry, telemetry service, or external tracker is required. Use the local evidence and report to record dispositions.
- Do not repair the target implementation. Test fixtures and scheduling controls for reproduction must preserve the behavior under investigation. Keep unresolved candidates, including environmental limitations, clearly separate from reproduced bugs. Suggestions in a report are allowed; applying a fix requires the user's later request.

## Investigation

1. **Analyze the code.** Read `code_analysis/guide.md`, then the references relevant to the target's distributed/concurrent/BFT category. Follow the user's scope, inspect relevant history and known reports, and write `modeling-brief.md` with mechanisms, source locations, proposed properties, assumptions, and exclusions. Apply the guide's investigative methods to this scope; repository-wide issue quotas are not prerequisites.
2. **Build the model.** Read `spec_generation/guide.md`, especially `references/base-spec-methodology.md`, `mc-spec-pattern.md`, and `brief-coverage-checklist.md`. Produce the base and model-checking modules/configurations, with source correspondence and a coverage audit of the chosen brief. Skip its trace and instrumentation outputs. Include implementation guards and atomicity boundaries, not just the reference algorithm.
3. **Check and investigate counterexamples.** Read `tla-checking-workflow/guide.md`, especially its counterexample classifications, fidelity checklist, and TLC gotchas. Parse the model, check structural and substantive properties, then investigate the relevant fault/interleaving scenarios. Use actual tool results to distinguish property mismatch, model error, and a candidate implementation defect. A clean finite check only covers the recorded model/configuration; it does not certify the implementation.
4. **Attempt reproduction.** Read `bug-confirmation/guide.md` and its investigation/reproduction phases. Handle candidates sequentially, including code-review candidates without a model counterexample. Establish reachable preconditions and observable harm in the real implementation. Execute tests and retain commands and outputs. When reproduction exposes a model artifact, correct the model and return to checking directly. A failure to reproduce alone does not establish that a candidate is false.
5. **Report.** Use `bug-classification/guide.md` for impact/severity reasoning, writing the final result directly to `report.md`; its pipeline-specific intermediate report formats are not required. Finish when the selected scope has been investigated, relevant checks have completed or have an explained blocker, and every candidate has an evidence-backed disposition. An external blocker may leave an explicitly incomplete result; do not manufacture successful completion.

## Tool calls

See [scripts.md](references/scripts.md) for optional arguments. Run these from the directory containing the model. Use a fresh log name for each invocation. Use `read_tlc.py` when the log contains a counterexample; for other outcomes, inspect the log and execution receipt directly:

```bash
python3 "$SKILL_DIR/scripts/tlc.py" parse base.tla --log output/parse.log
python3 "$SKILL_DIR/scripts/tlc.py" check MC.tla --config MC.cfg --log output/check.log
python3 "$SKILL_DIR/scripts/read_tlc.py" output/check.log --summary --json
python3 "$SKILL_DIR/scripts/read_tlc.py" output/check.log --state last
python3 "$SKILL_DIR/scripts/read_tlc.py" output/check.log --diff -2 -1
```

The runner has no default timeout. If the host returns a running command/session handle, keep observing that same process until it exits; a host wait interval is not a reason to relaunch TLC. Read the saved log for progress. Observe reproduction/build processes as well, and retain their actual exit status. The `.run.json` sidecar records execution, not a verification verdict. Inspect TLC's diagnostic output; absence of a parsed counterexample does not imply success.

## Deliver the report

Include the investigated source/revision and scope; model assumptions and checked configurations; completed checks and their coverage/limits; and paths to models, logs, and executed reproduction tests. Explicitly state that trace validation was not performed.

Separate:

- **Reproduced bugs:** source, location, trigger, observable consequence, actual reproduction command/result, novelty evidence where available, and severity supported by the demonstrated impact.
- **Unconfirmed findings:** model/source evidence, attempted reproduction, what remains unknown or blocked, and useful next steps. Preserve distinctions such as environment-limited, masked, and needs-more-information; do not count them as reproduced bugs.
- **Other dispositions:** known duplicates, ruled-out candidates, and corrected model/property artifacts, with reasons. Do not silently lose candidates.

If no bug is reproduced, say so without claiming the code is correct. Link the report and important artifacts in the final response. End by asking whether the user wants help fixing any reported issue, and wait for their answer before making repairs.
