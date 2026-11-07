# Specula blind incremental bug-discovery experiment

## Objective

Run one fresh Agent on each of 12 code updates and measure how many update-introduced bugs are independently discovered from the source delta and a pre-update Specula suite.

## Primary outcome

Count a case as `BLIND_DISCOVERED` only when all of the following hold:

1. Before Gold is available, the Agent derives a materially correct bug mechanism and property from the source delta.
2. TLC produces a reachable counterexample on the buggy revision.
3. The same property/scenario does not fail on the immediate pre-update revision.
4. The counterexample maps to the real implementation or the upstream regression test.
5. The fixed revision removes the failure under the same property/scenario.

Other terminal dispositions are `PARTIAL_HYPOTHESIS`, `MODEL_OR_INVARIANT_ERROR`, `MISSED`, `ENV_LIMITED`, `TIMEOUT`, and `CONTAMINATED`.

## Blind inputs

Each Agent may see only its own Bubblewrap-mounted `/work`:

- neutral `case.json` without upstream SHA, issue number, fix revision, or bug label;
- changed files at the immediate pre-update and buggy revisions;
- a full writable source snapshot at the buggy revision with no upstream Git history or remote;
- a validated pre-update `.specula-output/` stripped of historical bug reports, target-specific hunt configs, reproductions, and answer-bearing comments;
- frozen skills and local tools;
- pre-fetched build dependencies where practical.

The Agent must not see the candidate report, private case map, upstream issue/PR pages, fixed source, Gold properties, prior experiment conversations, user memories, or grading material.

## Network boundary

The Codex client requires network access to the model provider. The current Bubblewrap runner therefore cannot enforce complete network disconnection while the model is running.

Controls:

1. The task explicitly prohibits internet/history search and allows network only for ordinary dependency retrieval.
2. The source snapshot has no upstream Git history or remote.
3. Common search/download commands are shadowed by deny wrappers where they are not required for the build.
4. Agent-visible bind mounts originate from random paths under the neutral host
   root `.cache/sci-20260904/`; `/proc/self/mountinfo` therefore cannot reveal
   the answer-bearing experiment directory name. The parent launches bwrap with
   only `PATH` and `LANG`, and resolved opaque bind paths, so `/proc/1/environ`
   and `/proc/1/cmdline` do not expose the outer thread or logical experiment
   path. stdout/stderr are anonymous pipes drained by the parent.
5. The complete Agent activity stream is frozen and audited before Gold is unsealed.
6. Any issue/PR/commit lookup, general web search, or unexplained outbound retrieval makes the run `CONTAMINATED`, not a discovery.

This primary arm measures source-derived discovery, not Specula's full history-assisted research capability.

## Execution

- Model: `gpt-5.6-sol`
- Reasoning effort: `xhigh`
- Preparation: one exact-old-only V0 generator per case; these are teacher/setup
  runs and are not counted among the 12 incremental discovery Agents.
- Attempts: one fresh attempt per case
- Parallelism: 3 isolated Agents; 12 cases run in four waves
- Outer timeout: 4 hours per Agent
- Reproduction: separate frozen Agent only after a main-run finding exists
- No semantic retry; infrastructure retries get a new attempt identity

The authoritative V0 run is `attempt-004`. Earlier identities are retained as
non-semantic infrastructure/pilot records: `attempt-001` failed before model
execution because of a CLI invocation mismatch; `attempt-002` was stopped after
the isolation audit found inherited host environment variables; `attempt-003`
was prepared but never started. Only `attempt-004` uses a cleared environment,
read-only pristine source, a separate writable instrumentation worktree, exact
mounts, sandbox-external logs, and command-deny wrappers.

The V0 subsystem boundary is selected before the updated tree is mounted. This
is an applicability precondition for incremental modeling, not a claim that
Specula independently chose the correct module. The final report must identify
this module-selection assistance as an external-validity limitation.

## Freeze and grading order

1. Freeze source trees, pre-update suite, task, skill tree, and input hashes.
2. Run all 12 main Agents.
3. Freeze final responses, activity logs, models, traces, TLC logs, findings, usage, and retry lineage.
4. Run the network/history leak audit.
5. Unseal private Gold.
6. Run pre-update and fixed controls for each actual finding.
7. Grade case-level discovery and workflow quality separately.

## Interpretation

- A real bug that also fails on the pre-update control is inherited redetection, not update discovery.
- A correct guess without a TLC counterexample is partial, not discovered.
- A TLC violation from an unfaithful model/property is not a bug.
- A timeout or open state-space frontier is limited coverage, not a pass or miss.
- Multiple symptoms caused by one update count as one successful case.
