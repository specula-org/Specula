# Iteration log

Every change to an arm's prompt or to the harness is recorded here with what triggered it. A prompt change makes a new prompt hash; results of earlier versions are kept, not overwritten.

## Iteration 0 — A0, A1 (2026-11-13)

- **A0** `prompts/A0-skill-rules.md`: property rules quoted from `skills/incremental-modeling` (02 §3, 03 §3, 04 §5), same inputs and output fields as A1, no separating state.
- **A1** `prompts/A1-judge.md`: Qian's `inv-judge` prompt; only `/workspace` was replaced, by "the current directory".
- **Harness:** `claude -p`, Opus 5.5, effort xhigh. Tools Read/Glob/Grep/Write/Edit only; reads outside the workspace are denied.
- **First runs:** V03 r1 for both arms. A0 copied the buggy crossing guard into AutoLeaveAdvance; A1 did not. Both named bug B.
- **Extra runs:** V03 r2 and r3 were run before the one-run-per-input rule was set. They are kept as supplementary variance data and are not part of the main table.
- **Not a prompt change:** `check_decision.py` now also accepts `action` and `property` as field names, because A0 used them.

## Iteration 1 — A2, A3 prototypes v1 (2026-11-14)

- **A2** `prompts/A2-judge-evidence.md`: A1's judgment text, without the "do not execute" sentence, then an execution phase carrying over the rules of Qian's `inv-evidence` prompt:
  - TLC evaluates the actual old and proposed definitions on the separating state, with `INSTANCE ... WITH var <- expr` recommended;
  - history and quality records must be non-empty;
  - Go tests observe old and new code behavior;
  - relaxations need a nearby forbidden control, strengthenings an allowed control.
  The first judgment is written to `out/decision.initial.json` before any command runs, and is then frozen.
  Difference from Qian: one session does both the judgment and the evidence. In Qian's setup they were two calls, and the evidence call did not author the edits.
- **A3** `prompts/A3-two-axis.md`: A2 plus a Phase 3:
  - each witness is classified on an implementation axis and a requirement axis;
  - requirement evidence may cite only tests, documentation, contracts and intent comments, never non-comment implementation code;
  - when the implementation produces a state the requirement forbids, the default is a bug candidate, not a property edit;
  - kept properties whose inputs the update touched also need an executed state.
- **Harness for A2/A3:** `sandbox.sh`, unprivileged user and mount namespaces.
  - Only the workspace (at `/tmp/workspace`), the TLC jars and an offline Go module cache are visible. Home, the repo, `/proj` and `/mydata` are empty tmpfs mounts.
  - Bash is enabled, the cap is $40 per run, and the JVM is limited to 8 GB.
  - A Haiku smoke test confirmed that the rubric path and the transcripts were not readable, that TLC ran, and that Go built offline.
  - The network cannot be cut, because the agent needs the API. `run.py` therefore records every Bash command and flags any that look like network use.
- **Go build overlay:** the raft revisions have no `go.mod`, so `godeps/` recreates the one Qian's harness used: module `go.etcd.io/etcd/raft`, with datadriven, gogo/protobuf and golang/protobuf pinned as in etcd v3.4.0, and `go.etcd.io/etcd/pkg/testutil` taken from etcd v3.4.0. All V03 packages pass `go test` offline.
- **Checker:** `check_decision.py` now also checks `evidence.json`: whether claimed truth values match TLC, how many code observations were made, and, for A3, requirement citations that point at non-comment implementation code.

## Iteration 1a — harness fix, no prompt change (2026-11-14)

- **Trigger:** the first launch of all 10 remaining runs, 10 in parallel at 01:01, returned exit code 1 after 6–10 minutes. Every run's final message was "You've hit your 5-hour limit · resets 5:50am" (HTTP 429). The Claude Code result event still said `subtype: success`, so `run.py` had recorded the runs as results. Two of them had written only `decision.initial.json`.
- **What this says about the method:** nothing. The runs were cut off by the account's usage window.
- **Changes:**
  - The 10 results moved to `results/invalid-usage-limit-20261114/` and are not scored.
  - `run.py` now treats a missing result event or `is_error: true` as an invalid attempt. The attempt goes to `$INV_ABLATION_WORK/invalid/` together with `invalid.json`, which gives the reason, the cost and the API status. Nothing is written under `results/`.
  - On a usage-limit message, `run.py` waits until the stated reset plus 3 minutes and restarts the run from scratch, up to 3 attempts. Each result records its `attempt` number.
  - Runs now go at most 2 at a time, so a batch cannot use up the window in a few minutes. Order: A2/A3 on V03, V02, V01 first, alongside A0/A1 on V01, V02.

## Iteration 1b — harness, no prompt change (2026-11-14 11:05)

- **Trigger:** with 2 runs in parallel, the usage window was used up again at about 06:45. A1-V01 was cut off after 22 minutes ($5.76) and A2-V03 after 43 minutes ($9.37), both before writing their final decisions. `run.py` handled it as designed: it moved both attempts to `invalid/` and slept until the reset. The usage window is shared with the interactive session that coordinates the experiment.
- **Change:** both waiting queues were stopped, and the remaining 9 runs restarted as one sequential queue (`queue.sh`): A2/A3 on V03, V02, V01, then A0/A1 on V01, V02. The retry-after-reset logic stays.

## Iteration 1c — harness, no prompt change (2026-11-14 13:12)

- **Trigger:** A2-V02 hit the previous account's 5-hour limit at 12:23, after 2 minutes ($0.68), and was waiting for a 16:00 reset. The user switched to another account.
- **Change:** the waiting queue was stopped and `queue.sh` restarted. Finished runs (A2-V03, A3-V03) were skipped. A2-V02 restarted from scratch on the new account. The sandbox copies the current credentials when each run starts, so no other change was needed. Model, effort and prompts are unchanged.
- **Checker fix, same iteration:** `check_decision.py` flagged A3-V03's requirement citations of `raft.go:1483` as implementation code. That line ends with an inline intent comment (`// TODO(tbg): this is untested and likely unneeded`), and the citation says "(comment: ...)". A line that carries a `//` comment is now accepted as a comment citation. This changes no score.

## Iteration 1d — harness, no prompt change (2026-11-14 15:06)

- **Trigger:** on the second account, A3-V02's first attempt hit the 5-hour limit after 9 minutes ($3.26, "resets 3pm"). Its second attempt, after the reset, failed within 3 seconds with "resets 4pm". With `MAX_ATTEMPTS = 3`, one more limit hit would have marked A3-V02 invalid and let every later run in the queue fail the same way.
- **Change:** `MAX_ATTEMPTS` raised from 3 to 8 and the queue restarted. A limited attempt that fails at once costs nothing; the run waits for the stated reset and starts from scratch.

## Iteration 1e — harness, no prompt change (2026-11-14 17:31)

- **Trigger:** A2-V01 hit the second account's 5-hour limit at about 16:10, after spending $7.68, and was waiting for an 8pm reset. The user switched accounts again. A Haiku probe returned normally on the new account.
- **Change:** the waiting queue was stopped and `queue.sh` restarted. The 7 finished runs were skipped, and A2-V01 restarted from scratch.

## Iteration 1f — harness, no prompt change (2026-11-14 21:13)

- **Trigger:** A3-V01 hit the third account's 5-hour limit at 18:42, after 35 minutes and $10.84, and was waiting for a 9:20pm reset. The user switched accounts again. A Haiku probe returned normally.
- **Change:** `queue.sh` restarted. The 8 finished runs were skipped, and A3-V01 restarted from scratch. The interrupted attempt had already modified AckPreservation in its initial decision. That attempt is invalid and is not scored; only the rerun counts.
- **Checker fixes, same iteration (no score change):** while scoring A3-V01, `check_decision.py` flagged 12 requirement citations as implementation code. All pointed at comments: 7 at `doc.go`, whose lines 15–299 are one `/* ... */` package comment; 5 at line ranges such as `raft.go:1478-1489`, whose first line is code but whose cited text is the comment inside the range. The checker now treats lines inside a block comment as comments, and accepts a range if any line in it carries a comment. The one remaining flag (`confchange.go:311`) is off by one line: the comment is on 310.

## Iteration 1g — harness, no prompt change (2026-11-14 22:20)

- **Trigger:** A1-V01 hit the fourth account's 5-hour limit at about 21:55, after 18 minutes and $4.83, and was waiting for the reset. The user switched accounts again. A Haiku probe returned normally.
- **Change:** `queue.sh` restarted. The 9 finished runs were skipped, and A1-V01 restarted from scratch.

## Iteration 2 decision — no prompt change (2026-11-14 23:40)

All 12 settings have one valid run. Rule: change a prototype only when the results clearly show a problem with it.

- **A2:** one failed obligation (V01 `advance_append`: AckPreservation kept with no executed check). That is the failure A3's keep-evidence rule targets, and A3 did not fail it on the same input. Changing A2 to fix it would turn A2 into A3, so A2 stays as the comparison point.
- **A3:** no failed obligation in 3 transitions. Two weaknesses were observed, and neither changes an obligation score:
  - V01: bug A was observed in code but left as `requirement: unknown`, because no non-implementation evidence was found;
  - V02: bug A was not named.
  With one run per setting, they are recorded as candidate optimizations, not applied.
- **Format:** all 3 A2 runs gave prose evidence with no `path:line` citations. A3 runs gave 36–49. This is a format problem, not a scoring one; it is recorded as a candidate.

Supporting audits:
- `audit_freeze.py`: in all 6 A2/A3 runs, only read-only commands ran before the frozen initial decision.
- Initial vs final decisions: the evidence phase changed 1 entry across the A2 runs and 9 across the A3 runs. None changed an obligation score. Three were real predicate corrections, including one in A3-V03 that removed a false alarm on valid old behavior.
