# Driver and reference audit

No original source or behavior-model file was edited. Input hashes were checked before and after the work. There were no source-backed modeling repairs. Changes described here are changes to new scenario drivers under `out/`.

## Reachability and full-reference inclusion

`C03Progress.DriverInit` calls the selected version's original `Init`. It selects only the original trace's legal initial timeout assignment (auto prefix: 1→4, 2→4, 3→5, 4→6; explicit prefix: 1→7, 2→5, 3→4, 4→6); it does not import the recorded raft, disk, Ready, application, or network states. Settings are explicit constants. The Node scenarios change `RawNodes` to `{}` before Init, so they are fresh Node MODEL executions.

The first 152 transitions call `Trace.MatchEvent(TraceLog[l])` for trace events 2 through 153. `PrefixApplicable` checks ENABLED at every prefix position. There is no `ValidatePostState` or old-post equality. Every event must execute; a disabled event fails the run. The original complete 153-event recorded prefixes are saved as `*-prefix-full.ndjson`. The smaller `*-prefix-inputs.ndjson` retains event 1's settings/initial timeout evidence and all subsequent exact event inputs, with unused post fields replaced by typed atom 0. This is a loading optimization, not a state abstraction. It reduced JSON initialization from roughly 30 seconds to about a second.

All suffix protocol transitions call the original `Ready`, `StartPersist`, `CompletePersist`, `StorageApplySnapshot`, `StorageAppend`, `StorageSetHardState`, `Publish`, `QueueApplication`, `ApplyEntry`, `FinishApplication`, `Advance`, `Receive`, `ReturnAPI`, `Tick`, and `TransferLeader` actions. `DeferApplication` changes only caller scheduling variables and is a stutter in `vars`. These actions are members of `base.Next` with parameters in its original domains. No core function is overridden and no transition assigns a convenient protocol state.

`C03Clocked` starts a heartbeat round only after existing queues, Ready work, application jobs and pending updates drain. The leader's original Tick generates the heartbeat; every other voter in its configuration receives one original Tick before service resumes. Reliable FIFO-independent selection drains the resulting work before another round. Followers receive heartbeats before reaching election timeout. Nodes outside the leader's voter configuration are not required to tick; all four servers still receive caller/network service. Every voter ticks forever on both failing loops.

The service scheduler cyclically scans 56 service positions (14 service types × 4 nodes), executes the first enabled position, and resumes scanning immediately after it. Omitting disabled positions adds no protocol transition. `WF(ClockPump)`, `WF(FollowerTick)`, and `WF(ClockReplay)` exclude stopping a pending service cycle. Publication/delivery use fixed TLC `CHOOSE` selection within each node's current finite bag. This is a serialized reliable network scenario, explicitly narrower than every possible message permutation. Branching is real: the optional transfer can be inserted between any reference actions before the original leader's first automatic proposal; optional entering-entry deferral can start at any eligible caller position/node. Neither suffix is a prescribed success/failure replay.

The transfer window is `~proposed`, a retained history fact about whether any automatic exit has yet been proposed. This bounds injected interactions, not service or the response deadline. There is at most one transfer and at most one deferral. The budgets (`transferUsed`, `earlyUsed`) remain in state and VIEW. No term/log/state constraints, tick budget, retry bound, or temporal cutoff are used for focused progress checks.

## VIEW dependency audit

`IdentityView` changes only these fields for fingerprinting:

- `raft[n].readySeq := 0`;
- `ready[n].id := 0`;
- `application[n].jobs[k].batch := 0`.

`ClockView` additionally retains `tickPending`. Every other state field is retained: full raft/storage/network/caller state, all history and quality records, real terms/logs/quotas/cursors, fault/interaction budgets, episode monitors, scheduler position and last-event record. Server IDs, entry IDs and request IDs are untouched.

The source-model audit is saved in `identity-uses-all-models.txt`. In V03 `base.tla`, readySeq is initialized at 827, incremented to form Ready.id at 987, and copied back at 1006. Ready.id is copied into an application-job batch at 1104. No behavior guard or checked property compares these identities; job.batch is never read. The `b.id` at 433 is a **raft node ID**, not Ready.id, and is retained. `history.readyChecks`, acknowledgements, and Quality observations do not record the three erased identities. V02 has the corresponding same dependency pattern.

Thus renaming these monotonically increasing allocation identities preserves enabled actions and all checked predicates. A reported back edge is a quotient cycle: in the concrete execution IDs continue increasing. There is no claim that all concrete variables literally repeat.

To check that this quotient did not invent the findings, `ReplayLeadership` and `ReplayDeferred` replay the extracted exact reference actions from Init, through the whole stem and **two copies of the loop**, with no VIEW. They retain the real IDs and all reference state. `Applicable`, `NoFatal`, `EndStillJoint`, and `ReachedEnd` all pass. The input scripts include the precise Receive/Publish message values, not just action names. Their JSON counterpart is `reference-actions.json` beside each primary counterexample. These are post-discovery concretization checks, not the branching searches that discovered the counterexamples.

## Developmental driver issues, preserved rather than hidden

- The first standalone SANY call used the wrong module directory; it could not find `base`. Subsequent TLC parses and semantic processing succeeded from isolated run directories.
- Early driver drafts had a conjunction indentation error, missing parentheses around Boolean assignments, and an action-level disjunction that evaluated CHOOSE on an empty publication bag. These runs are errors, not property evidence. The final driver uses guarded IF for publication.
- The first V02 cfg referenced V03-only TraceAutoLeave operators. V02 configs now retain their original source-backed weights (payload 2, encoding 10); V03 uses payload 0, encoding 6. Caller/input domains are otherwise equal.
- The first optional Early action only ran when Advance was already enabled. The normal pump could apply the entering entry before all messages were published, preventing that action from testing late installation on the leader. Its passing runs and the nonvacuity probe are reported as undercoverage. The final driver allows the caller to defer application, continue publishing/persisting, Advance when the original action permits it, and then finish application in order.
- Allowing deferral of any entry found a separate duplicate-leave/fatal trace in both versions. That was saved, then the liveness search was narrowed to deferral while the **entering entry at index 5** remained queued. No fatal state was erased or repaired in the behavior model.
- Initial broad transfer searches timed out. Final searches restrict injection to before the first automatic proposal, still exploring every transfer placement in that window, and include all-voter ticks.
- The supplied default MC workload omits V2. Its ordinary run was a resource/safety baseline. A second ordinary configuration adds V2 to the workload without changing behavior or other bounds. Both timeouts are inconclusive for liveness.
