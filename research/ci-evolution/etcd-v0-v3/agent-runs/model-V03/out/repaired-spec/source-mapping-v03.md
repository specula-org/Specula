# V03 behavior and source map

The version binding is the supplied `/workspace/old/source` (V02) and `/workspace/new/source` (V03), plus `update.patch`. `assets/v02` preserves the entire actual inherited suite; no substitute transition system is used. Current action behavior remains in `base.tla`; MC, Update, Trace and the target adapter call those operators.

| Source function / caller | Model behavior | Validation boundaries |
|---|---|---|
| `raft.stepLeader`, MsgProp | `RewriteConf`, `StepLeaderProposal`, `Step` | pending below/equal/above applied, simple/joint, legacy NodeID=0, zero-change V2 Auto/Implicit/Explicit, mixed batches, rewriting before quota rejection |
| `increaseUncommittedSize`, `appendEntry` | `AppendEntry` | zero/15/16/17 held bytes, empty one/two entries, mixed payload, oversized first proposal; nonempty configuration payloads can still be quota-rejected |
| `raft.advance`, `Ready.appliedCursor`; RawNode/Node Advance | `AdvanceCore`, `ProtocolAdvance` | quota reduction precedes applying cursor; old applied strictly below pending; zero cursor, equality, beyond boundary, follower, post-Ready term/output/proposal; committed-entry and snapshot cursors; nil automatic leave and pending update |
| `confchange.Changer.initProgress`; `Simple`, `EnterJoint`, `LeaveJoint`, `Restore` | `ChangeProgress`, `ApplyConfCore`, `Restore` | Next=LastIndex (including zero), RecentActive; preserve existing progress, delete/re-add lifecycle, learner promotion/demotion/staging; live restore self MaybeUpdate(Next-1) |
| `raft.switchToConfig` | `ProbeConfig`, `ApplyConfCore`, unchanged `MaybeSendAppend` | commit-triggered broadcast versus one nonempty probe per progress; includes self and existing peers, paused Probe/Snapshot/full Replicate, caught-up, compacted tails; no snapshot fallback for empty refill |
| `switchToConfig`, `abortLeaderTransfer` | `ApplyConfCore` | cancel when transfer target leaves voter union, including demotion; staged outgoing voters remain eligible; early return on removed/demoted self preserves leader role and transfer |
| `newRaft`, `NewRawNode` | `RestartCore` | full ConfState, empty/nonempty storage, zero HardState; Restore's temporary progress is overwritten by becomeFollower/Reset (Next=Last+1, active=false, self Match=Last) |
| `RawNode.Bootstrap`, `StartNode`, `Init` | `InitialRaft`, `ProtocolInit`, MCInit, TraceInit | Bootstrap all entries before applying configuration: Next=number of bootstrap entries; one/three peers and differing order; immediate Campaign's legacy scan; Ready |
| snapshot restore / restart | `Restore`, `RestartCore` | incoming, outgoing, staged, current learner, removed self; first snapshot index; unchanged incoming/current-learner guard; restart differs from live restore |
| `node.run` confc and propc | `ProtocolApplyEntry`, `ProtocolPropose`, `WrapperLoop` | actual channels, callbacks followed by public Propose: legacy/V2 self-removal, staged self, self demotion, transfer demotion, new peer, already-removed self |
| unchanged consumers | `StepHup`, `StepVote`, `StepCandidate`, `StepLeaderAppResp`, `StepLeaderHeartbeatResp`, `StepCheckQuorum`, `StepLeaderTransfer`, Ready/Advance | prior local cases retained; newly initialized/reconfigured progress consumed by response, heartbeat, quorum, proposal and transfer calls |

`ChangeProgress` and the callback membership-before/after guard repair pre-existing model omissions, witnessed against V02 as well as V03. All other substantive core changes listed above follow this packet's source delta.

`campaign` now sorts recipients. The model and comparator represent messages as a multiset, preserving duplicates but omitting ordering between recipients; no new order claim is made. `log_unstable.maybeLastIndex/maybeTerm`, IsEmptyHardState spelling, lease-read temporary variable, formatting/parser helpers, comments and test harness additions were inspected. They introduce no additional transition change within this model's observation scope. `Simple` still calls checkAndCopy, apply and checkAndReturn; removing the redundant invariant check does not change the tested structurally valid inputs. Arbitrary malformed protobufs, corrupt tracker maps and unknown transitions are outside the descriptor domain.

No correctness predicate is weakened. AutoLeaveAdvance and ProposalContract intentionally retain the inherited meaning. See `property-phase-handoff.md`; these properties are not asserted in local action checking.

A further pre-existing repair separates the append return from the inherited `decision` observation. A rejected proposal between Ready and Advance leaves `decision=DropQuota`, even if the automatic append succeeds. `AdvanceCore` now consults `AppendQuotaExceeded` for that call; the observation and old predicates are unchanged. The added `appended` witness explicitly records whether the log grew. V02 quota-14 and V03 quota-14/17 failures and repairs are saved.

The injected configuration-broadcast panic case also preserves partial effects: source execution stops before transfer cancellation. `ApplyConfCore` now returns its fatal state before aborting transfer. The inherited model continued after fatal; this is a pre-existing local model repair, not a claimed reachable Raft bug.
