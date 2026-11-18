-------------------------------- MODULE MC --------------------------------
EXTENDS base
Original == INSTANCE base
CONSTANTS TickLimit, CampaignLimit, RequestLimit, CrashLimit, LossLimit,
          DuplicateLimit, TransferLimit, SnapshotLimit, CompactLimit,
          AvailabilityLimit, CancelLimit, ReportLimit, QuiesceLimit,
          MaxTermLimit, MaxLogLimit, MaxMsgBufferLimit, WorkloadKinds,
          AllowEmptyContext
VARIABLE faultCount
faultVars == <<faultCount>>
mcvars == <<vars,faultCount>>
Limits == [tick |-> TickLimit, campaign |-> CampaignLimit, request |-> RequestLimit,
    crash |-> CrashLimit, loss |-> LossLimit, duplicate |-> DuplicateLimit,
    transfer |-> TransferLimit, snapshot |-> SnapshotLimit, compact |-> CompactLimit,
    availability |-> AvailabilityLimit, cancel |-> CancelLimit,
    report |-> ReportLimit, quiesce |-> QuiesceLimit]
MCInit == Init /\ faultCount=[k\in DOMAIN Limits |-> 0]
Budget(k) == faultCount[k]<Limits[k]
Spend(k) == faultCount'=[faultCount EXCEPT ![k]=@+1]
\* All bounds apply to injected operations, never to their completion/response paths.
MCTick(n,t) == /\ Budget("tick") /\ Original!Tick(n,t) /\ Spend("tick")
MCCampaign(n,t) == /\ Budget("campaign") /\ Original!Campaign(n,t) /\ Spend("campaign")
MCInvoke(n,id,kind,target,w,z,parent,ctx) ==
    /\ Budget("request") /\ kind\in WorkloadKinds /\ (AllowEmptyContext \/ ctx#0)
    /\ Original!Invoke(n,id,kind,target,w,z,parent,ctx) /\ Spend("request")
MCInvokeV2(n,id,changes,transition,w,z,parent) ==
    /\ Budget("request") /\ "V2"\in WorkloadKinds
    /\ Original!InvokeV2(n,id,changes,transition,w,z,parent) /\ Spend("request")
MCCrash(n) == /\ Budget("crash") /\ Original!Crash(n) /\ Spend("crash")
MCLose(m) == /\ Budget("loss") /\ Original!Lose(m) /\ Spend("loss")
MCDuplicate(m) == /\ Budget("duplicate") /\ Original!Duplicate(m) /\ Spend("duplicate")
MCTransfer(n,p,t) == /\ Budget("transfer") /\ Original!TransferLeader(n,p,t) /\ Spend("transfer")
MCCreateSnapshot(n,k) == /\ Budget("snapshot") /\ Original!CreateSnapshot(n,k) /\ Spend("snapshot")
MCCompact(n,k) == /\ Budget("compact") /\ Original!Compact(n,k) /\ Spend("compact")
MCAvailability(n,available) == /\ Budget("availability")
    /\ Original!SnapshotAvailability(n,available) /\ Spend("availability")
MCCancel(id) == /\ Budget("cancel") /\ Original!Cancel(id) /\ Spend("cancel")
MCReportSnapshot(n,m,failed,t) == /\ Budget("report")
    /\ Original!ReportSnapshot(n,m,failed,t) /\ Spend("report")
MCReportUnreachable(n,m,t) == /\ Budget("report")
    /\ Original!ReportUnreachable(n,m,t) /\ Spend("report")
MCQuiesce(n) == /\ Budget("quiesce") /\ Original!TickQuiesced(n) /\ Spend("quiesce")
MCNext ==
    \/ /\ Original!ReactiveActions /\ UNCHANGED faultVars
    \/ \E n\in Server,t\in Timeouts:MCTick(n,t) \/ MCCampaign(n,t) \/
                                  (\E p\in Server:MCTransfer(n,p,t))
    \/ \E n\in Server,id\in RequestId,kind\in WorkloadKinds,target\in Server\cup {0},
          w\in PayloadWeights,z\in EncodedWeights,parent\in RequestId\cup {0}:
          \E ctx\in {id,0}:MCInvoke(n,id,kind,target,w,z,parent,ctx)
    \/ \E n\in Server,id\in RequestId,changes\in V2Batches,
          transition\in {"Auto","JointImplicit","JointExplicit"},
          w\in PayloadWeights,z\in EncodedWeights,parent\in RequestId\cup {0}:
          MCInvokeV2(n,id,changes,transition,w,z,parent)
    \/ \E n\in Server:MCCrash(n) \/ MCQuiesce(n) \/
          (\E k\in 1..Last(raft[n]):MCCreateSnapshot(n,k) \/ MCCompact(n,k)) \/
          MCAvailability(n,TRUE) \/ MCAvailability(n,FALSE)
    \/ \E id\in RequestId:MCCancel(id)
    \/ \E m\in DOMAIN wire:MCLose(m) \/ MCDuplicate(m)
    \/ \E m\in history.sent,t\in Timeouts:MCReportUnreachable(m.from,m,t) \/
                                    (\E failed\in BOOLEAN:MCReportSnapshot(m.from,m,failed,t))
MCSpec == MCInit /\ [][MCNext]_mcvars
\* Source terms do not wrap. These state constraints prune exploration explicitly.
StateConstraint ==
    /\ \A n\in Server:raft[n].term<=MaxTermLimit /\ Last(raft[n])<=MaxLogLimit
    /\ BagCardinality(wire)<=MaxMsgBufferLimit
    /\ \A n\in Server:BagCardinality(raft[n].out)<=MaxMsgBufferLimit
\* REQ-EVIDENCE MCTypeOK
\* intent:   TypeOK holds and every fault-budget counter is a natural number within its configured limit.
\* status:   model-internal
\* verified: V02
\* note:     fault budgets are model-checking bookkeeping; the TypeOK part carries its own block in base.tla.
\* review:   ok
MCTypeOK == TypeOK /\ faultCount\in [DOMAIN Limits -> Nat] /\
                          (\A k\in DOMAIN Limits:faultCount[k]<=Limits[k])
\* Bootstrap order pins bootstrap identities; only equal-option joining IDs permute.
Symmetry == {p\in Permutations(Server):
    /\ \A k\in DOMAIN BootPeers:p[BootPeers[k]]=BootPeers[k]
    /\ \A n\in Server:
        /\ (n\in Joining)=(p[n]\in Joining)
        /\ (n\in RawNodes)=(p[n]\in RawNodes)
        /\ (n\in PreVoteNodes)=(p[n]\in PreVoteNodes)
        /\ (n\in CheckQuorumNodes)=(p[n]\in CheckQuorumNodes)
        /\ (n\in NoForwardNodes)=(p[n]\in NoForwardNodes)}
\* Diagnostic projection only: cfgs retain counters in fingerprinting. Hiding budget
\* counters can merge states with different remaining enabled faults unsoundly.
MCView == vars

(***************************************************************************
Progress targets are separate from finite safety exploration. They are NOT
claimed checked by MC.cfg: fault exhaustion/state constraints break fairness.
Fairness is action-specific and all availability/timing premises are explicit.
See model-notes.md for the remaining unbounded liveness-driver obligation.
***************************************************************************)
LeaderExists == \E n\in Server:raft[n].alive /\ raft[n].role="Leader"
FairCaller == \A n\in Server:
    /\ WF_vars(Ready(n)) /\ WF_vars(Publish(n)) /\ WF_vars(QueueApplication(n))
    /\ WF_vars(Advance(n)) /\ WF_vars(ApplySnapshot(n)) /\ WF_vars(FinishApplication(n))
    /\ WF_vars(StorageApplySnapshot(n)) /\ WF_vars(StorageAppend(n)) /\ WF_vars(StorageSetHardState(n))
    /\ WF_vars(\E t\in Timeouts:ApplyEntry(n,t) \/ Restart(n,t))
    /\ \A part\in {"All","Entries","HS","Snapshot"}:
             WF_vars(StartPersist(n,part)) /\ WF_vars(CompletePersist(n,part))
StableLeader(n) == <>[](raft[n].alive /\ raft[n].role="Leader" /\ Promotable(raft[n]))
StableServices == <>[](\A n\in Server:Live(n) /\ raft[n].snapAvailable)
\* A candidate gets a quiet term while votes are serviced: the needed timing window,
\* not an assumption that it wins. Other nodes may still receive/respond and persist.
QuietCampaign(n) == <>[][
    (raft[n].role\in {"Candidate","PreCandidate"} /\
     raft'[n].role\in {"Candidate","PreCandidate"}) =>
         (raft'[n].term=raft[n].term /\ raft[n].yes\subseteq raft'[n].yes /\
          raft[n].no\subseteq raft'[n].no)]_vars
FairNetwork == \A n,p\in Server:
    SF_vars(\E m\in DOMAIN wire,t\in Timeouts:m.from=n /\ m.to=p /\ Receive(m,t))
CommonConfiguration == \A n,p\in Server:raft[n].config=raft[p].config
\* REQ-EVIDENCE ElectionProgress
\* intent:   Under stable services, an eventually common configuration, a fair caller and network, and some promotable node that gets quiet campaign windows and campaigns strongly fairly, a leader eventually exists.
\* status:   requirement
\* evidence: test source/raft_test.go:3700 TestNodeWithSmallerTermCanCompleteElection "Previously the cluster would come to a standstill when run with PreVote" -> an election that cannot complete is a bug (eventual leader)
\* evidence: test source/raft_paper_test.go:188 TestLeaderElectionInOneRoundRPC "a) it wins the election" -> a candidate that gets a quorum of votes becomes leader
\* evidence: doc source/doc.go:209 "candidate has not received any heartbeat before the election timeout, it" -> a promotable node that times out campaigns
\* evidence: impl source/raft.go:662 "if r.promotable() && r.pastElectionTimeout() {"
\* watch:    raft.go:tickElection; raft.go:campaign; raft.go:Step (MsgHup, vote handling); raft.go:stepCandidate; raft.go:resetRandomizedElectionTimeout; raft.go:pastElectionTimeout
\* verified: V02
\* note:     commented out in every cfg (e.g. MC.cfg:80); MC.tla:83-86 says progress is not claimed checked under finite budgets. The library's stated aim is election progress (standstill was treated as a bug), but no doc states this exact premise set.
\* review:   ok
ElectionProgress ==
    (StableServices /\ <>[]CommonConfiguration /\ FairCaller /\ FairNetwork /\
     (\E n\in Server:<>[]Promotable(raft[n]) /\ QuietCampaign(n) /\
       SF_vars(\E t\in Timeouts:Campaign(n,t)))) => <>LeaderExists
\* REQ-EVIDENCE CatchupProgress
\* intent:   With a stable leader n, a stable member p, stable services and fair execution, every index committed at n is eventually applied by p.
\* status:   requirement
\* evidence: test source/raft_paper_test.go:433 TestLeaderCommitEntry "and it includes that index in future AppendEntries RPCs so that the other" -> followers eventually learn the leader's commit index
\* evidence: comment source/node.go:196 "it could end up in a limbo, never getting any" -> a follower must not be left without updates from the leader
\* evidence: doc source/design.md:40 "leader sends at most one `replication message` per heartbeat interval" -> a probing follower keeps receiving replication messages each heartbeat
\* evidence: impl source/raft.go:1155 "if pr.Match < r.raftLog.lastIndex() {"
\* watch:    raft.go:bcastAppend; raft.go:maybeSendAppend; raft.go:stepLeader (MsgAppResp, MsgHeartbeatResp, MsgSnapStatus); tracker/progress.go:IsPaused; tracker/progress.go:BecomeProbe; log.go:nextEnts
\* verified: V02
\* note:     commented out in every cfg; MC.tla:83-86 says not claimed checked.
\* review:   ok
CatchupProgress == \A n,p\in Server:
    (StableLeader(n) /\ StableServices /\ FairCaller /\ FairNetwork /\
     <>[](p\in Members(raft[n])) /\
     WF_vars(\E t\in Timeouts:Tick(n,t))) =>
       (\A k\in Nat: (raft[n].commit>=k) ~> (Len(application[p].hist)>=k))
\* Once a change is committed/released, ordered continuing callbacks must finish.
\* REQ-EVIDENCE ManagementProgress
\* intent:   Under stable services and a fair caller, every configuration entry committed at a node is eventually applied by that node's application.
\* status:   requirement
\* evidence: doc source/README.md:178 "After config change is committed, some committed entry with type raftpb.EntryConfChange" -> a committed configuration entry is handed to the application, which must apply it
\* evidence: comment source/node.go:170 "ProposeConfChange) to the node. This must be called whenever a config" -> the application must apply every configuration change it observes
\* evidence: doc source/README.md:120 "ApplyConfChange must be called one way or the other" -> the application must apply it even when cancelling
\* evidence: impl source/log.go:153 "if l.committed+1 > off {"
\* watch:    log.go:nextEnts; log.go:hasNextEnts; node.go:newReady; raft.go:advance; node.go:run (confc)
\* verified: V02
\* note:     commented out in every cfg; the obligation is shared between the library (emit committed entries) and the caller (apply them).
\* review:   ok
ManagementProgress == (StableServices /\ FairCaller) =>
    (\A n\in Server,id\in RequestId:
        (\E e\in SeqSet(Prefix(Hist(raft[n]),raft[n].commit)):e.id=id /\ e.kind\in ConfKinds)
        ~> (\E e\in SeqSet(application[n].hist):e.id=id))
\* REQ-EVIDENCE TransferSettlement
\* intent:   A leader with a pending leadership transfer whose ticks are fair, and whose transferee is not repeatedly replaced, eventually clears the transfer or stops being leader.
\* status:   requirement
\* evidence: test source/raft_test.go:3522 TestLeaderTransferTimeout "Transfer leadership to isolated node, wait for timeout." -> a pending transfer is cleared after the election timeout while the node stays leader
\* evidence: test source/raft_test.go:3646 TestLeaderTransferSecondTransferToSameNode "to the same node should not extend the timeout while the first one is pending." -> repeated same-target requests do not postpone clearing
\* evidence: comment source/raft.go:1227 "Transfer leadership should be finished in one electionTimeout, so reset r.electionElapsed." -> a transfer is meant to finish within one election timeout
\* evidence: impl source/raft.go:678 "If current leader cannot transfer leadership in electionTimeout, it becomes leader again."
\* evidence: impl source/raft.go:680 "r.abortLeaderTransfer()"
\* watch:    raft.go:tickHeartbeat; raft.go:abortLeaderTransfer; raft.go:reset; raft.go:stepLeader (MsgTransferLeader); raft.go:switchToConfig
\* verified: V02
\* note:     commented out in every cfg.
\* review:   retyped the narrating raft.go:678 comment to impl and added the raft.go:1227 rule comment; the tests still support the intent, so status unchanged.
TransferSettlement == \A n\in Server:
    (StableServices /\ WF_vars(\E t\in Timeouts:Tick(n,t)) /\
     <>[][raft'[n].transfer\in {0,raft[n].transfer}]_vars) =>
         ((raft[n].transfer#0) ~> (raft[n].transfer=0 \/ raft[n].role#"Leader"))
\* Delivered, correlated reads complete after a reachable caller fence; retried
\* request-to-ReadState progress additionally needs a liveness harness (not claimed).
\* REQ-EVIDENCE ReadProgress
\* intent:   Under stable services, a fair caller and a strongly fair CompleteRead, a read whose completion becomes enabled is eventually completed.
\* status:   model-internal
\* verified: V02
\* note:     the conclusion follows from the premise on the model's own caller action (CompleteRead), so this checks the caller model, not the library; MC.tla:126-127 says request-to-ReadState progress is not claimed. Searched rawnode.go:233-236, node.go:180-183 and read_only.go for a library-level read liveness statement and found none. Commented out in every cfg.
\* review:   ok
ReadProgress == (StableServices /\ FairCaller) =>
    (\A n\in Server,id\in RequestId:
       SF_vars(\E k\in DOMAIN application[n].reads:CompleteRead(n,id,k)) =>
       ((\E k\in DOMAIN application[n].reads:ENABLED CompleteRead(n,id,k)) ~> requests[id].completed))
=============================================================================
