----------------------- MODULE ConfigurationProgress -----------------------
EXTENDS Trace
CONSTANTS ProgressSeeds, AllowTransfer, StallDelivery
VARIABLES seed, slot, transferUsed, exercised
progressVars == <<traceVars,seed,slot,transferUsed,exercised>>
SeedPost == Decode(TraceLog[seed].post)
SeedParams == Decode(TraceLog[seed].params)
Origin == SeedParams.node
TrackedRequest == SeedParams.id
TrackedEntry == Hist(SeedPost.raft[Origin])[Len(Hist(SeedPost.raft[Origin]))]
\* Starting evidence is an actual accepted but uncommitted proposal, including
\* pending-configuration rewrites. The source trace proves admission separately.
NonvacuousPendingRequest ==
    /\ SeedPost.requests[TrackedRequest].kind\in ConfKinds
    /\ SeedPost.requests[TrackedRequest].core="Accepted"
    /\ SeedPost.requests[TrackedRequest].handoff
    /\ TrackedEntry.index>SeedPost.raft[Origin].commit
    /\ TrackedEntry.index>Len(SeedPost.application[Origin].hist)
    /\ \A n\in Server:SeedPost.raft[n].alive
EntryApplied(n) == Len(application[n].hist)>=TrackedEntry.index /\
                    application[n].hist[TrackedEntry.index]=TrackedEntry
Settled == \A n\in SeqSet(BootPeers):EntryApplied(n)
\* Cyclic caller/network service, not a successful replay suffix. One node's
\* legal service action per slot, arbitrary selection among its valid messages.
\* This finite scenario assumes reliable delivery, available storage, no new
\* crashes/proposals/timeouts and at most one ordinary leadership transfer.
Services == <<"Ready","StartPersist","CompletePersist","StorageApplySnapshot",
    "StorageAppend","StorageSetHardState","Publish","QueueApplication",
    "Advance","ApplyEntry","FinishApplication","Receive","ReturnAPI">>
Slots == Len(Services)*Cardinality(Server)
Nodes == SetSequence(Server)
NodeAt(k) == Nodes[((k-1) % Cardinality(Server))+1]
ServiceAt(k) == Services[((k-1)\div Cardinality(Server))+1]
\* Default explores any valid delivery; the explicitly small serial configs
\* replace Delivery with a fixed choice per receiver, without success filtering.
Delivery(n) == \E m\in DOMAIN wire:m.to=n /\ Receive(m,raft[n].timeout)
SerialDelivery(n) == LET messages=={m\in DOMAIN wire:m.to=n} IN
    /\ messages#{} /\ Receive(CHOOSE m\in messages:TRUE,raft[n].timeout)
Publication(n) == Publish(n)
SerialPublication(n) == /\ Publish(n)
    /\ IF ready[n].remainingMessages=EmptyBag THEN TRUE
        ELSE wire'=AddBag(wire,CHOOSE m\in DOMAIN ready[n].remainingMessages:TRUE)
Service(n,s) ==
    CASE s="Ready" -> Ready(n)
      [] s="StartPersist" -> StartPersist(n,"All")
      [] s="CompletePersist" -> CompletePersist(n,"All")
      [] s="StorageApplySnapshot" -> StorageApplySnapshot(n)
      [] s="StorageAppend" -> StorageAppend(n)
      [] s="StorageSetHardState" -> StorageSetHardState(n)
      [] s="Publish" -> Publication(n)
      [] s="QueueApplication" -> QueueApplication(n)
      [] s="Advance" -> Advance(n)
      [] s="ApplyEntry" -> ApplyEntry(n,raft[n].timeout)
      [] s="FinishApplication" -> FinishApplication(n)
      [] s="Receive" -> /\ ~StallDelivery
             /\ Delivery(n)
      [] OTHER -> n=Origin /\ ReturnAPI(TrackedRequest)
ProgressInit ==
    /\ seed\in ProgressSeeds
    /\ LET p==SeedPost IN
       /\ raft=[n\in Server |-> Override(InitialRaft(n,p.raft[n].timeout),p.raft[n])]
       /\ disk=p.disk /\ ready=p.ready /\ application=p.application
       /\ requests=p.requests /\ wire=p.wire /\ history=EmptyHistory
    /\ quality=EmptyQuality /\ l=seed+1 /\ slot=1
    /\ transferUsed=FALSE /\ exercised={}
Pump ==
    /\ ~Settled
    /\ LET n==NodeAt(slot) s==ServiceAt(slot) IN
         IF ENABLED Service(n,s) THEN
             /\ Service(n,s)
             /\ exercised'=exercised\cup {[node |-> n,action |-> s]}
         ELSE /\ UNCHANGED vars /\ UNCHANGED exercised
    /\ slot'=(slot % Slots)+1
    /\ UNCHANGED <<l,seed,transferUsed>>
\* Public transfer, once, may occur at any service position while node 1 leads.
\* This is a scenario input, not a success/freshness/promotion guard.
Handoff == /\ ~Settled /\ AllowTransfer /\ ~transferUsed /\ raft[Origin].role="Leader"
    /\ TransferLeader(Origin,2,raft[Origin].timeout)
    /\ transferUsed'=TRUE
    /\ exercised'=exercised\cup {[node |-> Origin,action |-> "TransferLeader" ]}
    /\ UNCHANGED <<l,seed,slot>>
\* Cancellation of the API wait after handoff leaves a logged command intact.
CancelWait == /\ ~Settled /\ Cancel(TrackedRequest)
    /\ exercised'=exercised\cup {[node |-> Origin,action |-> "Cancel" ]}
    /\ UNCHANGED <<l,seed,slot,transferUsed>>
ProgressNext == Pump \/ Handoff \/ CancelWait
ProgressSpec == ProgressInit /\ [][ProgressNext]_progressVars /\ WF_progressVars(Pump)
PendingConfigurationProgress == <>Settled
\* Deliberately false coverage probes: witnesses are model reachability evidence.
NoDistributedCommit == ~\E n\in Server:raft[n].commit>=TrackedEntry.index
NoApplicationAfterTransfer == ~(Settled /\ transferUsed /\ raft[Origin].role#"Leader")
=============================================================================
