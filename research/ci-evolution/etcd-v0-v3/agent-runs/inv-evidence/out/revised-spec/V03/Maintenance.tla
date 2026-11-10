---------------- MODULE Maintenance ----------------
EXTENDS base
RevisedCampaignContract(o) ==
    LET tick==o.trigger="Tick"
        due==~tick \/ (o.role#"Leader" /\ o.elapsed+1>=o.timeout)
        ignore==~due \/ o.role="Leader" \/ o.node\notin o.voters
        badSlice==~ignore /\ o.applied+1<o.first
        pending==\E k\in (o.applied+1)..o.commit:o.hist[k].kind\in ConfKinds
        blocked==ignore \/ pending \/ badSlice
        singleton==JointWon(o.config,{o.node})
        expected==IF blocked \/ singleton THEN {} ELSE
            {[from |-> o.node,to |-> n,type |-> IF o.pre THEN "MsgPreVote" ELSE "MsgVote",
              term |-> o.term+1,index |-> Len(o.hist),
              logTerm |-> IF o.hist= <<>> THEN 0 ELSE o.hist[Len(o.hist)].term,
              forced |-> FALSE,count |-> 1]:n\in o.voters\{o.node}}
    IN /\ o.voteRequests=expected
       /\ IF tick /\ o.role="Leader" THEN o.afterTerm=o.term
          ELSE IF badSlice THEN o.fatal="Hup unapplied slice compacted"
          ELSE IF blocked THEN o.afterRole=o.role /\ o.afterTerm=o.term
          ELSE /\ o.fatal=""
               /\ o.afterRole=IF singleton THEN "Leader" ELSE IF o.pre THEN "PreCandidate" ELSE "Candidate"
               /\ o.afterTerm=o.term+(IF ~o.pre \/ singleton THEN 1 ELSE 0)


VARIABLE audit
EmptyAudit == [advances |-> {}, ready |-> {}, proposals |-> {}, switches |-> {}]
AdvanceObservation(r,b,a) == [before |-> Hist(r), after |-> Hist(a),
 oldSnap |-> r.usnap.index,batchSnap |-> b.snapshot.index,afterSnap |-> a.usnap.index,
 cursor |-> b.cursor,applied |-> a.applied,oldApplied |-> r.applied,
 config |-> r.config,role |-> r.role,term |-> r.term,pendingBefore |-> r.pendingConf,
 pendingAfter |-> a.pendingConf,quotaBefore |-> r.quota,quotaAfter |-> a.quota,
 committedWeight |-> Weight(b.committed),fatal |-> a.fatal,decision |-> a.decision,raw |-> r.id\in RawNodes,
 outBefore |-> r.out,outAfter |-> a.out,readsBefore |-> r.readStates,readsAfter |-> a.readStates,
 ssBefore |-> r.prevSS,ssAfter |-> a.prevSS,batchReads |-> b.reads,
 hsBefore |-> r.prevHS,hsAfter |-> a.prevHS,batchHS |-> b.hs]
ReadyObservation(r,b,a) == [raw |-> r.id\in RawNodes,
 outBefore |-> r.out,outAfter |-> a.out,readsBefore |-> r.readStates,readsAfter |-> a.readStates,
 quotaBefore |-> r.quota,quotaAfter |-> a.quota,batch |-> b,
 ssBefore |-> r.prevSS,ssAfter |-> a.prevSS,hsBefore |-> r.prevHS,hsAfter |-> a.prevHS,
 appliedBefore |-> r.applied,appliedAfter |-> a.applied,
 unstableBefore |-> r.unstable,unstableAfter |-> a.unstable]
RevisedProposalObservation(r,es,a,qs) == ProposalObservation(r,es,a,qs) @@
 [config |-> r.config,beforeTerm |-> r.term,afterPending |-> a.pendingConf]
SwitchObservation(r,a) == [node |-> r.id,role |-> r.role,before |-> r.config,
 after |-> a.config,oldTransfer |-> r.transfer,afterTransfer |-> a.transfer,fatal |-> a.fatal]
\* These observers consume real pre/post states, never decide protocol behavior.
AuditNext == [
 advances |-> {AdvanceObservation(raft[n],ready[n],raft'[n]):
   n\in {i\in Server:ProtocolAdvance(i)}},
 ready |-> {ReadyObservation(raft[n],ready'[n],raft'[n]):
   n\in {i\in Server:ProtocolReady(i)}},
 proposals |-> {o @@ [config |-> raft[o.node].config,beforeTerm |-> raft[o.node].term,
   afterPending |-> raft'[o.node].pendingConf]:o\in quality'.proposals},
 switches |-> {SwitchObservation(raft[o.node],raft'[o.node]):o\in quality'.effects}]
MaintainedInit == Init /\ audit=EmptyAudit
MaintainedNext == Next /\ audit'=AuditNext
maintainedVars == <<vars,audit>>
MaintainedSpec == MaintainedInit /\ [][MaintainedNext]_maintainedVars
RevisedCampaignDecisionEligibility == \A o\in quality.campaigns:RevisedCampaignContract(o)
ActualBootstrap(e,k) == k\in DOMAIN BootLog /\ e=BootLog[k]
RevisedConfigurationTransitionSafety == \A c\in history.commitUses:
 \A k\in (c.oldCommit+1)..Len(c.hist):
  (c.hist[k].kind\in ConfKinds /\ ~ActualBootstrap(c.hist[k],k)) =>
   c.config=ConfigOf(Prefix(c.hist,k-1))
CanonicalLeave(e,a,w,z) == e=V2Entry(a.term,Len(a.before)+1,0,<<>>,"Auto",w,z)
AdvanceEnvelope(a) ==
 /\ (a.oldSnap#0 /\ a.oldSnap#a.batchSnap => a.afterSnap=a.oldSnap)
 /\ (a.cursor#0 => a.applied=a.cursor)

RevisedAutoLeaveContract(a) ==
 LET trigger==a.config.autoLeave /\ a.role="Leader" /\ a.cursor>0 /\
              a.oldApplied<a.pendingBefore /\ a.pendingBefore<=a.cursor
 IN /\ a.fatal=""
    /\ IF trigger THEN
         /\ a.after=Append(a.before,V2Entry(a.term,Len(a.before)+1,0,<<>>,"Auto",0,AutoLeaveEncoded))
         /\ a.pendingAfter=Len(a.before)+1
       ELSE a.after=a.before /\ a.pendingAfter=a.pendingBefore
    /\ a.quotaAfter=Max(0,a.quotaBefore-a.committedWeight)
RevisedAckPreservation == \A a\in audit.advances:
 AdvanceEnvelope(a) /\ RevisedAutoLeaveContract(a) /\
 (a.after#a.before => ~\E k\in (a.oldApplied+1)..Len(a.before):IsLeave(a.before[k]) /\ a.before[k].id=0)
RevisedAutoLeaveAdvance == \A a\in audit.advances:RevisedAutoLeaveContract(a)

RevisedReadyContract(o) ==
 /\ o.quotaAfter=o.quotaBefore
 /\ o.batch.messages=o.outBefore /\ o.batch.reads=o.readsBefore
 /\ o.outAfter=EmptyBag /\ o.readsAfter= <<>>
 /\ o.ssAfter=o.batch.ss
 /\ o.hsAfter=o.hsBefore /\ o.appliedAfter=o.appliedBefore
 /\ o.unstableAfter=o.unstableBefore
RevisedReadyOwnership == \A o\in audit.ready:RevisedReadyContract(o)
PendingOutputContract(a) == a.outAfter=a.outBefore /\ a.readsAfter=a.readsBefore /\ a.ssAfter=a.ssBefore
AdvancePreservesPendingOutput == \A a\in audit.advances:PendingOutputContract(a)
\* Same original pagination/cursor predicate, supplied ACTUAL lost observations.
ActualLostReads == {a\in audit.advances:a.readsBefore#a.readsAfter}
RevisedReadyAccounting ==
 LET H==INSTANCE base WITH history <- [history EXCEPT !.lostReads=ActualLostReads]
 IN H!ReadyAccounting

\* Independent content oracle: never calls protocol RewriteConf.
ContractLeave(e) == e.kind="V2" /\ e.changes= <<>> /\ e.transition="Auto"
RECURSIVE ContractBatch(_,_,_,_,_)
ContractBatch(es,c,p,applied,last) ==
 IF es= <<>> THEN [entries |-> <<>>,pending |-> p] ELSE
 LET e==Head(es)
     refuse==e.kind\in ConfKinds /\ (p>applied \/
       (c.outgoing#{} /\ ~ContractLeave(e)) \/ (c.outgoing={} /\ ContractLeave(e)))
     effective==IF refuse THEN Entry(0,0,"Normal",0,0,0,EmptyEncoded) ELSE e
     nextPending==IF e.kind\in ConfKinds /\ ~refuse THEN last+1 ELSE p
     rest==ContractBatch(Tail(es),c,nextPending,applied,last+1)
 IN [entries |-> <<effective>>\o rest.entries,pending |-> rest.pending]
RevisedExpectedDecision(o) ==
 IF o.role="Leader" THEN
  IF ~o.member THEN "DropRemoved" ELSE IF o.transfer#0 THEN "DropTransfer"
  ELSE IF o.quota>0 /\ o.weight>0 /\ o.quota+o.weight>MaxUncommitted THEN "DropQuota" ELSE "Accepted"
 ELSE IF o.role#"Follower" \/ o.lead=0 THEN "DropNoLeader"
 ELSE IF ~o.forwarding THEN "DropForwardDisabled" ELSE "Forwarded"
ProposalOutcome(o) ==
 LET b==ContractBatch(o.entries,o.config,o.pending,o.applied,Len(o.before))
 IN [role |-> o.role,member |-> o.node\in o.voters\cup o.learners,
 transfer |-> o.transfer,quota |-> o.quota,weight |-> Weight(b.entries),
 lead |-> o.lead,forwarding |-> ~o.noForward,decision |-> o.decision]
RevisedProposalContract(o) ==
 LET b==ContractBatch(o.entries,o.config,o.pending,o.applied,Len(o.before))
     expected==RevisedExpectedDecision(ProposalOutcome(o))
     assigned==[k\in DOMAIN b.entries |-> [b.entries[k] EXCEPT !.term=o.beforeTerm,!.index=Len(o.before)+k]]
 IN /\ o.entries# <<>> /\ o.decision=expected
    /\ IF expected="Accepted" THEN
         /\ o.after=o.before\o assigned /\ o.afterPending=b.pending
         /\ \A e\in SeqSet(b.entries):e.id#0 => e.id\in RequestId /\
              o.requests[e.id].kind=e.kind /\
              IF e.kind="V2" THEN o.requests[e.id].changes=e.changes /\ o.requests[e.id].transition=e.transition
              ELSE o.requests[e.id].target=e.target
       ELSE o.after=o.before
\* Pending mutation on quota drop deliberately remains unresolved.
RevisedProposalConfigurationDecisions == \A o\in audit.proposals:RevisedProposalContract(o)
RevisedOutcomeSoundness == \A o\in audit.proposals:o.decision=RevisedExpectedDecision(ProposalOutcome(o))
TransferCancellationContract(o) ==
 (o.fatal="" /\ o.role="Leader" /\ o.node\in VoterIDs(o.after) /\ o.after.voters#{}) =>
 o.afterTransfer=IF o.oldTransfer\in VoterIDs(o.after) THEN o.oldTransfer ELSE 0
TransferCancellationOnConfigurationChange == \A o\in audit.switches:TransferCancellationContract(o)
\* DRAFT ONLY. No liveness validation. Service premise must be instantiated with
\* fair communication, persistence, Ready/Advance AND ordered callbacks; no new
\* client write and no requirement to re-cross a previously acknowledged index.
AutoLeaveCompletionUnder(service) ==
 service => \A n\in Server: (raft[n].config.autoLeave /\ raft[n].config.outgoing#{}) ~>
                         (raft[n].config.outgoing={} /\ ~raft[n].config.autoLeave)

====================================================
