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
 LET eligible==a.config.autoLeave /\ a.role="Leader" /\ a.cursor>0 /\ a.cursor>=a.pendingBefore
     blocked==a.quotaBefore>0 /\ a.quotaBefore+AutoLeaveWeight>MaxUncommitted
 IN /\ a.fatal=""
    /\ IF ~eligible THEN a.after=a.before /\ a.pendingAfter=a.pendingBefore
       ELSE IF blocked THEN a.after=a.before /\ a.pendingAfter=Len(a.before)
       ELSE /\ a.after=Append(a.before,V2Entry(a.term,Len(a.before)+1,0,<<>>,"Auto",AutoLeaveWeight,AutoLeaveEncoded))
    /\ a.quotaAfter=Max(0,a.quotaBefore+(IF eligible /\ ~blocked THEN AutoLeaveWeight ELSE 0)-a.committedWeight)
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

====================================================
