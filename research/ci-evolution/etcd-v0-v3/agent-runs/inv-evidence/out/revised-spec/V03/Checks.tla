---------------- MODULE Checks ----------------
EXTENDS Maintenance, Json

H0 == INSTANCE HistoricalV00
H1 == INSTANCE HistoricalV01
H2 == INSTANCE HistoricalV02
Ack0(a) == LET H==INSTANCE HistoricalV00 WITH history <- [H0!EmptyHistory EXCEPT !.acks={a}] IN H!AckPreservation
AckFrozen(a) == LET H==INSTANCE base WITH history <- [EmptyHistory EXCEPT !.acks={a}] IN H!AckPreservation
ReadyOld(o) == LET H==INSTANCE HistoricalV01 WITH history <- [H1!EmptyHistory EXCEPT !.readyChecks={o}] IN H!ReadyOwnership
ReadyFrozen(o) == LET H==INSTANCE base WITH history <- [EmptyHistory EXCEPT !.readyChecks={o}] IN H!ReadyOwnership
AutoOld(a) == LET o==[eligible |-> a.config.autoLeave /\ a.cursor>=a.pendingBefore /\ a.role="Leader",
 beforeLast |-> Len(a.before),afterHist |-> a.after,pending |-> a.pendingAfter,decision |-> a.decision]
 H==INSTANCE base WITH history <- [EmptyHistory EXCEPT !.autoLeaveChecks={o}] IN H!AutoLeaveAdvance
\* Exact pre-existing lost-read formula; application queue holds captured reads.
OldLost(a) == IF a.raw /\ a.batchReads# <<>> THEN
 {rd\in SeqSet(a.readsBefore):rd\notin SeqSet(a.batchReads) /\ rd\notin SeqSet(<<>>)} ELSE {}
AccountingWith(lost) == LET H==INSTANCE base WITH history <- [EmptyHistory EXCEPT !.lostReads=lost] IN H!ReadyAccounting
CampaignTruth(r,a) == LET o==CampaignObservation(r,a) IN
 [observation |-> o,old |-> CampaignContract(o),candidate |-> RevisedCampaignContract(o),
 negative |-> RevisedCampaignContract([o EXCEPT !.afterTerm=@+7]),
 population |-> "Original CampaignObservation on mapped actual Step pre/post; singleton record, not quality={}."]
VoteTruth(r,m,a) == LET o==VoteObservation(r,m,a) IN
 [observation |-> o,old |-> H1!VoteContract(o),candidate |-> VoteContract(o),
 negative |-> VoteContract([o EXCEPT !.afterTerm=@+7]),
 population |-> "Original VoteObservation on mapped actual Step pre/post/input."]
AdvanceTruth(r,b,a) == LET o==AdvanceObservation(r,b,a)
 bad==[o EXCEPT !.applied=o.cursor+1]
 badExtra==[o EXCEPT !.after=Append(@,Entry(o.term,Len(@)+1,"Normal",0,0,0,8))]
 badCanonical==IF o.after=o.before THEN o ELSE [o EXCEPT !.after[Len(o.after)].transition="JointExplicit"]
 IN [observation |-> o,old |-> Ack0(o),frozen |-> AckFrozen(o),candidate |-> AdvanceEnvelope(o) /\ RevisedAutoLeaveContract(o) /\ (o.after=o.before \/ ~\E k\in (o.oldApplied+1)..Len(o.before):IsLeave(o.before[k]) /\ o.before[k].id=0),
 oldAuto |-> AutoOld(o),candidateAuto |-> RevisedAutoLeaveContract(o),
 negativeCursor |-> IF o.cursor=0 THEN "not-applicable" ELSE AdvanceEnvelope(bad) /\ RevisedAutoLeaveContract(bad),
 negativeExtra |-> AdvanceEnvelope(badExtra) /\ RevisedAutoLeaveContract(badExtra),
 negativePrefix |-> IF o.before= <<>> THEN "not-applicable" ELSE RevisedAutoLeaveContract([o EXCEPT !.after[1].term=@+1]),
 oldLostReadTruth |-> AccountingWith(OldLost(o)),
 newLostReadTruth |-> AccountingWith(IF o.readsBefore=o.readsAfter THEN {} ELSE {o}),
 negativeCanonical |-> IF o.after=o.before THEN "not-applicable" ELSE RevisedAutoLeaveContract(badCanonical),
 population |-> "Original ProtocolReady/ProtocolAdvance populated history. Added raw-fact observer uses actual pre-Advance state and captured Ready; no protocol predicate used for eligibility."]
ReadyTruth(r,b,a) == LET o==ReadyObservation(r,b,a) IN
 [observation |-> o,old |-> ReadyOld(o),frozen |-> ReadyFrozen(o),candidate |-> RevisedReadyContract(o),
 negative |-> RevisedReadyContract([o EXCEPT !.quotaAfter=@+1]),
 population |-> "Actual original ProtocolReady transition and delivered batch; original history.readyChecks is nonempty."]
ProposalTruth(r,es,a,qs) == LET o==RevisedProposalObservation(r,es,a,qs) IN
 [observation |-> o,old |-> ProposalContract(o),candidate |-> RevisedProposalContract(o),
 negative |-> RevisedProposalContract([o EXCEPT !.decision="Forwarded"]),
 population |-> "Original ProposalObservation over actual Step pre/post, extended with pre term/config and actual post pending; not empty quality.proposals."]
CommitTruth(a) ==
 LET H==INSTANCE base WITH history <- [EmptyHistory EXCEPT !.commitUses=a.commitUses]
     M==INSTANCE Maintenance WITH history <- [EmptyHistory EXCEPT !.commitUses=a.commitUses]
 IN IF a.commitUses={} THEN [old |-> "no-commit-event",candidate |-> "no-commit-event",population |-> "No vacuous pass"] ELSE
 [observation |-> a.commitUses,old |-> H!ConfigurationTransitionSafety,candidate |-> M!RevisedConfigurationTransitionSafety,
 quorum |-> H!QuorumAccounting,population |-> "Actual original MaybeCommit commitUses event from Step(MsgAppResp); nonempty history."]
ActionTruth(action,r,b,a,qs,m,es) ==
 CASE action="hup" -> CampaignTruth(r,a)
 [] action="vote" -> VoteTruth(r,m,a)
 [] action\in {"advance_raw","advance_node"} -> AdvanceTruth(r,b,a)
 [] action\in {"ready_raw","ready_node"} -> ReadyTruth(r,b,a)
 [] action="proposal" -> ProposalTruth(r,es,a,qs)
 [] action="receive" -> CommitTruth(a)
 [] action="apply" -> [observation |-> SwitchObservation(r,a),old |-> "not-observed-by-old-transfer-request-contract",candidate |-> TransferCancellationContract(SwitchObservation(r,a)),population |-> "Mapped original ApplyConfCore pre/post; separate configuration callback observer."]
 [] OTHER -> [old |-> "not-observed",candidate |-> "not-observed",population |-> "No contract evaluated for this action; raw transition retained."]

==============================
