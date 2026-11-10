-------------------------- MODULE QualityDecisions --------------------------
EXTENDS Quality
CONSTANT QualityCase
QualityBootPeers == <<1,2,3>>
QualityInitialTimeoutAssignments == {[n\in Server |-> ElectionTick]}
Cfg(v,l) == [voters |-> v,learners |-> l]
VoterCfg == Cfg({1,2,3},{})
LearnerCfg == Cfg({2,3},{1})
RemovedCfg == Cfg({2,3},{})
R(cfg,role) == [InitialRaft(1,ElectionTick) EXCEPT
    !.config=cfg, !.role=role, !.applied=Len(BootLog),
    !.prs=[n\in cfg.voters\cup cfg.learners |-> Progress(IF n=1 THEN Len(BootLog) ELSE 0,Len(BootLog)+1,TRUE)]]
Q(id,kind,target,status) == [EmptyRequest EXCEPT !.node=1, !.status=status,
    !.kind=kind, !.target=target, !.handoff=status#"Invoked"]
QS(id,kind,target,status) == [j\in RequestId |-> IF j=id THEN Q(id,kind,target,status) ELSE EmptyRequest]

\* Finite decision-context tests, not reachable whole-protocol executions.
\* Candidate 4 lies outside all receiver voter configurations on purpose:
\* V00 StepVote does not require candidate membership.
VoteCase(cfg,v,lead,ty,term,idx,lt,forced,check,elapsed) ==
    LET r==[R(cfg,"Follower") EXCEPT !.term=2,!.vote=v,!.lead=lead,
             !.checkQuorum=check,!.elapsed=elapsed]
        m==[Message(ty,4,1,term) EXCEPT !.index=idx,!.logTerm=lt,!.forced=forced]
    IN VoteObservation(r,m,Step(r,m,ElectionTick))
VoteCases == {VoteCase(cfg,v,lead,ty,t,i,lt,f,c,el):
    cfg\in {VoterCfg,LearnerCfg,RemovedCfg},v\in {0,2,4},lead\in {0,2},
    ty\in {"MsgVote","MsgPreVote"},t\in {1,2,3},i\in {2,3},lt\in {0,1,2},
    f\in BOOLEAN,c\in BOOLEAN,el\in {0,ElectionTick}}
CampaignCase(cfg,role,pre,pending) ==
    LET r==[R(cfg,role) EXCEPT !.preVote=pre,!.applied=Len(BootLog)-(IF pending THEN 1 ELSE 0)]
    IN CampaignObservation(r,StepHup(r,ElectionTick))
CampaignCases == {CampaignCase(cfg,role,pre,pending):
    cfg\in {VoterCfg,LearnerCfg,RemovedCfg,Cfg({1},{})},
    role\in {"Follower","Candidate","PreCandidate","Leader"},pre\in BOOLEAN,pending\in BOOLEAN}
TickCase(cfg,role,pre,pending,elapsed) ==
    LET r==[R(cfg,role) EXCEPT !.preVote=pre,
              !.applied=Len(BootLog)-(IF pending THEN 1 ELSE 0),!.elapsed=elapsed]
    IN [CampaignObservation(r,TickCore(r,ElectionTick)) EXCEPT !.trigger="Tick"]
TickCases == {TickCase(cfg,role,pre,pending,elapsed):
    cfg\in {VoterCfg,LearnerCfg,RemovedCfg,Cfg({1},{})},
    role\in {"Follower","Candidate","PreCandidate","Leader"},pre\in BOOLEAN,
    pending\in BOOLEAN,elapsed\in {0,ElectionTick-1}}
\* Pure observation controls: the target implementation is never mutated.
IllicitCampaignOutput(o) == [o EXCEPT !.voteRequests={
    [from |-> o.node,to |-> 2,type |-> "MsgPreVote",term |-> o.term+1,
     index |-> Len(o.hist),logTerm |-> 1,forced |-> FALSE,count |-> 1]}]

TransferCase(cfg,target,old,caught) ==
    LET r==[R(cfg,"Leader") EXCEPT !.transfer=old,!.elapsed=2,
        !.prs=[n\in cfg.voters\cup cfg.learners |-> Progress(IF caught THEN Len(BootLog) ELSE 0,Len(BootLog)+1,TRUE)]]
    IN TransferObservation(r,target,Step(r,Message("MsgTransferLeader",target,1,0),ElectionTick))
TransferCases == {TransferCase(cfg,target,old,caught):
    cfg\in {VoterCfg,Cfg({1,2},{3}),Cfg({1,2,3},{4})},target\in Server,old\in {0,2,3},caught\in BOOLEAN}
EffectCase(cfg,kind,target,id,status) ==
    LET e==Entry(2,Len(BootLog)+1,kind,id,target,1,1)
        r==[R(cfg,"Follower") EXCEPT !.unstable=BootLog\o <<e>>,!.commit=Len(BootLog)+1]
    IN EffectObservation(r,e,ApplyConfCore(r,e,ElectionTick),QS(id,kind,target,status))
EffectCases == {EffectCase(cfg,kind,target,id,status):
    cfg\in {VoterCfg,Cfg({1,2},{3})},kind\in ConfKinds,target\in Server\cup {0},
    id\in {1,2},status\in {"Returned","Canceled"}}
ProposalCase(role,removed,lead,transfer,pending,quota,weight,kind,target) ==
    LET r==[R(IF removed THEN RemovedCfg ELSE VoterCfg,role) EXCEPT
             !.lead=lead,!.transfer=transfer,!.pendingConf=IF pending THEN Len(BootLog)+1 ELSE 0,!.quota=quota]
        es==<<Entry(0,0,kind,1,target,weight,1)>>
        m==[Message("MsgProp",1,1,0) EXCEPT !.entries=es,!.request=1]
    IN ProposalObservation(r,es,Step(r,m,ElectionTick),QS(1,kind,target,"Invoked"))
ProposalCases == {ProposalCase(role,removed,lead,transfer,pending,quota,weight,kind,target):
    role\in {"Follower","Candidate","PreCandidate","Leader"},removed\in BOOLEAN,lead\in {0,2},
    transfer\in {0,2},pending\in BOOLEAN,quota\in {0,1},weight\in {1,3},kind\in ConfKinds,target\in {3,4}}

\* Sensitivity mutations alter observations only, never production/model actions.
\* Every mutant is deliberately named by the independent error it injects.
Mutant == CASE QualityCase="hup-ineligible-side-effect" ->
    [EmptyQuality EXCEPT !.campaigns={IllicitCampaignOutput(CampaignCase(LearnerCfg,"Follower",TRUE,FALSE))}]
  [] QualityCase="repeated-prevote-missing-output" ->
    [EmptyQuality EXCEPT !.campaigns={
       [CampaignCase(VoterCfg,"PreCandidate",TRUE,FALSE) EXCEPT !.voteRequests={}]}]
  [] QualityCase="repeated-prevote-double-output" ->
    [EmptyQuality EXCEPT !.campaigns={
       [CampaignCase(VoterCfg,"PreCandidate",TRUE,FALSE) EXCEPT
         !.voteRequests={ [m EXCEPT !.count=2]:m\in @}]}]
  [] QualityCase="tick-ineligible-side-effect" ->
    [EmptyQuality EXCEPT !.campaigns={IllicitCampaignOutput(TickCase(LearnerCfg,"Follower",TRUE,FALSE,ElectionTick-1))}]
  [] QualityCase="tick-pending-side-effect" ->
    [EmptyQuality EXCEPT !.campaigns={IllicitCampaignOutput(TickCase(VoterCfg,"PreCandidate",TRUE,TRUE,ElectionTick-1))}]
  [] QualityCase="tick-premature-side-effect" ->
    [EmptyQuality EXCEPT !.campaigns={IllicitCampaignOutput(TickCase(VoterCfg,"Follower",TRUE,FALSE,0))}]
  [] QualityCase="hup-forced-transfer-flag" ->
    [EmptyQuality EXCEPT !.campaigns={
       [CampaignCase(VoterCfg,"Follower",FALSE,FALSE) EXCEPT
         !.voteRequests={ [m EXCEPT !.forced=TRUE]:m\in @}]}]
  [] QualityCase="vote-unjustified-rejection" ->
    [EmptyQuality EXCEPT !.votes={
      [VoteCase(VoterCfg,0,0,"MsgVote",2,3,1,FALSE,FALSE,0) EXCEPT
        !.responses={[type |-> "MsgVoteResp",term |-> 2,to |-> 4,reject |-> TRUE,count |-> 1]},!.afterVote=0]}]
  [] QualityCase="vote-learner-grant" ->
    [EmptyQuality EXCEPT !.votes={
      [VoteCase(LearnerCfg,0,0,"MsgVote",2,3,1,FALSE,FALSE,0) EXCEPT
        !.responses={[type |-> "MsgVoteResp",term |-> 2,to |-> 4,reject |-> FALSE,count |-> 1]},!.afterVote=4]}]
  [] QualityCase="campaign-unjustified-ignore" ->
    [EmptyQuality EXCEPT !.campaigns={
      [CampaignCase(VoterCfg,"Follower",FALSE,FALSE) EXCEPT !.afterRole="Follower",!.afterTerm=1]}]
  [] QualityCase="campaign-pending-admitted" ->
    [EmptyQuality EXCEPT !.campaigns={
      [CampaignCase(VoterCfg,"Follower",FALSE,TRUE) EXCEPT !.afterRole="Candidate",!.afterTerm=2]}]
  [] QualityCase="transfer-unjustified-ignore" ->
    [EmptyQuality EXCEPT !.transfers={[TransferCase(VoterCfg,2,0,FALSE) EXCEPT !.after=0]}]
  [] QualityCase="transfer-learner-admitted" ->
    [EmptyQuality EXCEPT !.transfers={[TransferCase(Cfg({1,2},{3}),3,0,FALSE) EXCEPT !.after=3]}]
  [] QualityCase="effect-wrong-request" ->
    [EmptyQuality EXCEPT !.effects={[EffectCase(VoterCfg,"AddLearner",4,1,"Returned") EXCEPT !.request.target=3]}]
  [] QualityCase="effect-cancel-applied" ->
    [EmptyQuality EXCEPT !.effects={[EffectCase(VoterCfg,"Remove",3,2,"Returned") EXCEPT !.after.voters={1,2}]}]
  [] QualityCase="effect-demotion-applied" ->
    [EmptyQuality EXCEPT !.effects={[EffectCase(VoterCfg,"AddLearner",3,1,"Returned") EXCEPT !.after=Cfg({1,2},{3})]}]
  [] QualityCase="proposal-unjustified-rejection" ->
    [EmptyQuality EXCEPT !.proposals={
      [ProposalCase("Leader",FALSE,1,0,FALSE,0,1,"AddLearner",4) EXCEPT !.decision="DropQuota",!.after=BootLog]}]
  [] QualityCase="proposal-rewrite-wrong-identity" ->
    [EmptyQuality EXCEPT !.proposals={
      [ProposalCase("Leader",FALSE,1,0,TRUE,0,1,"AddLearner",4) EXCEPT !.after[4].id=1]}]
  [] OTHER -> EmptyQuality
FixtureInit == ProtocolInit /\
    CASE QualityCase="votes" -> quality\in {[EmptyQuality EXCEPT !.votes={o}]:o\in VoteCases}
      [] QualityCase="ticks" -> quality\in {[EmptyQuality EXCEPT !.campaigns={o}]:o\in TickCases}
      [] QualityCase="campaigns" -> quality\in {[EmptyQuality EXCEPT !.campaigns={o}]:o\in CampaignCases}
      [] QualityCase="transfers" -> quality\in {[EmptyQuality EXCEPT !.transfers={o}]:o\in TransferCases}
      [] QualityCase="effects" -> quality\in {[EmptyQuality EXCEPT !.effects={o}]:o\in EffectCases}
      [] QualityCase="proposals" -> quality\in {[EmptyQuality EXCEPT !.proposals={o}]:o\in ProposalCases}
      [] OTHER -> quality=Mutant
FixtureNext == UNCHANGED qualityVars
=============================================================================
