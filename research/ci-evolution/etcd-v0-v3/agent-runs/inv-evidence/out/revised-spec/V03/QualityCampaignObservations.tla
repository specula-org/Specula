------------------- MODULE QualityCampaignObservations -------------------
EXTENDS QualityDecisions
\* Supplemental local observer diagnostics. No production or reference mutation.
\* These feed actual before/after outgoing bags to CampaignObservation.
RepeatBefore == StepHup([R(VoterCfg,"Follower") EXCEPT !.preVote=TRUE],ElectionTick)
RepeatAfter == StepHup(RepeatBefore,ElectionTick)
Repeated == CampaignObservation(RepeatBefore,RepeatAfter)
Ineligible == [R(LearnerCfg,"Follower") EXCEPT !.preVote=TRUE,!.elapsed=ElectionTick-1]
Illicit == [Message("MsgPreVote",1,2,Ineligible.term+1) EXCEPT !.index=Last(Ineligible),!.logTerm=1]
Observed ==
  CASE QualityCase="observer-positive" -> {
       Repeated,
       CampaignObservation(Ineligible,StepHup(Ineligible,ElectionTick)),
       [CampaignObservation(Ineligible,TickCore(Ineligible,ElectionTick)) EXCEPT !.trigger="Tick"]}
    [] QualityCase="observer-ineligible-hup-output" ->
         {CampaignObservation(Ineligible,Send(Ineligible,Illicit))}
    [] QualityCase="observer-ineligible-tick-output" ->
         {[CampaignObservation(Ineligible,Send(TickCore(Ineligible,ElectionTick),Illicit)) EXCEPT !.trigger="Tick"]}
    [] QualityCase="observer-repeat-missing-delta" ->
         {CampaignObservation(RepeatBefore,RepeatBefore)}
    [] QualityCase="observer-repeat-extra-delta" ->
         {CampaignObservation(RepeatBefore,Send(RepeatAfter,CHOOSE m\in DOMAIN RepeatAfter.out:TRUE))}
    [] QualityCase="observer-wrong-recipient" ->
         LET m==CHOOSE x\in DOMAIN RepeatAfter.out:TRUE
             wrong==[m EXCEPT !.to=4]
         IN {CampaignObservation(RepeatBefore,[RepeatAfter EXCEPT !.out=AddBag(RemoveBag(@,m),wrong)])}
    [] OTHER ->
         LET m==CHOOSE x\in DOMAIN RepeatAfter.out:TRUE
             wrong==[m EXCEPT !.logTerm=99]
         IN {CampaignObservation(RepeatBefore,[RepeatAfter EXCEPT !.out=AddBag(RemoveBag(@,m),wrong)])}
ObserverInit == ProtocolInit /\ quality\in {[EmptyQuality EXCEPT !.campaigns={o}]:o\in Observed}
=============================================================================
