------------------------------ MODULE PrefixBranch ------------------------------
EXTENDS Trace, Update, Maintenance, TLC
CONSTANTS PBPoints, PBMaxSteps, PBAfter
VARIABLES pbAt, pbStep, pbBroken, pbBranched, pbSlot, pbAction
pbVars == <<vars, l, faultCount, pbAt, pbStep, pbBroken, pbBranched, pbSlot, pbAction, audit>>
PBInit == MCInit /\ l = 2 /\ pbAt \in PBPoints /\ pbStep = 0 /\ pbBranched = FALSE /\ pbSlot = 1 /\ pbAction = 0 /\ audit = EmptyAudit /\ pbBroken = {}
PBReplay == /\ ~pbBranched /\ pbStep < pbAt /\ l <= Len(TraceLog) /\ MatchEvent(logline) /\ audit' = AuditNext
    /\ l' = l + 1 /\ pbStep' = pbStep + 1 /\ UNCHANGED <<faultCount, pbAt, pbBroken, pbBranched, pbSlot, pbAction>>
PBSettle1 ==
    \E n\in Server,id\in RequestId,t\in Timeouts:Propose(n,id,t)
PBSettle2 ==
    \E n\in Server,id\in RequestId,t\in Timeouts:ReadIndex(n,id,t)
PBSettle3 ==
    \E id\in RequestId:ReturnAPI(id)
PBSettle4 ==
    \E m\in DOMAIN wire,t\in Timeouts:Receive(m,t)
PBSettle5 ==
    \E n\in Server:Ready(n) \/ Publish(n) \/ QueueApplication(n) \/ Advance(n)
             \/ StorageApplySnapshot(n) \/ StorageAppend(n) \/ StorageSetHardState(n)
             \/ ApplySnapshot(n) \/ FinishApplication(n) \/ SaveApplication(n)
             \/ PersistLocalSnapshot(n)
PBSettle6 ==
    \E n\in Server,part\in {"All","Entries","HS","Snapshot"}:StartPersist(n,part) \/ CompletePersist(n,part)
PBSettle7 ==
    \E n\in Server,t\in Timeouts:ApplyEntry(n,t) \/ Restart(n,t)
PBSettle8 ==
    \E n\in Server,id\in RequestId:CompleteWrite(n,id) \/
             (\E k\in DOMAIN application[n].reads:CompleteRead(n,id,k))
PBPart(i) == CASE i = 1 -> PBSettle1
    [] i = 2 -> PBSettle2
    [] i = 3 -> PBSettle3
    [] i = 4 -> PBSettle4
    [] i = 5 -> PBSettle5
    [] i = 6 -> PBSettle6
    [] i = 7 -> PBSettle7
    [] i = 8 -> PBSettle8
PBParts == 8
PBOffsets == {d \in 0..(PBParts - 1) : ENABLED PBPart(((pbSlot - 1 + d) % PBParts) + 1)}
PBFirst == CHOOSE d \in PBOffsets : \A e \in PBOffsets : d <= e
PBSettle == /\ IF pbBranched THEN pbStep < pbAt + 1 + PBAfter ELSE l > Len(TraceLog) /\ pbStep < pbAt
    /\ PBOffsets # {}
    /\ LET i == ((pbSlot - 1 + PBFirst) % PBParts) + 1 IN PBPart(i) /\ pbSlot' = (i % PBParts) + 1
    /\ pbStep' = pbStep + 1 /\ UNCHANGED <<l, faultCount, pbAt, pbBroken, pbBranched, pbAction>> /\ audit' = AuditNext
PBProbe1 ==
    \E n\in Server,t\in Timeouts:MCCampaign(n,t)
PBProbe2 ==
    \E n\in Server,t\in Timeouts:MCTick(n,t)
PBProbe3 ==
    \E m\in DOMAIN wire,t\in Timeouts:
         /\ m.type\in {"MsgVote","MsgPreVote","MsgVoteResp","MsgPreVoteResp"}
         /\ Framed(Original!Receive(m,t))
PBProbe4 ==
    \E n\in Server:Framed(Original!Ready(n))
PBProbe5 ==
    \E n\in Server:Framed(Original!Advance(n))
PBProbe6 ==
    \E n\in Server,t\in Timeouts:Framed(Original!Restart(n,t))
PBProbe7 ==
    \E m\in DOMAIN wire,t\in Timeouts:
         /\ m.type="MsgSnap"
         /\ Framed(Original!Receive(m,t))
PBProbe8 ==
    \E n\in Server,id\in RequestId,kind\in WorkloadKinds\{"Read","V2"},
          target\in Server\cup{0},w\in PayloadWeights,z\in EncodedWeights,
          parent\in RequestId\cup{0}:
          \E ctx\in {id,0}:MCInvoke(n,id,kind,target,w,z,parent,ctx)
PBProbe9 ==
    \E n\in Server,id\in RequestId,changes\in V2Batches,
          transition\in {"Auto","JointImplicit","JointExplicit"},
          w\in PayloadWeights,z\in EncodedWeights,parent\in RequestId\cup{0}:
          MCInvokeV2(n,id,changes,transition,w,z,parent)
PBProbe10 ==
    \E n\in Server,id\in RequestId,t\in Timeouts:
          Framed(Original!Propose(n,id,t))
PBProbe11 ==
    \E n\in Server,t\in Timeouts:Framed(Original!ApplyEntry(n,t))
PBProbe12 ==
    \E n,p\in Server,t\in Timeouts:MCTransfer(n,p,t)
PBProbe13 ==
    \E m\in DOMAIN wire,t\in Timeouts:
         /\ m.type\in {"MsgApp","MsgAppResp","MsgHeartbeat","MsgHeartbeatResp", "MsgTimeoutNow"}
         /\ Framed(Original!Receive(m,t))
PBBranch == /\ ~pbBranched /\ pbStep = pbAt
    /\ \/ PBProbe1 /\ pbAction' = 1
       \/ PBProbe2 /\ pbAction' = 2
       \/ PBProbe3 /\ pbAction' = 3
       \/ PBProbe4 /\ pbAction' = 4
       \/ PBProbe5 /\ pbAction' = 5
       \/ PBProbe6 /\ pbAction' = 6
       \/ PBProbe7 /\ pbAction' = 7
       \/ PBProbe8 /\ pbAction' = 8
       \/ PBProbe9 /\ pbAction' = 9
       \/ PBProbe10 /\ pbAction' = 10
       \/ PBProbe11 /\ pbAction' = 11
       \/ PBProbe12 /\ pbAction' = 12
       \/ PBProbe13 /\ pbAction' = 13
    /\ pbBroken' = (IF ElectionSafety THEN {} ELSE {"ElectionSafety"}) \cup (IF LogMatching THEN {} ELSE {"LogMatching"}) \cup (IF LeaderCompleteness THEN {} ELSE {"LeaderCompleteness"}) \cup (IF CommittedHistory THEN {} ELSE {"CommittedHistory"}) \cup (IF AppliedAgreement THEN {} ELSE {"AppliedAgreement"}) \cup (IF MCTypeOK THEN {} ELSE {"MCTypeOK"}) \cup (IF LogStructure THEN {} ELSE {"LogStructure"}) \cup (IF VoteDecisionEligibility THEN {} ELSE {"VoteDecisionEligibility"}) \cup (IF TransferDecisionEligibility THEN {} ELSE {"TransferDecisionEligibility"}) \cup (IF RequestCorrelatedConfigurationEffects THEN {} ELSE {"RequestCorrelatedConfigurationEffects"}) \cup (IF VoteRecovery THEN {} ELSE {"VoteRecovery"}) \cup (IF RecoveryBacking THEN {} ELSE {"RecoveryBacking"}) \cup (IF PromiseBacking THEN {} ELSE {"PromiseBacking"}) \cup (IF NoUnexpectedFatal THEN {} ELSE {"NoUnexpectedFatal"}) \cup (IF LearnerEligibility THEN {} ELSE {"LearnerEligibility"}) \cup (IF QuorumAccounting THEN {} ELSE {"QuorumAccounting"}) \cup (IF ConfigurationOrigin THEN {} ELSE {"ConfigurationOrigin"}) \cup (IF ReplicationEvidence THEN {} ELSE {"ReplicationEvidence"}) \cup (IF SnapshotBacking THEN {} ELSE {"SnapshotBacking"}) \cup (IF QuotaIntegrity THEN {} ELSE {"QuotaIntegrity"}) \cup (IF ReadBasis THEN {} ELSE {"ReadBasis"}) \cup (IF ReadApplication THEN {} ELSE {"ReadApplication"}) \cup (IF ReadCorrelation THEN {} ELSE {"ReadCorrelation"}) \cup (IF TypeOK THEN {} ELSE {"TypeOK"}) \cup (IF RevisedConfigurationTransitionSafety THEN {} ELSE {"RevisedConfigurationTransitionSafety"}) \cup (IF RevisedAckPreservation THEN {} ELSE {"RevisedAckPreservation"}) \cup (IF RevisedReadyAccounting THEN {} ELSE {"RevisedReadyAccounting"}) \cup (IF RevisedOutcomeSoundness THEN {} ELSE {"RevisedOutcomeSoundness"}) \cup (IF RevisedCampaignDecisionEligibility THEN {} ELSE {"RevisedCampaignDecisionEligibility"}) \cup (IF RevisedProposalConfigurationDecisions THEN {} ELSE {"RevisedProposalConfigurationDecisions"}) \cup (IF JointConfigurationShape THEN {} ELSE {"JointConfigurationShape"}) \cup (IF JointSnapshotRecovery THEN {} ELSE {"JointSnapshotRecovery"}) \cup (IF RevisedAutoLeaveAdvance THEN {} ELSE {"RevisedAutoLeaveAdvance"}) \cup (IF RevisedReadyOwnership THEN {} ELSE {"RevisedReadyOwnership"}) \cup (IF AdvancePreservesPendingOutput THEN {} ELSE {"AdvancePreservesPendingOutput"}) \cup (IF TransferCancellationOnConfigurationChange THEN {} ELSE {"TransferCancellationOnConfigurationChange"}) \cup (IF JointSnapshotMemberAcceptance THEN {} ELSE {"JointSnapshotMemberAcceptance"}) \cup (IF UpdateJointConfigurationShape THEN {} ELSE {"UpdateJointConfigurationShape"}) \cup (IF UpdateQuorumAccounting THEN {} ELSE {"UpdateQuorumAccounting"}) \cup (IF UpdateLearnerVoteContract THEN {} ELSE {"UpdateLearnerVoteContract"}) \cup (IF UpdateLearnerCampaignEligibility THEN {} ELSE {"UpdateLearnerCampaignEligibility"}) \cup (IF UpdateReadyOwnership THEN {} ELSE {"UpdateReadyOwnership"}) \cup (IF UpdateAdvanceOutputPreservation THEN {} ELSE {"UpdateAdvanceOutputPreservation"}) \cup (IF UpdateAutoLeaveAdvance THEN {} ELSE {"UpdateAutoLeaveAdvance"}) \cup (IF UpdateJointSnapshotRecovery THEN {} ELSE {"UpdateJointSnapshotRecovery"}) \cup (IF UpdateJointSnapshotMemberAcceptance THEN {} ELSE {"UpdateJointSnapshotMemberAcceptance"}) /\ audit' = AuditNext
    /\ pbBranched' = TRUE /\ pbStep' = pbStep + 1 /\ UNCHANGED <<l, pbAt, pbSlot>> /\ (\A id \in RequestId : (requests[id].status = "Unused" /\ requests'[id].status = "Invoked" /\ requests'[id].kind = "V2") => ConfigWellFormed(ConfigCandidate(raft[requests'[id].node].config, [kind |-> "V2", id |-> id, changes |-> requests'[id].changes, transition |-> requests'[id].transition])))
PBSpec == PBInit /\ [][PBReplay \/ PBSettle \/ PBBranch]_pbVars
PBReplayed == l <= Len(TraceLog)
PBReplayOnly == l' = l + 1
PBAllPoints == 0..(PBMaxSteps - 1)
PBConstraint == ~pbBranched \/ (StateConstraint)
PB_ElectionSafety == ~pbBranched \/ "ElectionSafety" \in pbBroken \/ ElectionSafety
PB_LogMatching == ~pbBranched \/ "LogMatching" \in pbBroken \/ LogMatching
PB_LeaderCompleteness == ~pbBranched \/ "LeaderCompleteness" \in pbBroken \/ LeaderCompleteness
PB_CommittedHistory == ~pbBranched \/ "CommittedHistory" \in pbBroken \/ CommittedHistory
PB_AppliedAgreement == ~pbBranched \/ "AppliedAgreement" \in pbBroken \/ AppliedAgreement
PB_MCTypeOK == ~pbBranched \/ "MCTypeOK" \in pbBroken \/ MCTypeOK
PB_LogStructure == ~pbBranched \/ "LogStructure" \in pbBroken \/ LogStructure
PB_VoteDecisionEligibility == ~pbBranched \/ "VoteDecisionEligibility" \in pbBroken \/ VoteDecisionEligibility
PB_TransferDecisionEligibility == ~pbBranched \/ "TransferDecisionEligibility" \in pbBroken \/ TransferDecisionEligibility
PB_RequestCorrelatedConfigurationEffects == ~pbBranched \/ "RequestCorrelatedConfigurationEffects" \in pbBroken \/ RequestCorrelatedConfigurationEffects
PB_VoteRecovery == ~pbBranched \/ "VoteRecovery" \in pbBroken \/ VoteRecovery
PB_RecoveryBacking == ~pbBranched \/ "RecoveryBacking" \in pbBroken \/ RecoveryBacking
PB_PromiseBacking == ~pbBranched \/ "PromiseBacking" \in pbBroken \/ PromiseBacking
PB_NoUnexpectedFatal == ~pbBranched \/ "NoUnexpectedFatal" \in pbBroken \/ NoUnexpectedFatal
PB_LearnerEligibility == ~pbBranched \/ "LearnerEligibility" \in pbBroken \/ LearnerEligibility
PB_QuorumAccounting == ~pbBranched \/ "QuorumAccounting" \in pbBroken \/ QuorumAccounting
PB_ConfigurationOrigin == ~pbBranched \/ "ConfigurationOrigin" \in pbBroken \/ ConfigurationOrigin
PB_ReplicationEvidence == ~pbBranched \/ "ReplicationEvidence" \in pbBroken \/ ReplicationEvidence
PB_SnapshotBacking == ~pbBranched \/ "SnapshotBacking" \in pbBroken \/ SnapshotBacking
PB_QuotaIntegrity == ~pbBranched \/ "QuotaIntegrity" \in pbBroken \/ QuotaIntegrity
PB_ReadBasis == ~pbBranched \/ "ReadBasis" \in pbBroken \/ ReadBasis
PB_ReadApplication == ~pbBranched \/ "ReadApplication" \in pbBroken \/ ReadApplication
PB_ReadCorrelation == ~pbBranched \/ "ReadCorrelation" \in pbBroken \/ ReadCorrelation
PB_TypeOK == ~pbBranched \/ "TypeOK" \in pbBroken \/ TypeOK
PB_RevisedConfigurationTransitionSafety == ~pbBranched \/ "RevisedConfigurationTransitionSafety" \in pbBroken \/ RevisedConfigurationTransitionSafety
PB_RevisedAckPreservation == ~pbBranched \/ "RevisedAckPreservation" \in pbBroken \/ RevisedAckPreservation
PB_RevisedReadyAccounting == ~pbBranched \/ "RevisedReadyAccounting" \in pbBroken \/ RevisedReadyAccounting
PB_RevisedOutcomeSoundness == ~pbBranched \/ "RevisedOutcomeSoundness" \in pbBroken \/ RevisedOutcomeSoundness
PB_RevisedCampaignDecisionEligibility == ~pbBranched \/ "RevisedCampaignDecisionEligibility" \in pbBroken \/ RevisedCampaignDecisionEligibility
PB_RevisedProposalConfigurationDecisions == ~pbBranched \/ "RevisedProposalConfigurationDecisions" \in pbBroken \/ RevisedProposalConfigurationDecisions
PB_JointConfigurationShape == ~pbBranched \/ "JointConfigurationShape" \in pbBroken \/ JointConfigurationShape
PB_JointSnapshotRecovery == ~pbBranched \/ "JointSnapshotRecovery" \in pbBroken \/ JointSnapshotRecovery
PB_RevisedAutoLeaveAdvance == ~pbBranched \/ "RevisedAutoLeaveAdvance" \in pbBroken \/ RevisedAutoLeaveAdvance
PB_RevisedReadyOwnership == ~pbBranched \/ "RevisedReadyOwnership" \in pbBroken \/ RevisedReadyOwnership
PB_AdvancePreservesPendingOutput == ~pbBranched \/ "AdvancePreservesPendingOutput" \in pbBroken \/ AdvancePreservesPendingOutput
PB_TransferCancellationOnConfigurationChange == ~pbBranched \/ "TransferCancellationOnConfigurationChange" \in pbBroken \/ TransferCancellationOnConfigurationChange
PB_JointSnapshotMemberAcceptance == ~pbBranched \/ "JointSnapshotMemberAcceptance" \in pbBroken \/ JointSnapshotMemberAcceptance
PB_UpdateJointConfigurationShape == ~pbBranched \/ "UpdateJointConfigurationShape" \in pbBroken \/ UpdateJointConfigurationShape
PB_UpdateQuorumAccounting == ~pbBranched \/ "UpdateQuorumAccounting" \in pbBroken \/ UpdateQuorumAccounting
PB_UpdateLearnerVoteContract == ~pbBranched \/ "UpdateLearnerVoteContract" \in pbBroken \/ UpdateLearnerVoteContract
PB_UpdateLearnerCampaignEligibility == ~pbBranched \/ "UpdateLearnerCampaignEligibility" \in pbBroken \/ UpdateLearnerCampaignEligibility
PB_UpdateReadyOwnership == ~pbBranched \/ "UpdateReadyOwnership" \in pbBroken \/ UpdateReadyOwnership
PB_UpdateAdvanceOutputPreservation == ~pbBranched \/ "UpdateAdvanceOutputPreservation" \in pbBroken \/ UpdateAdvanceOutputPreservation
PB_UpdateAutoLeaveAdvance == ~pbBranched \/ "UpdateAutoLeaveAdvance" \in pbBroken \/ UpdateAutoLeaveAdvance
PB_UpdateJointSnapshotRecovery == ~pbBranched \/ "UpdateJointSnapshotRecovery" \in pbBroken \/ UpdateJointSnapshotRecovery
PB_UpdateJointSnapshotMemberAcceptance == ~pbBranched \/ "UpdateJointSnapshotMemberAcceptance" \in pbBroken \/ UpdateJointSnapshotMemberAcceptance
=============================================================================
