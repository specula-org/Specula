------------------------------ MODULE PrefixBranch ------------------------------
EXTENDS Trace, Update, TLC
CONSTANTS PBPoints, PBMaxSteps
VARIABLES pbAt, pbStep, pbBranched, pbSlot, pbAction
pbVars == <<vars, l, faultCount, pbAt, pbStep, pbBranched, pbSlot, pbAction>>
PBInit == MCInit /\ l = 2 /\ pbAt \in PBPoints /\ pbStep = 0 /\ pbBranched = FALSE /\ pbSlot = 1 /\ pbAction = 0
PBReplay == /\ ~pbBranched /\ pbStep < pbAt /\ l <= Len(TraceLog) /\ MatchEvent(logline)
    /\ l' = l + 1 /\ pbStep' = pbStep + 1 /\ UNCHANGED <<faultCount, pbAt, pbBranched, pbSlot, pbAction>>
PBSettle1 ==
    FullUpdateNext
PBPart(i) == CASE i = 1 -> PBSettle1
PBParts == 1
PBOffsets == {d \in 0..(PBParts - 1) : ENABLED PBPart(((pbSlot - 1 + d) % PBParts) + 1)}
PBFirst == CHOOSE d \in PBOffsets : \A e \in PBOffsets : d <= e
PBSettle == /\ l > Len(TraceLog) /\ (pbBranched \/ pbStep < pbAt) /\ pbStep < PBMaxSteps /\ PBOffsets # {}
    /\ LET i == ((pbSlot - 1 + PBFirst) % PBParts) + 1 IN PBPart(i) /\ pbSlot' = (i % PBParts) + 1
    /\ pbStep' = pbStep + 1 /\ UNCHANGED <<l, pbAt, pbBranched, pbAction>>
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
    /\ pbBranched' = TRUE /\ pbStep' = pbStep + 1 /\ UNCHANGED <<l, pbAt, pbSlot>>
PBSpec == PBInit /\ [][PBReplay \/ PBSettle \/ PBBranch]_pbVars
PBReplayed == l <= Len(TraceLog)
PBAllPoints == 0..(PBMaxSteps - 1)
PBConstraint == ~pbBranched \/ (StateConstraint)
PB_ElectionSafety == ~pbBranched \/ ElectionSafety
PB_LogMatching == ~pbBranched \/ LogMatching
PB_LeaderCompleteness == ~pbBranched \/ LeaderCompleteness
PB_CommittedHistory == ~pbBranched \/ CommittedHistory
PB_AppliedAgreement == ~pbBranched \/ AppliedAgreement
PB_MCTypeOK == ~pbBranched \/ MCTypeOK
PB_LogStructure == ~pbBranched \/ LogStructure
PB_VoteDecisionEligibility == ~pbBranched \/ VoteDecisionEligibility
PB_CampaignDecisionEligibility == ~pbBranched \/ CampaignDecisionEligibility
PB_TransferDecisionEligibility == ~pbBranched \/ TransferDecisionEligibility
PB_RequestCorrelatedConfigurationEffects == ~pbBranched \/ RequestCorrelatedConfigurationEffects
PB_ProposalConfigurationDecisions == ~pbBranched \/ ProposalConfigurationDecisions
PB_VoteRecovery == ~pbBranched \/ VoteRecovery
PB_RecoveryBacking == ~pbBranched \/ RecoveryBacking
PB_PromiseBacking == ~pbBranched \/ PromiseBacking
PB_AckPreservation == ~pbBranched \/ AckPreservation
PB_NoUnexpectedFatal == ~pbBranched \/ NoUnexpectedFatal
PB_LearnerEligibility == ~pbBranched \/ LearnerEligibility
PB_QuorumAccounting == ~pbBranched \/ QuorumAccounting
PB_ConfigurationOrigin == ~pbBranched \/ ConfigurationOrigin
PB_ConfigurationTransitionSafety == ~pbBranched \/ ConfigurationTransitionSafety
PB_ReadyAccounting == ~pbBranched \/ ReadyAccounting
PB_OutcomeSoundness == ~pbBranched \/ OutcomeSoundness
PB_ReplicationEvidence == ~pbBranched \/ ReplicationEvidence
PB_SnapshotBacking == ~pbBranched \/ SnapshotBacking
PB_QuotaIntegrity == ~pbBranched \/ QuotaIntegrity
PB_ReadBasis == ~pbBranched \/ ReadBasis
PB_ReadApplication == ~pbBranched \/ ReadApplication
PB_ReadCorrelation == ~pbBranched \/ ReadCorrelation
PB_TypeOK == ~pbBranched \/ TypeOK
PB_JointConfigurationShape == ~pbBranched \/ JointConfigurationShape
PB_JointSnapshotRecovery == ~pbBranched \/ JointSnapshotRecovery
PB_ReadyOwnership == ~pbBranched \/ ReadyOwnership
PB_JointSnapshotMemberAcceptance == ~pbBranched \/ JointSnapshotMemberAcceptance
PB_UpdateJointConfigurationShape == ~pbBranched \/ UpdateJointConfigurationShape
PB_UpdateQuorumAccounting == ~pbBranched \/ UpdateQuorumAccounting
PB_UpdateLearnerVoteContract == ~pbBranched \/ UpdateLearnerVoteContract
PB_UpdateLearnerCampaignEligibility == ~pbBranched \/ UpdateLearnerCampaignEligibility
PB_UpdateReadyOwnership == ~pbBranched \/ UpdateReadyOwnership
PB_UpdateAdvanceOutputPreservation == ~pbBranched \/ UpdateAdvanceOutputPreservation
PB_UpdateAutoLeaveAdvance == ~pbBranched \/ UpdateAutoLeaveAdvance
PB_UpdateJointSnapshotRecovery == ~pbBranched \/ UpdateJointSnapshotRecovery
PB_UpdateJointSnapshotMemberAcceptance == ~pbBranched \/ UpdateJointSnapshotMemberAcceptance
=============================================================================
