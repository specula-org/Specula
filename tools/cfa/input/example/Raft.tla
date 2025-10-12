---- MODULE Raft ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS 
    Nodes,           \* Set of node IDs
    MaxTerm,         \* Maximum term number
    MaxLogIndex,     \* Maximum log index
    None,            \* Constant for no leader (0)
    ElectionTimeout, \* Election timeout ticks
    HeartbeatTimeout \* Heartbeat timeout ticks

VARIABLES 
    id,                          \* Node identifier
    Term,                        \* Current term number
    Vote,                        \* Node voted for in current term
    state,                       \* Current role (follower/candidate/leader/precandidate)
    lead,                        \* Current leader ID
    raftLog,                     \* Log entries and commit/applied indices
    msgs,                        \* Outgoing messages queue
    msgsAfterAppend,            \* Messages to send after persistence
    trk,                        \* Tracks replication progress for all nodes
    electionElapsed,            \* Ticks since last election timeout reset
    heartbeatElapsed,           \* Ticks since last heartbeat
    randomizedElectionTimeout,  \* Current election timeout value
    pendingConfIndex,           \* Index of pending configuration change
    uncommittedSize,            \* Size of uncommitted entries
    leadTransferee,             \* Target of leadership transfer
    readStates,                 \* Read states
    pendingReadIndexMessages,   \* Pending read index messages
    isLearner,                  \* Whether node is a learner
    preVote,                    \* Whether pre-vote is enabled
    checkQuorum,                \* Whether check quorum is enabled
    disableProposalForwarding,  \* Whether proposal forwarding is disabled
    stepDownOnRemoval,          \* Whether to step down on removal
    readOnly                    \* Read-only state

vars == <<id, Term, Vote, state, lead, raftLog, msgs, msgsAfterAppend, trk, 
          electionElapsed, heartbeatElapsed, randomizedElectionTimeout,
          pendingConfIndex, uncommittedSize, leadTransferee, readStates,
          pendingReadIndexMessages, isLearner, preVote, checkQuorum,
          disableProposalForwarding, stepDownOnRemoval, readOnly>>

\* State type definitions
StateFollower == "StateFollower"
StateCandidate == "StateCandidate"
StateLeader == "StateLeader"
StatePreCandidate == "StatePreCandidate"

\* Message type definitions
MsgHup == "MsgHup"
MsgBeat == "MsgBeat"
MsgProp == "MsgProp"
MsgApp == "MsgApp"
MsgAppResp == "MsgAppResp"
MsgVote == "MsgVote"
MsgVoteResp == "MsgVoteResp"
MsgPreVote == "MsgPreVote"
MsgPreVoteResp == "MsgPreVoteResp"
MsgSnap == "MsgSnap"
MsgHeartbeat == "MsgHeartbeat"
MsgHeartbeatResp == "MsgHeartbeatResp"
MsgCheckQuorum == "MsgCheckQuorum"
MsgTransferLeader == "MsgTransferLeader"
MsgTimeoutNow == "MsgTimeoutNow"
MsgReadIndex == "MsgReadIndex"
MsgReadIndexResp == "MsgReadIndexResp"
MsgSnapStatus == "MsgSnapStatus"

\* Campaign type definitions
campaignPreElection == "CampaignPreElection"
campaignElection == "CampaignElection"
campaignTransfer == "CampaignTransfer"

Init == 
    /\ id \in Nodes
    /\ Term = 0
    /\ Vote = None
    /\ state = StateFollower
    /\ lead = None
    /\ raftLog = [committed |-> 0, applied |-> 0, entries |-> <<>>, 
                  lastIndex |-> 0, lastTerm |-> 0]
    /\ msgs = <<>>
    /\ msgsAfterAppend = <<>>
    /\ trk = [n \in Nodes |-> [Match |-> 0, Next |-> 1, State |-> "StateProbe",
                               RecentActive |-> FALSE, IsLearner |-> FALSE,
                               Inflights |-> [start |-> 0, count |-> 0, buffer |-> <<>>]]]
    /\ electionElapsed = 0
    /\ heartbeatElapsed = 0
    /\ randomizedElectionTimeout = ElectionTimeout
    /\ pendingConfIndex = 0
    /\ uncommittedSize = 0
    /\ leadTransferee = None
    /\ readStates = <<>>
    /\ pendingReadIndexMessages = <<>>
    /\ isLearner = FALSE
    /\ preVote = TRUE
    /\ checkQuorum = TRUE
    /\ disableProposalForwarding = FALSE
    /\ stepDownOnRemoval = TRUE
    /\ readOnly = [option |-> "ReadOnlySafe", pendingReadIndex |-> <<>>]

\* Helper functions
send(m) ==
    LET msg == IF m.From = None THEN [m EXCEPT !.From = id] ELSE m IN
    IF msg.Type \in {MsgAppResp, MsgVoteResp, MsgPreVoteResp}
    THEN msgsAfterAppend' = Append(msgsAfterAppend, msg)
    ELSE msgs' = Append(msgs, msg)

reset(term) ==
    /\ IF Term # term 
       THEN /\ Term' = term
            /\ Vote' = None
       ELSE UNCHANGED <<Term, Vote>>
    /\ lead' = None
    /\ electionElapsed' = 0
    /\ heartbeatElapsed' = 0
    /\ randomizedElectionTimeout' = ElectionTimeout + (term % ElectionTimeout)
    /\ leadTransferee' = None
    /\ trk' = [n \in Nodes |-> 
               [Match |-> 0, 
                Next |-> raftLog.lastIndex + 1,
                State |-> "StateProbe",
                RecentActive |-> FALSE,
                IsLearner |-> trk[n].IsLearner,
                Inflights |-> [start |-> 0, count |-> 0, buffer |-> <<>>]]]
    /\ pendingConfIndex' = 0
    /\ uncommittedSize' = 0
    /\ readOnly' = [option |-> readOnly.option, pendingReadIndex |-> <<>>]

\* Core function: becomeFollower
becomeFollower(term, leader) ==
    /\ reset(term)
    /\ state' = StateFollower
    /\ lead' = leader
    /\ UNCHANGED <<id, raftLog, msgs, msgsAfterAppend, readStates, 
                   pendingReadIndexMessages, isLearner, preVote, checkQuorum,
                   disableProposalForwarding, stepDownOnRemoval>>

\* Core function: becomeCandidate
becomeCandidate ==
    /\ state # StateLeader  \* Panic if transitioning from leader
    /\ reset(Term + 1)
    /\ state' = StateCandidate
    /\ Vote' = id
    /\ UNCHANGED <<id, raftLog, msgs, msgsAfterAppend, readStates,
                   pendingReadIndexMessages, isLearner, preVote, checkQuorum,
                   disableProposalForwarding, stepDownOnRemoval>>

\* Core function: becomePreCandidate
becomePreCandidate ==
    /\ state # StateLeader  \* Panic if transitioning from leader
    /\ state' = StatePreCandidate
    /\ trk' = [trk EXCEPT ![id].Match = 0, ![id].Next = raftLog.lastIndex + 1]
    /\ lead' = None
    /\ UNCHANGED <<id, Term, Vote, raftLog, msgs, msgsAfterAppend, 
                   electionElapsed, heartbeatElapsed, randomizedElectionTimeout,
                   pendingConfIndex, uncommittedSize, leadTransferee, readStates,
                   pendingReadIndexMessages, isLearner, preVote, checkQuorum,
                   disableProposalForwarding, stepDownOnRemoval, readOnly>>

\* Core function: becomeLeader
becomeLeader ==
    /\ state # StateFollower  \* Panic if transitioning from follower
    /\ reset(Term)
    /\ state' = StateLeader
    /\ lead' = id
    /\ trk' = [trk EXCEPT ![id].State = "StateReplicate", 
                          ![id].Match = raftLog.lastIndex,
                          ![id].RecentActive = TRUE]
    /\ pendingConfIndex' = raftLog.lastIndex
    /\ LET emptyEntry == [Term |-> Term, Index |-> raftLog.lastIndex + 1, 
                          Type |-> "EntryNormal", Data |-> <<>>] IN
       /\ raftLog' = [raftLog EXCEPT !.entries = Append(raftLog.entries, emptyEntry),
                                     !.lastIndex = raftLog.lastIndex + 1,
                                     !.lastTerm = Term]
       /\ send([To |-> id, Type |-> MsgAppResp, Index |-> raftLog.lastIndex + 1])
    /\ UNCHANGED <<id, Vote, electionElapsed, heartbeatElapsed, 
                   randomizedElectionTimeout, uncommittedSize, leadTransferee,
                   readStates, pendingReadIndexMessages, isLearner, preVote,
                   checkQuorum, disableProposalForwarding, stepDownOnRemoval>>

\* Core function: campaign
campaign(t) ==
    LET voteMsg == IF t = campaignPreElection THEN MsgPreVote ELSE MsgVote
        term == IF t = campaignPreElection THEN Term + 1 ELSE Term
        ctx == IF t = campaignTransfer THEN <<t>> ELSE <<>>
    IN
    /\ IF t = campaignPreElection 
       THEN becomePreCandidate
       ELSE becomeCandidate
    /\ send([To |-> id, Term |-> term, Type |-> IF voteMsg = MsgVote 
                                                 THEN MsgVoteResp 
                                                 ELSE MsgPreVoteResp])
    /\ \A n \in Nodes \ {id} :
       send([To |-> n, Term |-> term, Type |-> voteMsg, 
             Index |-> raftLog.lastIndex, LogTerm |-> raftLog.lastTerm,
             Context |-> ctx])

\* Core function: poll
poll(nodeId, msgType, granted) ==
    LET updatedTrk == IF granted 
                      THEN [trk EXCEPT ![nodeId].Match = raftLog.lastIndex]
                      ELSE trk
        grantedCount == Cardinality({n \in Nodes : updatedTrk[n].Match > 0})
        rejectedCount == Cardinality(Nodes) - grantedCount
        majority == (Cardinality(Nodes) \div 2) + 1
    IN
    /\ trk' = updatedTrk
    /\ IF grantedCount >= majority
       THEN "VoteWon"
       ELSE IF rejectedCount >= majority
            THEN "VoteLost"
            ELSE "VotePending"

\* Core function: appendEntry
appendEntry(entries) ==
    LET li == raftLog.lastIndex
        newEntries == [i \in 1..Len(entries) |-> 
                       [entries[i] EXCEPT !.Term = Term, 
                                          !.Index = li + i]]
        totalSize == Len(entries)  \* Simplified size calculation
    IN
    /\ uncommittedSize + totalSize <= 1000  \* maxUncommittedSize check
    /\ raftLog' = [raftLog EXCEPT !.entries = raftLog.entries \o newEntries,
                                  !.lastIndex = li + Len(entries),
                                  !.lastTerm = Term]
    /\ uncommittedSize' = uncommittedSize + totalSize
    /\ send([To |-> id, Type |-> MsgAppResp, Index |-> li + Len(entries)])
    /\ UNCHANGED <<id, Term, Vote, state, lead, trk, electionElapsed,
                   heartbeatElapsed, randomizedElectionTimeout, pendingConfIndex,
                   leadTransferee, readStates, pendingReadIndexMessages, isLearner,
                   preVote, checkQuorum, disableProposalForwarding, stepDownOnRemoval,
                   readOnly>>

\* Core function: maybeCommit
maybeCommit ==
    LET matchIndexes == {trk[n].Match : n \in Nodes}
        sortedMatches == CHOOSE seq \in [1..Cardinality(matchIndexes) -> matchIndexes] :
                         \A i,j \in 1..Len(seq) : i < j => seq[i] >= seq[j]
        commitIndex == IF Len(sortedMatches) >= (Cardinality(Nodes) \div 2) + 1
                       THEN sortedMatches[(Cardinality(Nodes) \div 2) + 1]
                       ELSE raftLog.committed
    IN
    /\ commitIndex > raftLog.committed
    /\ \E entry \in raftLog.entries : 
       /\ entry.Index = commitIndex
       /\ entry.Term = Term
    /\ raftLog' = [raftLog EXCEPT !.committed = commitIndex]
    /\ UNCHANGED <<id, Term, Vote, state, lead, msgs, msgsAfterAppend, trk,
                   electionElapsed, heartbeatElapsed, randomizedElectionTimeout,
                   pendingConfIndex, uncommittedSize, leadTransferee, readStates,
                   pendingReadIndexMessages, isLearner, preVote, checkQuorum,
                   disableProposalForwarding, stepDownOnRemoval, readOnly>>

\* Core function: handleAppendEntries
handleAppendEntries(m) ==
    IF m.Index < raftLog.committed
    THEN send([To |-> m.From, Type |-> MsgAppResp, Index |-> raftLog.committed])
    ELSE IF \E entry \in raftLog.entries : 
            /\ entry.Index = m.Index 
            /\ entry.Term = m.LogTerm
         THEN LET newEntries == m.Entries
                  lastNewIndex == m.Index + Len(newEntries)
              IN
              /\ raftLog' = [raftLog EXCEPT 
                            !.entries = SubSeq(raftLog.entries, 1, m.Index) \o newEntries,
                            !.lastIndex = lastNewIndex,
                            !.committed = IF m.Commit > raftLog.committed 
                                          THEN Min(m.Commit, lastNewIndex)
                                          ELSE raftLog.committed]
              /\ send([To |-> m.From, Type |-> MsgAppResp, Index |-> lastNewIndex])
         ELSE LET hintIndex == Min(m.Index, raftLog.lastIndex)
                  hintTerm == IF \E e \in raftLog.entries : e.Index = hintIndex
                              THEN CHOOSE e \in raftLog.entries : e.Index = hintIndex
                              ELSE 0
              IN
              send([To |-> m.From, Type |-> MsgAppResp, Index |-> m.Index,
                    Reject |-> TRUE, RejectHint |-> hintIndex, LogTerm |-> hintTerm.Term])

\* Core function: Step - Main message processing
Step(m) ==
    \/ m.Term > Term /\ m.Type # MsgPreVote =>
       IF m.Type \in {MsgApp, MsgHeartbeat, MsgSnap}
       THEN becomeFollower(m.Term, m.From)
       ELSE becomeFollower(m.Term, None)
    \/ m.Term < Term =>
       IF (checkQuorum \/ preVote) /\ m.Type \in {MsgHeartbeat, MsgApp}
       THEN send([To |-> m.From, Type |-> MsgAppResp])
       ELSE IF m.Type = MsgPreVote
            THEN send([To |-> m.From, Term |-> Term, Type |-> MsgPreVoteResp, Reject |-> TRUE])
            ELSE TRUE  \* Ignore other messages
    \/ m.Term = Term =>
       CASE m.Type = MsgHup ->
            IF preVote 
            THEN campaign(campaignPreElection)
            ELSE campaign(campaignElection)
       [] m.Type \in {MsgVote, MsgPreVote} ->
            LET canVote == Vote = m.From \/ (Vote = None /\ lead = None) \/
                           (m.Type = MsgPreVote /\ m.Term > Term)
                lastID == [term |-> raftLog.lastTerm, index |-> raftLog.lastIndex]
                candLastID == [term |-> m.LogTerm, index |-> m.Index]
                upToDate == candLastID.term > lastID.term \/
                            (candLastID.term = lastID.term /\ candLastID.index >= lastID.index)
            IN
            IF canVote /\ upToDate
            THEN /\ send([To |-> m.From, Term |-> m.Term, 
                          Type |-> IF m.Type = MsgVote THEN MsgVoteResp ELSE MsgPreVoteResp])
                 /\ IF m.Type = MsgVote
                    THEN /\ electionElapsed' = 0
                         /\ Vote' = m.From
                    ELSE UNCHANGED <<electionElapsed, Vote>>
            ELSE send([To |-> m.From, Term |-> Term, 
                       Type |-> IF m.Type = MsgVote THEN MsgVoteResp ELSE MsgPreVoteResp,
                       Reject |-> TRUE])
       [] OTHER ->
            CASE state = StateLeader -> stepLeader(m)
            [] state \in {StateCandidate, StatePreCandidate} -> stepCandidate(m)
            [] state = StateFollower -> stepFollower(m)

\* Core function: stepLeader
stepLeader(m) ==
    CASE m.Type = MsgBeat ->
         \A n \in Nodes \ {id} : 
         send([To |-> n, Type |-> MsgHeartbeat, Commit |-> raftLog.committed])
    [] m.Type = MsgCheckQuorum ->
         LET activeNodes == {n \in Nodes : trk[n].RecentActive}
             quorumActive == Cardinality(activeNodes) >= (Cardinality(Nodes) \div 2) + 1
         IN
         IF ~quorumActive
         THEN becomeFollower(Term, None)
         ELSE /\ trk' = [n \in Nodes |-> 
                         IF n = id THEN trk[n] 
                         ELSE [trk[n] EXCEPT !.RecentActive = FALSE]]
              /\ UNCHANGED <<id, Term, Vote, state, lead, raftLog, msgs, msgsAfterAppend,
                            electionElapsed, heartbeatElapsed, randomizedElectionTimeout,
                            pendingConfIndex, uncommittedSize, leadTransferee, readStates,
                            pendingReadIndexMessages, isLearner, preVote, checkQuorum,
                            disableProposalForwarding, stepDownOnRemoval, readOnly>>
    [] m.Type = MsgProp ->
         IF leadTransferee # None
         THEN TRUE  \* Drop proposal during transfer
         ELSE appendEntry(m.Entries) /\ \A n \in Nodes \ {id} : 
              send([To |-> n, Type |-> MsgApp, Index |-> raftLog.lastIndex - Len(m.Entries),
                    LogTerm |-> raftLog.lastTerm, Entries |-> m.Entries,
                    Commit |-> raftLog.committed])
    [] m.Type = MsgAppResp ->
         LET pr == trk[m.From] IN
         /\ trk' = [trk EXCEPT ![m.From].RecentActive = TRUE]
         /\ IF m.Reject
            THEN LET nextIdx == m.RejectHint IN
                 /\ trk' = [trk EXCEPT ![m.From].Next = nextIdx,
                                       ![m.From].State = "StateProbe"]
                 /\ send([To |-> m.From, Type |-> MsgApp, 
                          Index |-> nextIdx - 1,
                          LogTerm |-> IF \E e \in raftLog.entries : e.Index = nextIdx - 1
                                      THEN (CHOOSE e \in raftLog.entries : e.Index = nextIdx - 1).Term
                                      ELSE 0,
                          Entries |-> <<>>,
                          Commit |-> raftLog.committed])
            ELSE /\ trk' = [trk EXCEPT ![m.From].Match = m.Index,
                                       ![m.From].Next = m.Index + 1,
                                       ![m.From].State = "StateReplicate"]
                 /\ maybeCommit
                 /\ IF m.From = leadTransferee /\ trk'[m.From].Match = raftLog.lastIndex
                    THEN send([To |-> m.From, Type |-> MsgTimeoutNow])
                    ELSE TRUE
    [] m.Type = MsgHeartbeatResp ->
         /\ trk' = [trk EXCEPT ![m.From].RecentActive = TRUE]
         /\ IF trk[m.From].Match < raftLog.lastIndex
            THEN send([To |-> m.From, Type |-> MsgApp,
                       Index |-> trk[m.From].Next - 1,
                       LogTerm |-> IF \E e \in raftLog.entries : e.Index = trk[m.From].Next - 1
                                   THEN (CHOOSE e \in raftLog.entries : e.Index = trk[m.From].Next - 1).Term
                                   ELSE 0,
                       Entries |-> <<>>,
                       Commit |-> raftLog.committed])
            ELSE TRUE
    [] OTHER -> TRUE

\* Core function: stepCandidate
stepCandidate(m) ==
    LET myVoteRespType == IF state = StatePreCandidate THEN MsgPreVoteResp ELSE MsgVoteResp IN
    CASE m.Type = MsgProp ->
         TRUE  \* Drop proposals when not leader
    [] m.Type = MsgApp ->
         /\ becomeFollower(m.Term, m.From)
         /\ handleAppendEntries(m)
    [] m.Type = MsgHeartbeat ->
         /\ becomeFollower(m.Term, m.From)
         /\ raftLog' = [raftLog EXCEPT !.committed = m.Commit]
         /\ send([To |-> m.From, Type |-> MsgHeartbeatResp, Context |-> m.Context])
    [] m.Type = MsgSnap ->
         /\ becomeFollower(m.Term, m.From)
         /\ TRUE  \* Handle snapshot
    [] m.Type = myVoteRespType ->
         LET result == poll(m.From, m.Type, ~m.Reject) IN
         CASE result = "VoteWon" ->
              IF state = StatePreCandidate
              THEN campaign(campaignElection)
              ELSE becomeLeader /\ \A n \in Nodes \ {id} :
                   send([To |-> n, Type |-> MsgApp, Index |-> raftLog.lastIndex,
                         LogTerm |-> raftLog.lastTerm, Entries |-> <<>>,
                         Commit |-> raftLog.committed])
         [] result = "VoteLost" ->
              becomeFollower(Term, None)
         [] OTHER -> TRUE
    [] OTHER -> TRUE

\* Core function: stepFollower
stepFollower(m) ==
    CASE m.Type = MsgProp ->
         IF lead = None \/ disableProposalForwarding
         THEN TRUE  \* Drop proposal
         ELSE send([m EXCEPT !.To = lead])
    [] m.Type = MsgApp ->
         /\ electionElapsed' = 0
         /\ lead' = m.From
         /\ handleAppendEntries(m)
    [] m.Type = MsgHeartbeat ->
         /\ electionElapsed' = 0
         /\ lead' = m.From
         /\ raftLog' = [raftLog EXCEPT !.committed = m.Commit]
         /\ send([To |-> m.From, Type |-> MsgHeartbeatResp, Context |-> m.Context])
    [] m.Type = MsgSnap ->
         /\ electionElapsed' = 0
         /\ lead' = m.From
         /\ TRUE  \* Handle snapshot
    [] m.Type = MsgTimeoutNow ->
         campaign(campaignTransfer)
    [] m.Type = MsgReadIndex ->
         IF lead = None
         THEN TRUE  \* Drop
         ELSE send([m EXCEPT !.To = lead])
    [] m.Type = MsgReadIndexResp ->
         readStates' = Append(readStates, 
                              [Index |-> m.Index, RequestCtx |-> m.Entries[1].Data])
    [] OTHER -> TRUE

\* Tick functions
tickElection ==
    /\ electionElapsed' = electionElapsed + 1
    /\ electionElapsed' >= randomizedElectionTimeout =>
       /\ electionElapsed' = 0
       /\ Step([From |-> id, Type |-> MsgHup])
    /\ UNCHANGED <<id, Term, Vote, state, lead, raftLog, msgs, msgsAfterAppend,
                   trk, heartbeatElapsed, randomizedElectionTimeout, pendingConfIndex,
                   uncommittedSize, leadTransferee, readStates, pendingReadIndexMessages,
                   isLearner, preVote, checkQuorum, disableProposalForwarding,
                   stepDownOnRemoval, readOnly>>

tickHeartbeat ==
    /\ heartbeatElapsed' = heartbeatElapsed + 1
    /\ electionElapsed' = electionElapsed + 1
    /\ electionElapsed' >= ElectionTimeout =>
       IF checkQuorum
       THEN Step([From |-> id, Type |-> MsgCheckQuorum])
       ELSE IF state = StateLeader /\ leadTransferee # None
            THEN leadTransferee' = None
            ELSE TRUE
    /\ state = StateLeader /\ heartbeatElapsed' >= HeartbeatTimeout =>
       /\ heartbeatElapsed' = 0
       /\ Step([From |-> id, Type |-> MsgBeat])
    /\ UNCHANGED <<id, Term, Vote, raftLog, msgs, msgsAfterAppend, trk,
                   randomizedElectionTimeout, pendingConfIndex, uncommittedSize,
                   readStates, pendingReadIndexMessages, isLearner, preVote,
                   checkQuorum, disableProposalForwarding, stepDownOnRemoval, readOnly>>

Next == 
    \/ \E m \in msgs : Step(m)
    \/ \E m \in msgsAfterAppend : Step(m)
    \/ state \in {StateFollower, StateCandidate, StatePreCandidate} /\ tickElection
    \/ state = StateLeader /\ tickHeartbeat
    \/ \E nodeId \in Nodes, t \in {campaignPreElection, campaignElection, campaignTransfer} :
       campaign(t)
    \/ \E entries \in SUBSET raftLog.entries : appendEntry(entries)
    \/ maybeCommit

Spec == Init /\ [][Next]_vars

===