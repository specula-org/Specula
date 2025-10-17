---- MODULE etcdraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS
    Servers,          \* The set of server IDs, e.g., {1, 2, 3}
    DefaultValue,     \* A default value for client proposals
    ElectionTimeout,  \* Ticks before an election is called
    HeartbeatTimeout  \* Ticks between leader heartbeats

ASSUME /\ TLC!Print("TLC assumptions:", TRUE)
       /\ Servers \subseteq Nat \ {0}
       /\ IsFiniteSet(Servers)
       /\ Cardinality(Servers) % 2 = 1
       /\ ElectionTimeout \in Nat
       /\ HeartbeatTimeout \in Nat
       /\ ElectionTimeout > HeartbeatTimeout

\* Node states from the Go code
ServerStates == {"StateFollower", "StateCandidate", "StatePreCandidate", "StateLeader"}

\* A sentinel value for no vote or no leader
None == 0

VARIABLES
    \* The state of each server
    vars,
    \* The network is a bag of messages
    network

\* Helper for quorum size
Quorum == (Cardinality(Servers) \div 2) + 1

\* Helper for log properties
LastLogIndex(log) == Len(log)
LastLogTerm(log) == IF Len(log) = 0 THEN 0 ELSE log[Len(log)].term

\* The log up-to-date check from the paper and code
isUpToDate(candidateTerm, candidateIndex, myLog) ==
    LET myLastTerm == LastLogTerm(myLog)
        myLastIndex == LastLogIndex(myLog)
    IN \/ candidateTerm > myLastTerm
       \/ /\ candidateTerm = myLastTerm
          /\ candidateIndex >= myLastIndex

\* Initial state
Init ==
    /\ vars = [s \in Servers |->
        [
            state |-> "StateFollower",
            currentTerm |-> 0,
            votedFor |-> None,
            log |-> << >>,
            commitIndex |-> 0,
            leader |-> None,
            votesGranted |-> {},
            nextIndex |-> [p \in Servers |-> 1],
            matchIndex |-> [p \in Servers |-> 0],
            electionElapsed |-> 0,
            heartbeatElapsed |-> 0
        ]
    ]
    /\ network = EmptyBag

\*=============================================================================
\* ACTIONS
\*=============================================================================

\* A server's timer ticks.
Tick(s) ==
    /\ \/ /\ vars[s].state \in {"StateFollower", "StateCandidate", "StatePreCandidate"}
          /\ vars' = [vars EXCEPT ![s].electionElapsed = @ + 1]
       \/ /\ vars[s].state = "StateLeader"
          /\ vars' = [vars EXCEPT ![s].heartbeatElapsed = @ + 1]
    /\ UNCHANGED network

\* A follower or candidate times out and starts a pre-vote campaign.
\* This corresponds to the `tickElection` function leading to `MsgHup`.
TimeoutStartPreVote(s) ==
    LET self == vars[s]
    IN /\ self.state \in {"StateFollower", "StatePreCandidate"}
       /\ self.electionElapsed >= ElectionTimeout
       /\ LET nextTerm == self.currentTerm + 1
              lastLogIdx == LastLogIndex(self.log)
              lastLogTerm == LastLogTerm(self.log)
          IN /\ vars' = [vars EXCEPT ![s] = [
                    self EXCEPT
                    !.state = "StatePreCandidate",
                    !.votesGranted = {s},
                    !.electionElapsed = 0
               ]]
             /\ network' = network \+ Bag({
                   [
                       type |-> "MsgPreVote",
                       from |-> s,
                       to |-> p,
                       term |-> nextTerm,
                       lastLogIndex |-> lastLogIdx,
                       lastLogTerm |-> lastLogTerm
                   ] : p \in Servers \ {s}
               })

\* A candidate times out and starts a new election campaign.
TimeoutStartVote(s) ==
    LET self == vars[s]
    IN /\ self.state = "StateCandidate"
       /\ self.electionElapsed >= ElectionTimeout
       /\ LET nextTerm == self.currentTerm + 1
              lastLogIdx == LastLogIndex(self.log)
              lastLogTerm == LastLogTerm(self.log)
          IN /\ vars' = [vars EXCEPT ![s] = [
                    self EXCEPT
                    !.currentTerm = nextTerm,
                    !.votedFor = s,
                    !.votesGranted = {s},
                    !.electionElapsed = 0
               ]]
             /\ network' = network \+ Bag({
                   [
                       type |-> "MsgVote",
                       from |-> s,
                       to |-> p,
                       term |-> nextTerm,
                       lastLogIndex |-> lastLogIdx,
                       lastLogTerm |-> lastLogTerm
                   ] : p \in Servers \ {s}
               })

\* A leader's heartbeat timer fires.
\* This corresponds to `tickHeartbeat` leading to `MsgBeat`.
LeaderHeartbeat(s) ==
    LET self == vars[s]
    IN /\ self.state = "StateLeader"
       /\ self.heartbeatElapsed >= HeartbeatTimeout
       /\ vars' = [vars EXCEPT ![s].heartbeatElapsed = 0]
       /\ network' = network \+ Bag({
              [
                  type |-> "MsgApp",
                  from |-> s,
                  to |-> p,
                  term |-> self.currentTerm,
                  prevLogIndex |-> self.nextIndex[p] - 1,
                  prevLogTerm |-> IF self.nextIndex[p] - 1 > 0 THEN self.log[self.nextIndex[p] - 1].term ELSE 0,
                  entries |-> << >>,
                  commitIndex |-> self.commitIndex
              ] : p \in Servers \ {s}
          })

\* A leader proposes a new command. This corresponds to receiving `MsgProp`.
LeaderPropose(s) ==
    LET self == vars[s]
    IN /\ self.state = "StateLeader"
       /\ LET newEntry == [term |-> self.currentTerm, value |-> DefaultValue]
              newLog == Append(self.log, newEntry)
          IN vars' = [vars EXCEPT ![s].log = newLog, ![s].matchIndex[s] = Len(newLog), ![s].nextIndex[s] = Len(newLog) + 1]
       /\ UNCHANGED network

\* A leader sends AppendEntries RPCs to followers.
LeaderSendAppend(s) ==
    LET self == vars[s]
    IN /\ self.state = "StateLeader"
       /\ \E p \in Servers \ {s}:
            LET prevLogIdx == self.nextIndex[p] - 1
                lastEntryIdx == LastLogIndex(self.log)
            IN /\ self.matchIndex[p] < lastEntryIdx
               /\ LET prevLogTerm == IF prevLogIdx > 0 THEN self.log[prevLogIdx].term ELSE 0
                      entriesToSend == SubSeq(self.log, self.nextIndex[p], lastEntryIdx)
                  IN network' = network \+ Bag({[
                         type |-> "MsgApp",
                         from |-> s,
                         to |-> p,
                         term |-> self.currentTerm,
                         prevLogIndex |-> prevLogIdx,
                         prevLogTerm |-> prevLogTerm,
                         entries |-> entriesToSend,
                         commitIndex |-> self.commitIndex
                     ]})
       /\ UNCHANGED vars

\* A node becomes a follower.
BecomeFollower(s, newTerm, newLeader) ==
    [vars[s] EXCEPT
        !.state = "StateFollower",
        !.currentTerm = newTerm,
        !.votedFor = None,
        !.leader = newLeader,
        !.votesGranted = {}
    ]

\* Logic for handling AppendEntries (MsgApp)
HandleAppendEntries(msg, s) ==
    LET to == msg.to
    IN
    IF msg.term < s.currentTerm THEN
        /\ network' = network \+ Bag({[
               type |-> "MsgAppResp",
               from |-> to,
               to |-> msg.from,
               term |-> s.currentTerm,
               success |-> FALSE,
               matchIndex |-> 0
           ]})
        /\ UNCHANGED vars
    ELSE
        /\ LET logOK == \/ msg.prevLogIndex = 0
                       \/ /\ msg.prevLogIndex <= Len(s.log)
                          /\ s.log[msg.prevLogIndex].term = msg.prevLogTerm
           IN IF logOK THEN
                /\ LET newLog ==
                       LET unconflicting == SubSeq(s.log, 1, msg.prevLogIndex)
                       IN Concat(unconflicting, msg.entries)
                   newCommitIndex == max(s.commitIndex, msg.commitIndex)
                IN /\ vars' = [vars EXCEPT ![to] = [
                       BecomeFollower(to, msg.term, msg.from) EXCEPT
                       !.electionElapsed = 0,
                       !.log = newLog,
                       !.commitIndex = newCommitIndex
                   ]]
                   /\ network' = network \+ Bag({[
                          type |-> "MsgAppResp",
                          from |-> to,
                          to |-> msg.from,
                          term |-> msg.term,
                          success |-> TRUE,
                          matchIndex |-> LastLogIndex(newLog)
                      ]})
              ELSE
                /\ vars' = [vars EXCEPT ![to] = [
                       BecomeFollower(to, msg.term, msg.from) EXCEPT
                       !.electionElapsed = 0
                   ]]
                /\ network' = network \+ Bag({[
                       type |-> "MsgAppResp",
                       from |-> to,
                       to |-> msg.from,
                       term |-> msg.term,
                       success |-> FALSE,
                       matchIndex |-> 0
                   ]})

\* Logic for handling AppendEntriesResponse (MsgAppResp)
HandleAppendEntriesResponse(msg, s) ==
    LET to == msg.to
    IN
    IF s.state = "StateLeader" /\ msg.term = s.currentTerm THEN
        /\ IF msg.success THEN
             /\ LET newNextIndex == [s.nextIndex EXCEPT ![msg.from] = msg.matchIndex + 1]
                    newMatchIndex == [s.matchIndex EXCEPT ![msg.from] = msg.matchIndex]
                    newCommitIndex ==
                        LET CanCommit(idx) ==
                                /\ idx > s.commitIndex
                                /\ s.log[idx].term = s.currentTerm
                                /\ Cardinality({p \in Servers |-> newMatchIndex[p] >= idx} \cup {to}) >= Quorum
                        IN IF \E idx \in (s.commitIndex+1)..Len(s.log): CanCommit(idx)
                           THEN Max({idx \in (s.commitIndex+1)..Len(s.log) : CanCommit(idx)})
                           ELSE s.commitIndex
                IN vars' = [vars EXCEPT ![to] = [
                       s EXCEPT
                       !.nextIndex = newNextIndex,
                       !.matchIndex = newMatchIndex,
                       !.commitIndex = newCommitIndex
                   ]]
           ELSE
             /\ vars' = [vars EXCEPT ![to].nextIndex[msg.from] = max(1, @ - 1)]
        /\ UNCHANGED network
    ELSE
        /\ UNCHANGED <<vars, network>>

\* Logic for handling RequestPreVote (MsgPreVote)
HandleRequestPreVote(msg, s) ==
    LET to == msg.to
        candidateLogUpToDate == isUpToDate(msg.lastLogTerm, msg.lastLogIndex, s.log)
        grant == msg.term > s.currentTerm /\ candidateLogUpToDate
    IN
    /\ network' = network \+ Bag({[
           type |-> "MsgPreVoteResp",
           from |-> to,
           to |-> msg.from,
           term |-> msg.term,
           voteGranted |-> grant
       ]})
    /\ UNCHANGED vars

\* Logic for handling RequestPreVoteResponse (MsgPreVoteResp)
HandleRequestPreVoteResponse(msg, s) ==
    LET to == msg.to
    IN
    IF s.state = "StatePreCandidate" /\ msg.term = s.currentTerm + 1 THEN
        /\ IF msg.voteGranted THEN
             /\ LET newVotes == s.votesGranted \cup {msg.from}
                IN IF Cardinality(newVotes) >= Quorum THEN
                     /\ LET nextTerm == s.currentTerm + 1
                            lastLogIdx == LastLogIndex(s.log)
                            lastLogTerm == LastLogTerm(s.log)
                        IN vars' = [vars EXCEPT ![to] = [
                               s EXCEPT
                               !.state = "StateCandidate",
                               !.currentTerm = nextTerm,
                               !.votedFor = to,
                               !.votesGranted = {to},
                               !.electionElapsed = 0
                           ]]
                           network' = network \+ Bag({
                               [
                                   type |-> "MsgVote",
                                   from |-> to,
                                   to |-> p,
                                   term |-> nextTerm,
                                   lastLogIndex |-> lastLogIdx,
                                   lastLogTerm |-> lastLogTerm
                               ] : p \in Servers \ {to}
                           })
                   ELSE
                     /\ vars' = [vars EXCEPT ![to].votesGranted = newVotes]
                     /\ UNCHANGED network
           ELSE
             /\ UNCHANGED <<vars, network>>
    ELSE
        /\ UNCHANGED <<vars, network>>

\* Logic for handling RequestVote (MsgVote)
HandleRequestVote(msg, s) ==
    LET to == msg.to
        candidateLogUpToDate == isUpToDate(msg.lastLogTerm, msg.lastLogIndex, s.log)
        grant == (s.votedFor = None \/ s.votedFor = msg.from) /\ candidateLogUpToDate
    IN
    IF msg.term < s.currentTerm THEN
        /\ network' = network \+ Bag({[
               type |-> "MsgVoteResp",
               from |-> to,
               to |-> msg.from,
               term |-> s.currentTerm,
               voteGranted |-> FALSE
           ]})
        /\ UNCHANGED vars
    ELSE
        /\ IF grant THEN
            /\ vars' = [vars EXCEPT ![to].votedFor = msg.from]
            /\ network' = network \+ Bag({[
                   type |-> "MsgVoteResp",
                   from |-> to,
                   to |-> msg.from,
                   term |-> msg.term,
                   voteGranted |-> TRUE
               ]})
        ELSE
            /\ network' = network \+ Bag({[
                   type |-> "MsgVoteResp",
                   from |-> to,
                   to |-> msg.from,
                   term |-> msg.term,
                   voteGranted |-> FALSE
               ]})
            /\ UNCHANGED vars

\* Logic for handling RequestVoteResponse (MsgVoteResp)
HandleRequestVoteResponse(msg, s) ==
    LET to == msg.to
    IN
    IF s.state = "StateCandidate" /\ msg.term = s.currentTerm THEN
        /\ IF msg.voteGranted THEN
             /\ LET newVotes == s.votesGranted \cup {msg.from}
                IN IF Cardinality(newVotes) >= Quorum THEN
                     /\ vars' = [vars EXCEPT ![to] = [
                            s EXCEPT
                            !.state = "StateLeader",
                            !.leader = to,
                            !.nextIndex = [p \in Servers |-> LastLogIndex(s.log) + 1],
                            !.matchIndex = [p \in Servers |-> IF p = to THEN LastLogIndex(s.log) ELSE 0]
                        ]]
                     /\ UNCHANGED network
                   ELSE
                     /\ vars' = [vars EXCEPT ![to].votesGranted = newVotes]
                     /\ UNCHANGED network
           ELSE
             /\ IF msg.term > s.currentTerm THEN
                  /\ vars' = [vars EXCEPT ![to] = BecomeFollower(to, msg.term, None)]
                  /\ UNCHANGED network
                ELSE
                  /\ UNCHANGED <<vars, network>>
    ELSE
        /\ UNCHANGED <<vars, network>>

\* A message is received from the network.
Receive(msg) ==
    LET to == msg.to
        s == vars[to]
    IN
    IF msg.term > s.currentTerm THEN
        LET s_new_term == [s EXCEPT !.currentTerm = msg.term]
        IN
        CASE msg.type = "MsgApp" \/ msg.type = "MsgHeartbeat" ->
            HandleAppendEntries(msg, s_new_term)
        [] msg.type = "MsgVote" ->
            HandleRequestVote(msg, [BecomeFollower(to, msg.term, None) EXCEPT !.currentTerm = msg.term])
        [] OTHER ->
            /\ vars' = [vars EXCEPT ![to] = BecomeFollower(to, msg.term, None)]
            /\ UNCHANGED network
    ELSE
        CASE msg.type = "MsgApp" -> HandleAppendEntries(msg, s)
        [] msg.type = "MsgAppResp" -> HandleAppendEntriesResponse(msg, s)
        [] msg.type = "MsgPreVote" -> HandleRequestPreVote(msg, s)
        [] msg.type = "MsgPreVoteResp" -> HandleRequestPreVoteResponse(msg, s)
        [] msg.type = "MsgVote" -> HandleRequestVote(msg, s)
        [] msg.type = "MsgVoteResp" -> HandleRequestVoteResponse(msg, s)

ProcessMessage ==
    /\ \E msg \in BagToSet(network):
        /\ network' = network - Bag({msg})
        /\ Receive(msg)

\* A message in the network is lost.
DropMessage ==
    /\ \E msg \in BagToSet(network):
        /\ network' = network - Bag({msg})
        /\ UNCHANGED vars

\* A message in the network is duplicated.
DuplicateMessage ==
    /\ \E msg \in BagToSet(network):
        /\ network' = network \+ Bag({msg})
        /\ UNCHANGED vars

\*=============================================================================
\* Next-state relation
\*=============================================================================
Next ==
    \/ ProcessMessage
    \/ DropMessage
    \/ DuplicateMessage
    \/ \E s \in Servers:
        \/ Tick(s)
        \/ TimeoutStartPreVote(s)
        \/ TimeoutStartVote(s)
        \/ LeaderHeartbeat(s)
        \/ LeaderPropose(s)
        \/ LeaderSendAppend(s)

\*=============================================================================
\* Specification
\*=============================================================================
Spec == Init /\ [][Next]_<<vars, network>>

====