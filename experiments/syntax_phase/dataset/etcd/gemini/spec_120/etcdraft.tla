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
          /\ vars' = [vars EXCEPT ![s] = [vars[s] EXCEPT !.electionElapsed = @ + 1]]
       \/ /\ vars[s].state = "StateLeader"
          /\ vars' = [vars EXCEPT ![s] = [vars[s] EXCEPT !.heartbeatElapsed = @ + 1]]
    /\ UNCHANGED network

\* A follower or candidate times out and starts a pre-vote campaign.
\* This corresponds to the `tickElection` function leading to `MsgHup`.
TimeoutStartPreVote(s) ==
    LET self == vars[s]
        nextTerm == self.currentTerm + 1
        lastLogIdx == LastLogIndex(self.log)
        lastLogTerm == LastLogTerm(self.log)
    IN /\ self.state \in {"StateFollower", "StatePreCandidate"}
       /\ self.electionElapsed >= ElectionTimeout
       /\ vars' = [vars EXCEPT ![s] = [
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
        nextTerm == self.currentTerm + 1
        lastLogIdx == LastLogIndex(self.log)
        lastLogTerm == LastLogTerm(self.log)
    IN /\ self.state = "StateCandidate"
       /\ self.electionElapsed >= ElectionTimeout
       /\ vars' = [vars EXCEPT ![s] = [
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
        newEntry == [term |-> self.currentTerm, value |-> DefaultValue]
        newLog == Append(self.log, newEntry)
    IN /\ self.state = "StateLeader"
       /\ vars' = [vars EXCEPT ![s].log = newLog, ![s].matchIndex[s] = Len(newLog), ![s].nextIndex[s] = Len(newLog) + 1]
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
        !.votesGranted = {},
        !.electionElapsed = 0
    ]

\* Logic for handling AppendEntries (MsgApp)
HandleAppendEntries(msg) ==
    LET s == vars[msg.to]
    IN
    \/ /\ msg.term < s.currentTerm
       /\ network' = network \+ Bag({[
              type |-> "MsgAppResp",
              from |-> msg.to,
              to |-> msg.from,
              term |-> s.currentTerm,
              success |-> FALSE,
              matchIndex |-> 0
          ]})
       /\ UNCHANGED vars
    \/ /\ msg.term >= s.currentTerm
       /\ LET new_s == BecomeFollower(msg.to, msg.term, msg.from)
              logOK == \/ msg.prevLogIndex = 0
                       \/ /\ msg.prevLogIndex <= Len(s.log)
                          /\ s.log[msg.prevLogIndex].term = msg.prevLogTerm
          IN \/ /\ logOK
                /\ LET newLog ==
                       LET unconflicting == SubSeq(s.log, 1, msg.prevLogIndex)
                       IN Concat(unconflicting, msg.entries)
                   newCommitIndex == max(s.commitIndex, msg.commitIndex)
                IN /\ vars' = [vars EXCEPT ![msg.to] = [
                       new_s EXCEPT
                       !.log = newLog,
                       !.commitIndex = newCommitIndex
                   ]]
                   /\ network' = network \+ Bag({[
                          type |-> "MsgAppResp",
                          from |-> msg.to,
                          to |-> msg.from,
                          term |-> msg.term,
                          success |-> TRUE,
                          matchIndex |-> LastLogIndex(newLog)
                      ]})
             \/ /\ \lnot logOK
                /\ vars' = [vars EXCEPT ![msg.to] = new_s]
                /\ network' = network \+ Bag({[
                       type |-> "MsgAppResp",
                       from |-> msg.to,
                       to |-> msg.from,
                       term |-> msg.term,
                       success |-> FALSE,
                       matchIndex |-> 0
                   ]})

\* Logic for handling AppendEntriesResponse (MsgAppResp)
HandleAppendEntriesResponse(msg) ==
    LET s == vars[msg.to]
    IN
    \/ /\ s.state # "StateLeader" \/ msg.term # s.currentTerm
       /\ UNCHANGED <<vars, network>>
    \/ /\ s.state = "StateLeader" /\ msg.term = s.currentTerm
       /\ \/ /\ msg.success
             /\ LET newNextIndex == [s.nextIndex EXCEPT ![msg.from] = msg.matchIndex + 1]
                    newMatchIndex == [s.matchIndex EXCEPT ![msg.from] = msg.matchIndex]
                    newCommitIndex ==
                        LET CanCommit(idx) ==
                                /\ idx > s.commitIndex
                                /\ s.log[idx].term = s.currentTerm
                                /\ Cardinality({p \in Servers | newMatchIndex[p] >= idx}) >= Quorum
                        IN IF \E idx \in (s.commitIndex+1)..Len(s.log): CanCommit(idx)
                           THEN Max({idx \in (s.commitIndex+1)..Len(s.log) : CanCommit(idx)})
                           ELSE s.commitIndex
                IN vars' = [vars EXCEPT ![msg.to] = [
                       s EXCEPT
                       !.nextIndex = newNextIndex,
                       !.matchIndex = newMatchIndex,
                       !.commitIndex = newCommitIndex
                   ]]
          \/ /\ \lnot msg.success
             /\ vars' = [vars EXCEPT ![msg.to].nextIndex = [s.nextIndex EXCEPT ![msg.from] = max(1, s.nextIndex[msg.from] - 1)]]
       /\ UNCHANGED network

\* Logic for handling RequestPreVote (MsgPreVote)
HandleRequestPreVote(msg) ==
    LET s == vars[msg.to]
        candidateLogUpToDate == isUpToDate(msg.lastLogTerm, msg.lastLogIndex, s.log)
        grant == msg.term > s.currentTerm /\ candidateLogUpToDate
    IN
    /\ network' = network \+ Bag({[
           type |-> "MsgPreVoteResp",
           from |-> msg.to,
           to |-> msg.from,
           term |-> msg.term,
           voteGranted |-> grant
       ]})
    /\ UNCHANGED vars

\* Logic for handling RequestPreVoteResponse (MsgPreVoteResp)
HandleRequestPreVoteResponse(msg) ==
    LET s == vars[msg.to]
    IN
    \/ /\ s.state # "StatePreCandidate" \/ msg.term # s.currentTerm + 1
       /\ UNCHANGED <<vars, network>>
    \/ /\ s.state = "StatePreCandidate" /\ msg.term = s.currentTerm + 1
       /\ \/ /\ msg.voteGranted
             /\ LET newVotes == s.votesGranted \cup {msg.from}
                IN \/ /\ Cardinality(newVotes) >= Quorum
                      /\ LET nextTerm == s.currentTerm + 1
                             lastLogIdx == LastLogIndex(s.log)
                             lastLogTerm == LastLogTerm(s.log)
                         IN /\ vars' = [vars EXCEPT ![msg.to] = [
                                s EXCEPT
                                !.state = "StateCandidate",
                                !.currentTerm = nextTerm,
                                !.votedFor = msg.to,
                                !.votesGranted = {msg.to},
                                !.electionElapsed = 0
                            ]]
                            /\ network' = network \+ Bag({
                                [
                                    type |-> "MsgVote",
                                    from |-> msg.to,
                                    to |-> p,
                                    term |-> nextTerm,
                                    lastLogIndex |-> lastLogIdx,
                                    lastLogTerm |-> lastLogTerm
                                ] : p \in Servers \ {msg.to}
                            })
                   \/ /\ Cardinality(newVotes) < Quorum
                      /\ vars' = [vars EXCEPT ![msg.to].votesGranted = newVotes]
                      /\ UNCHANGED network
          \/ /\ \lnot msg.voteGranted
             /\ UNCHANGED <<vars, network>>

\* Logic for handling RequestVote (MsgVote)
HandleRequestVote(msg) ==
    LET s == vars[msg.to]
    IN
    \/ /\ msg.term < s.currentTerm
       /\ network' = network \+ Bag({[
              type |-> "MsgVoteResp",
              from |-> msg.to,
              to |-> msg.from,
              term |-> s.currentTerm,
              voteGranted |-> FALSE
          ]})
       /\ UNCHANGED vars
    \/ /\ msg.term >= s.currentTerm
       /\ LET new_s_base == IF msg.term > s.currentTerm
                           THEN BecomeFollower(msg.to, msg.term, None)
                           ELSE vars[msg.to]
              candidateLogUpToDate == isUpToDate(msg.lastLogTerm, msg.lastLogIndex, new_s_base.log)
              grant == (new_s_base.votedFor = None \/ new_s_base.votedFor = msg.from) /\ candidateLogUpToDate
          IN \/ /\ grant
                /\ vars' = [vars EXCEPT ![msg.to] = [new_s_base EXCEPT !.votedFor = msg.from]]
                /\ network' = network \+ Bag({[
                       type |-> "MsgVoteResp",
                       from |-> msg.to,
                       to |-> msg.from,
                       term |-> msg.term,
                       voteGranted |-> TRUE
                   ]})
             \/ /\ \lnot grant
                /\ vars' = [vars EXCEPT ![msg.to] = new_s_base]
                /\ network' = network \+ Bag({[
                       type |-> "MsgVoteResp",
                       from |-> msg.to,
                       to |-> msg.from,
                       term |-> msg.term,
                       voteGranted |-> FALSE
                   ]})

\* Logic for handling RequestVoteResponse (MsgVoteResp)
HandleRequestVoteResponse(msg) ==
    LET s == vars[msg.to]
    IN
    \/ /\ msg.term > s.currentTerm
       /\ vars' = [vars EXCEPT ![msg.to] = BecomeFollower(msg.to, msg.term, None)]
       /\ UNCHANGED network
    \/ /\ s.state # "StateCandidate" \/ msg.term # s.currentTerm
       /\ UNCHANGED <<vars, network>>
    \/ /\ s.state = "StateCandidate" /\ msg.term = s.currentTerm
       /\ \/ /\ msg.voteGranted
             /\ LET newVotes == s.votesGranted \cup {msg.from}
                IN \/ /\ Cardinality(newVotes) >= Quorum
                      /\ vars' = [vars EXCEPT ![msg.to] = [
                             s EXCEPT
                             !.state = "StateLeader",
                             !.leader = msg.to,
                             !.nextIndex = [p \in Servers |-> LastLogIndex(s.log) + 1],
                             !.matchIndex = [p \in Servers |-> IF p = msg.to THEN LastLogIndex(s.log) ELSE 0]
                         ]]
                      /\ UNCHANGED network
                   \/ /\ Cardinality(newVotes) < Quorum
                      /\ vars' = [vars EXCEPT ![msg.to].votesGranted = newVotes]
                      /\ UNCHANGED network
          \/ /\ \lnot msg.voteGranted
             /\ UNCHANGED <<vars, network>>

ProcessMessage ==
    \E msg \in BagToSet(network):
        /\ network' = network - Bag({msg})
        /\ \/ (msg.type = "MsgApp" /\ HandleAppendEntries(msg))
           \/ (msg.type = "MsgAppResp" /\ HandleAppendEntriesResponse(msg))
           \/ (msg.type = "MsgPreVote" /\ HandleRequestPreVote(msg))
           \/ (msg.type = "MsgPreVoteResp" /\ HandleRequestPreVoteResponse(msg))
           \/ (msg.type = "MsgVote" /\ HandleRequestVote(msg))
           \/ (msg.type = "MsgVoteResp" /\ HandleRequestVoteResponse(msg))

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
