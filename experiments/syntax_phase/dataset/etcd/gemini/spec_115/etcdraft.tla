---- MODULE etcdraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Server, Value, Nil

ASSUME Server \subseteq Nat
ASSUME Nil \notin Server

NodeStates == {"StateFollower", "StateCandidate", "StatePreCandidate", "StateLeader"}
MessageTypes == {"MsgHup", "MsgProp", "MsgApp", "MsgAppResp", "MsgVote", "MsgVoteResp", "MsgPreVote", "MsgPreVoteResp"}

(* Timers *)
ElectionTimeoutMin == 5
ElectionTimeoutMax == 10
HeartbeatTimeout == 2

(* Log entry is a record with a term and a value *)
LogEntry(t, v) == [term |-> t, value |-> v]

(* Message is a record representing a network message *)
Message(typ, src, dst, trm, pIdx, pTrm, ents, cmt, rej) ==
    [type |-> typ, from |-> src, to |-> dst, term |-> trm,
     prevLogIndex |-> pIdx, prevLogTerm |-> pTrm,
     entries |-> ents, leaderCommit |-> cmt, reject |-> rej]

Quorum == (Cardinality(Server) \div 2) + 1

VARIABLES
    network,
    vars

vars_type == [
    state: NodeStates,
    currentTerm: Nat,
    votedFor: Server \cup {Nil},
    log: Seq(RECORD),
    commitIndex: Nat,
    leaderId: Server \cup {Nil},
    votesGranted: SUBSET Server,
    nextIndex: [Server -> Nat],
    matchIndex: [Server -> Nat],
    electionTimer: 0..ElectionTimeoutMax,
    heartbeatTimer: 0..HeartbeatTimeout
]

TypeOK ==
    /\ network \in Bags(DOMAIN Message(
        MessageTypes, Server, Server, Nat, Nat, Nat, Seq(RECORD), Nat, BOOLEAN
    ))
    /\ vars \in [Server -> vars_type]

-----------------------------------------------------------------------------

LastLogIndex(log) == Len(log)
LastLogTerm(log) == IF Len(log) > 0 THEN log[Len(log)].term ELSE 0

IsUpToDate(logA, logB) ==
    LET lastTermA == LastLogTerm(logA)
        lastIndexA == LastLogIndex(logA)
        lastTermB == LastLogTerm(logB)
        lastIndexB == LastLogIndex(logB)
    IN \/ lastTermA > lastTermB
       \/ (lastTermA = lastTermB /\ lastIndexA >= lastIndexB)

BecomeFollower(s, term, lead) ==
    s EXCEPT !.state = "StateFollower",
             !.currentTerm = term,
             !.votedFor = Nil,
             !.leaderId = lead,
             !.electionTimer = 0

-----------------------------------------------------------------------------

Init ==
    /\ network = EmptyBag
    /\ vars = [i \in Server |->
        [state |-> "StateFollower",
         currentTerm |-> 0,
         votedFor |-> Nil,
         log |-> << >>,
         commitIndex |-> 0,
         leaderId |-> Nil,
         votesGranted |-> {},
         nextIndex |-> [j \in Server |-> 1],
         matchIndex |-> [j \in Server |-> 0],
         electionTimer |-> 0,
         heartbeatTimer |-> 0
        ]
    ]

-----------------------------------------------------------------------------
(* Actions that send messages *)

ClientRequest(s, v) ==
    /\ network' = network \+ Bag({Message("MsgProp", Nil, s, 0, 0, 0, <<[value |-> v]>>, 0, FALSE)})
    /\ UNCHANGED vars

Timeout(s) ==
    LET self == vars[s]
    IN /\ self.state \in {"StateFollower", "StateCandidate", "StatePreCandidate"}
       /\ self.electionTimer >= ElectionTimeoutMin
       /\ network' = network \+ Bag({Message("MsgHup", s, s, 0, 0, 0, << >>, 0, FALSE)})
       /\ UNCHANGED vars

LeaderHeartbeat(s) ==
    LET self == vars[s]
    IN /\ self.state = "StateLeader"
       /\ self.heartbeatTimer >= HeartbeatTimeout
       /\ LET
            SendHeartbeat(peer) ==
                LET prevIdx == self.nextIndex[peer] - 1
                    prevTerm == IF prevIdx > 0 THEN self.log[prevIdx].term ELSE 0
                IN Message("MsgApp", s, peer, self.currentTerm, prevIdx, prevTerm, << >>, self.commitIndex, FALSE)
          IN network' = network \+ Bag({SendHeartbeat(p) : p \in Server \ {s}})
       /\ vars' = vars EXCEPT ![s].heartbeatTimer = 0
       
-----------------------------------------------------------------------------
(* Actions that handle received messages *)

HandleHup(s) ==
    LET self == vars[s]
    IN /\ self.state \in {"StateFollower", "StateCandidate", "StatePreCandidate"}
       /\ LET
            \* Pre-Vote phase
            preVoteTerm == self.currentTerm + 1
            preVoteMsgs == {Message("MsgPreVote", s, p, preVoteTerm, LastLogIndex(self.log), LastLogTerm(self.log), << >>, 0, FALSE) : p \in Server \ {s}}
            newState == self EXCEPT !.state = "StatePreCandidate",
                                   !.leaderId = Nil,
                                   !.votesGranted = {s},
                                   !.electionTimer = 0
          IN /\ network' = network \+ Bag(preVoteMsgs)
             /\ vars' = vars EXCEPT ![s] = newState

HandleRequestPreVote(s, m) ==
    LET self == vars[s]
    IN /\ m.term > self.currentTerm
       /\ IsUpToDate([term |-> m.prevLogTerm, index |-> m.prevLogIndex], [term |-> LastLogTerm(self.log), index |-> LastLogIndex(self.log)])
       /\ LET resp == Message("MsgPreVoteResp", s, m.from, m.term, 0, 0, << >>, 0, FALSE)
          IN network' = network \+ Bag({resp})
       /\ UNCHANGED vars

HandleRequestPreVoteRejection(s, m) ==
    LET self == vars[s]
    IN /\ \/ m.term <= self.currentTerm
          \/ ~IsUpToDate([term |-> m.prevLogTerm, index |-> m.prevLogIndex], [term |-> LastLogTerm(self.log), index |-> LastLogIndex(self.log)])
       /\ LET resp == Message("MsgPreVoteResp", s, m.from, self.currentTerm, 0, 0, << >>, 0, TRUE)
          IN network' = network \+ Bag({resp})
       /\ UNCHANGED vars

HandleRequestPreVoteResponse(s, m) ==
    LET self == vars[s]
    IN /\ self.state = "StatePreCandidate"
       /\ m.term = self.currentTerm + 1
       /\ ~m.reject
       /\ LET newVotes == self.votesGranted \cup {m.from}
          IN IF Cardinality(newVotes) >= Quorum
             THEN (* Start real election *)
                LET newTerm == self.currentTerm + 1
                    voteMsgs == {Message("MsgVote", s, p, newTerm, LastLogIndex(self.log), LastLogTerm(self.log), << >>, 0, FALSE) : p \in Server \ {s}}
                    newState == self EXCEPT !.state = "StateCandidate",
                                           !.currentTerm = newTerm,
                                           !.votedFor = s,
                                           !.votesGranted = {s},
                                           !.electionTimer = 0
                IN /\ network' = network \+ Bag(voteMsgs)
                   /\ vars' = vars EXCEPT ![s] = newState
             ELSE (* Not a quorum yet, just record vote *)
                /\ vars' = vars EXCEPT ![s].votesGranted = newVotes
                /\ UNCHANGED network

HandleRequestVote(s, m) ==
    LET self == vars[s]
    IN /\ m.term = self.currentTerm
       /\ (self.votedFor = Nil \/ self.votedFor = m.from)
       /\ IsUpToDate([term |-> m.prevLogTerm, index |-> m.prevLogIndex], [term |-> LastLogTerm(self.log), index |-> LastLogIndex(self.log)])
       /\ LET resp == Message("MsgVoteResp", s, m.from, self.currentTerm, 0, 0, << >>, 0, FALSE)
          IN /\ network' = network \+ Bag({resp})
             /\ vars' = vars EXCEPT ![s].votedFor = m.from

HandleRequestVoteRejection(s, m) ==
    LET self == vars[s]
    IN /\ \/ m.term /= self.currentTerm
          \/ (self.votedFor /= Nil /\ self.votedFor /= m.from)
          \/ ~IsUpToDate([term |-> m.prevLogTerm, index |-> m.prevLogIndex], [term |-> LastLogTerm(self.log), index |-> LastLogIndex(self.log)])
       /\ LET resp == Message("MsgVoteResp", s, m.from, self.currentTerm, 0, 0, << >>, 0, TRUE)
          IN network' = network \+ Bag({resp})
       /\ UNCHANGED vars

HandleRequestVoteResponse(s, m) ==
    LET self == vars[s]
    IN /\ self.state = "StateCandidate"
       /\ m.term = self.currentTerm
       /\ ~m.reject
       /\ LET newVotes == self.votesGranted \cup {m.from}
          IN IF Cardinality(newVotes) >= Quorum
             THEN (* Become Leader *)
                LET
                    newState == self EXCEPT !.state = "StateLeader",
                                           !.leaderId = s,
                                           !.nextIndex = [p \in Server |-> LastLogIndex(self.log) + 1],
                                           !.matchIndex = [p \in Server |-> IF p = s THEN LastLogIndex(self.log) ELSE 0],
                                           !.heartbeatTimer = 0
                    \* Append a no-op entry for the new term
                    newLog == Append(self.log, LogEntry(self.currentTerm, "NoOp"))
                    updatedState == newState EXCEPT !.log = newLog,
                                                   !.matchIndex[s] = LastLogIndex(newLog)
                    initialAppends == {
                        LET prevIdx == updatedState.nextIndex[p] - 1
                            prevTerm == IF prevIdx > 0 THEN updatedState.log[prevIdx].term ELSE 0
                        IN Message("MsgApp", s, p, self.currentTerm, prevIdx, prevTerm, SubSeq(updatedState.log, updatedState.nextIndex[p], LastLogIndex(updatedState.log)), updatedState.commitIndex, FALSE)
                        : p \in Server \ {s}
                    }
                IN /\ network' = network \+ Bag(initialAppends)
                   /\ vars' = vars EXCEPT ![s] = updatedState
             ELSE (* Not a quorum yet, just record vote *)
                /\ vars' = vars EXCEPT ![s].votesGranted = newVotes
                /\ UNCHANGED network

HandleAppendEntries(s, m) ==
    LET self == vars[s]
    IN /\ self.state \in {"StateFollower", "StateCandidate", "StatePreCandidate"}
       /\ m.term = self.currentTerm
       /\ self.leaderId = m.from
       /\ LET
            logOK == \/ m.prevLogIndex = 0
                     \/ (/\ m.prevLogIndex <= LastLogIndex(self.log)
                         /\ self.log[m.prevLogIndex].term = m.prevLogTerm)
          IN IF logOK
             THEN
                LET
                    existingEntries == SubSeq(self.log, 1, m.prevLogIndex)
                    newLog == existingEntries \o m.entries
                    newCommitIndex == IF m.leaderCommit > self.commitIndex
                                      THEN Min({m.leaderCommit, LastLogIndex(newLog)})
                                      ELSE self.commitIndex
                    newState == self EXCEPT !.log = newLog,
                                           !.commitIndex = newCommitIndex,
                                           !.electionTimer = 0
                    resp == Message("MsgAppResp", s, m.from, self.currentTerm, LastLogIndex(newLog), 0, << >>, 0, FALSE)
                IN /\ network' = network \+ Bag({resp})
                   /\ vars' = vars EXCEPT ![s] = newState
             ELSE
                LET resp == Message("MsgAppResp", s, m.from, self.currentTerm, m.prevLogIndex, 0, << >>, 0, TRUE)
                IN /\ network' = network \+ Bag({resp})
                   /\ UNCHANGED vars

HandleAppendEntriesResponse(s, m) ==
    LET self == vars[s]
    IN /\ self.state = "StateLeader"
       /\ m.term = self.currentTerm
       /\ IF m.reject
          THEN (* Follower rejected, decrement nextIndex and retry *)
            LET newNextIndex == self.nextIndex[m.from] - 1
                newState == self EXCEPT !.nextIndex[m.from] = IF newNextIndex > 0 THEN newNextIndex ELSE 1
                prevIdx == newState.nextIndex[m.from] - 1
                prevTerm == IF prevIdx > 0 THEN self.log[prevIdx].term ELSE 0
                entriesToSend == SubSeq(self.log, newState.nextIndex[m.from], LastLogIndex(self.log))
                retryMsg == Message("MsgApp", s, m.from, self.currentTerm, prevIdx, prevTerm, entriesToSend, self.commitIndex, FALSE)
            IN /\ network' = network \+ Bag({retryMsg})
               /\ vars' = vars EXCEPT ![s] = newState
          ELSE (* Follower accepted *)
            LET newMatchIndex == m.prevLogIndex
                newNextIndex == newMatchIndex + 1
                newState == self EXCEPT !.matchIndex[m.from] = newMatchIndex,
                                       !.nextIndex[m.from] = newNextIndex
                \* Try to advance commit index
                commitCand == {i \in (self.commitIndex + 1)..LastLogIndex(self.log) |
                                /\ self.log[i].term = self.currentTerm
                                /\ Cardinality({p \in Server | newState.matchIndex[p] >= i}) >= Quorum}
                newCommitIndex == IF commitCand = {} THEN self.commitIndex ELSE Max(commitCand)
            IN /\ vars' = vars EXCEPT ![s] = newState, ![s].commitIndex = newCommitIndex
               /\ UNCHANGED network

HandleProposal(s, m) ==
    LET self == vars[s]
    IN /\ self.state = "StateLeader"
       /\ LET
            newEntry == LogEntry(self.currentTerm, m.entries[1].value)
            newLog == Append(self.log, newEntry)
            newState == self EXCEPT !.log = newLog,
                                   !.matchIndex[s] = LastLogIndex(newLog)
            \* Broadcast new entry
            appMsgs == {
                LET prevIdx == newState.nextIndex[p] - 1
                    prevTerm == IF prevIdx > 0 THEN newState.log[prevIdx].term ELSE 0
                IN Message("MsgApp", s, p, self.currentTerm, prevIdx, prevTerm, SubSeq(newState.log, newState.nextIndex[p], LastLogIndex(newState.log)), self.commitIndex, FALSE)
                : p \in Server \ {s}
            }
          IN /\ network' = network \+ Bag(appMsgs)
             /\ vars' = vars EXCEPT ![s] = newState

TermStepDown(s, m) ==
    LET self == vars[s]
    IN /\ m.term > self.currentTerm
       /\ LET newState == BecomeFollower(self, m.term, IF m.type \in {"MsgApp", "MsgHeartbeat"} THEN m.from ELSE Nil)
          IN /\ vars' = vars EXCEPT ![s] = newState
             /\ UNCHANGED network

Receive(s) ==
    \E m \in BagToSet(network):
        LET self == vars[s]
        IN /\ m.to = s
           /\ network' = network - Bag({m})
           /\ IF m.term > self.currentTerm
              THEN TermStepDown(s, m)
              ELSE CASE m.type = "MsgHup" -> HandleHup(s)
                   [] m.type = "MsgProp" -> HandleProposal(s, m)
                   [] m.type = "MsgApp" -> HandleAppendEntries(s, m)
                   [] m.type = "MsgAppResp" -> HandleAppendEntriesResponse(s, m)
                   [] m.type = "MsgPreVote" -> \/ HandleRequestPreVote(s, m) \/ HandleRequestPreVoteRejection(s, m)
                   [] m.type = "MsgPreVoteResp" -> HandleRequestPreVoteResponse(s, m)
                   [] m.type = "MsgVote" -> \/ HandleRequestVote(s, m) \/ HandleRequestVoteRejection(s, m)
                   [] m.type = "MsgVoteResp" -> HandleRequestVoteResponse(s, m)
                   [] OTHER -> UNCHANGED <<vars, network>>

DropMessage ==
    \E m \in BagToSet(network):
        /\ network' = network - Bag({m})
        /\ UNCHANGED vars

Tick ==
    /\ vars' = [i \in Server |->
        LET s == vars[i]
        IN s EXCEPT !.electionTimer = IF s.state /= "StateLeader" THEN Min({s.electionTimer + 1, ElectionTimeoutMax}) ELSE s.electionTimer,
                    !.heartbeatTimer = IF s.state = "StateLeader" THEN Min({s.heartbeatTimer + 1, HeartbeatTimeout}) ELSE s.heartbeatTimer
      ]
    /\ UNCHANGED network

-----------------------------------------------------------------------------

Next ==
    \/ \E s \in Server, v \in Value: ClientRequest(s, v)
    \/ \E s \in Server: Timeout(s)
    \/ \E s \in Server: LeaderHeartbeat(s)
    \/ \E s \in Server: Receive(s)
    \/ DropMessage
    \/ Tick

Spec == Init /\ [][Next]_<<vars, network>>

=============================================================================
