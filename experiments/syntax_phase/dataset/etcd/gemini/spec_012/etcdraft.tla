---- MODULE etcdraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS
    Servers,
    Commands,
    ElectionTimeout,
    HeartbeatInterval

ASSUME
    /\ IsFiniteSet(Servers)
    /\ Cardinality(Servers) % 2 = 1
    /\ IsFiniteSet(Commands)
    /\ ElectionTimeout > HeartbeatInterval
    /\ HeartbeatInterval > 0

Nil == "Nil"
AllServers == Servers \union {Nil}

LogEntry(t, c) == [term |-> t, command |-> c]

Message(ty, to, from, te, lte, lidx, ents, cidx, rej) ==
    [type |-> ty, to |-> to, from |-> from, term |-> te,
     logTerm |-> lte, logIndex |-> lidx, entries |-> ents,
     commit |-> cidx, reject |-> rej]

VARIABLES
    state,
    currentTerm,
    votedFor,
    log,
    commitIndex,
    leader,
    electionElapsed,
    heartbeatElapsed,
    votesGranted,
    matchIndex,
    nextIndex,
    messages

vars == <<state, currentTerm, votedFor, log, commitIndex, leader,
          electionElapsed, heartbeatElapsed, votesGranted, matchIndex, nextIndex, messages>>

Quorum == (Cardinality(Servers) \div 2) + 1

LastLogIndex(s) == Len(log[s])
LastLogTerm(s) == IF LastLogIndex(s) = 0 THEN 0 ELSE log[s][LastLogIndex(s)].term

isUpToDate(candidateTerm, candidateIndex, myTerm, myIndex) ==
    \/ candidateTerm > myTerm
    \/ (candidateTerm = myTerm /\ candidateIndex >= myIndex)

Init ==
    /\ state = [s \in Servers |-> "Follower"]
    /\ currentTerm = [s \in Servers |-> 0]
    /\ votedFor = [s \in Servers |-> Nil]
    /\ log = [s \in Servers |-> <<>>]
    /\ commitIndex = [s \in Servers |-> 0]
    /\ leader = [s \in Servers |-> Nil]
    /\ electionElapsed = [s \in Servers |-> 0]
    /\ heartbeatElapsed = [s \in Servers |-> 0]
    /\ votesGranted = [s \in Servers |-> {}]
    /\ matchIndex = [s \in Servers |-> [t \in Servers |-> 0]]
    /\ nextIndex = [s \in Servers |-> [t \in Servers |-> 1]]
    /\ messages = EmptyBag

Tick(s) ==
    /\ state[s] \in {"Follower", "PreCandidate", "Candidate"}
    /\ electionElapsed' = [electionElapsed EXCEPT ![s] = @ + 1]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader,
                   heartbeatElapsed, votesGranted, matchIndex, nextIndex, messages>>

LeaderTick(s) ==
    /\ state[s] = "Leader"
    /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![s] = @ + 1]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader,
                   electionElapsed, votesGranted, matchIndex, nextIndex, messages>>

Timeout(s) ==
    /\ state[s] \in {"Follower", "PreCandidate", "Candidate"}
    /\ electionElapsed[s] >= ElectionTimeout
    /\ state' = [state EXCEPT ![s] = "PreCandidate"]
    /\ electionElapsed' = [electionElapsed EXCEPT ![s] = 0]
    /\ leader' = [leader EXCEPT ![s] = Nil]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {}]
    /\ LET nextTerm == currentTerm[s] + 1
           lastIdx == LastLogIndex(s)
           lastTerm == LastLogTerm(s)
           newMsgs == { Message("MsgPreVote", peer, s, nextTerm, lastTerm, lastIdx, <<>>, 0, FALSE) : peer \in Servers \ {s} }
       IN messages' = messages \+ Bag(newMsgs)
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, heartbeatElapsed, matchIndex, nextIndex>>

StepDown(s, m) ==
    /\ m.term > currentTerm[s]
    /\ state' = [state EXCEPT ![s] = "Follower"]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = m.term]
    /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
    /\ leader' = [leader EXCEPT ![s] = IF m.type \in {"MsgApp", "MsgHeartbeat"} THEN m.from ELSE Nil]
    /\ UNCHANGED <<log, commitIndex, electionElapsed, heartbeatElapsed, votesGranted, matchIndex, nextIndex>>

HandlePreVoteRequest(s, m) ==
    /\ m.type = "MsgPreVote"
    /\ LET myLastTerm == LastLogTerm(s)
           myLastIndex == LastLogIndex(s)
           grantVote == /\ m.term > currentTerm[s]
                        /\ isUpToDate(m.logTerm, m.logIndex, myLastTerm, myLastIndex)
       IN messages' = (messages \- Bag({m}))
                     \+ IF grantVote
                        THEN Bag({Message("MsgPreVoteResp", m.from, s, m.term, 0, 0, <<>>, 0, FALSE)})
                        ELSE Bag({Message("MsgPreVoteResp", m.from, s, currentTerm[s], 0, 0, <<>>, 0, TRUE)})
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader,
                   electionElapsed, heartbeatElapsed, votesGranted, matchIndex, nextIndex>>

HandlePreVoteResponse(s, m) ==
    /\ m.type = "MsgPreVoteResp"
    /\ state[s] = "PreCandidate"
    /\ m.term > currentTerm[s]
    /\ IF m.reject
       THEN /\ state' = [state EXCEPT ![s] = "Follower"]
            /\ currentTerm' = [currentTerm EXCEPT ![s] = m.term]
            /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
            /\ messages' = messages \- Bag({m})
            /\ UNCHANGED <<log, commitIndex, leader, electionElapsed, heartbeatElapsed, votesGranted, matchIndex, nextIndex>>
       ELSE /\ LET newVotes == votesGranted[s] \union {m.from}
              IN IF Cardinality(newVotes \union {s}) >= Quorum
                 THEN (* Become Candidate *)
                      /\ state' = [state EXCEPT ![s] = "Candidate"]
                      /\ currentTerm' = [currentTerm EXCEPT ![s] = m.term]
                      /\ votedFor' = [votedFor EXCEPT ![s] = s]
                      /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
                      /\ electionElapsed' = [electionElapsed EXCEPT ![s] = 0]
                      /\ LET lastIdx == LastLogIndex(s)
                             lastTerm == LastLogTerm(s)
                             newMsgs == { Message("MsgVote", peer, s, m.term, lastTerm, lastIdx, <<>>, 0, FALSE) : peer \in Servers \ {s} }
                         IN messages' = (messages \- Bag({m})) \+ Bag(newMsgs)
                      /\ UNCHANGED <<log, commitIndex, leader, heartbeatElapsed, matchIndex, nextIndex>>
                 ELSE (* Not enough votes yet, just record the vote *)
                      /\ votesGranted' = [votesGranted EXCEPT ![s] = newVotes]
                      /\ messages' = messages \- Bag({m})
                      /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader,
                                     electionElapsed, heartbeatElapsed, matchIndex, nextIndex>>

HandleVoteRequest(s, m) ==
    /\ m.type = "MsgVote"
    /\ m.term = currentTerm[s]
    /\ LET myLastTerm == LastLogTerm(s)
           myLastIndex == LastLogIndex(s)
           grantVote == /\ (votedFor[s] = Nil \/ votedFor[s] = m.from)
                        /\ isUpToDate(m.logTerm, m.logIndex, myLastTerm, myLastIndex)
       IN /\ messages' = (messages \- Bag({m}))
                        \+ IF grantVote
                           THEN Bag({Message("MsgVoteResp", m.from, s, m.term, 0, 0, <<>>, 0, FALSE)})
                           ELSE Bag({Message("MsgVoteResp", m.from, s, currentTerm[s], 0, 0, <<>>, 0, TRUE)})
          /\ IF grantVote
             THEN /\ votedFor' = [votedFor EXCEPT ![s] = m.from]
                  /\ electionElapsed' = [electionElapsed EXCEPT ![s] = 0]
                  /\ UNCHANGED <<state, currentTerm, log, commitIndex, leader, heartbeatElapsed, votesGranted, matchIndex, nextIndex>>
             ELSE UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader,
                              electionElapsed, heartbeatElapsed, votesGranted, matchIndex, nextIndex>>

HandleVoteResponse(s, m) ==
    /\ m.type = "MsgVoteResp"
    /\ state[s] = "Candidate"
    /\ m.term = currentTerm[s]
    /\ IF m.reject
       THEN /\ messages' = messages \- Bag({m})
            /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader,
                           electionElapsed, heartbeatElapsed, votesGranted, matchIndex, nextIndex>>
       ELSE /\ LET newVotes == votesGranted[s] \union {m.from}
              IN IF Cardinality(newVotes) >= Quorum /\ state[s] = "Candidate"
                 THEN (* Become Leader *)
                      /\ state' = [state EXCEPT ![s] = "Leader"]
                      /\ leader' = [leader EXCEPT ![s] = s]
                      /\ nextIndex' = [nextIndex EXCEPT ![s] = [p \in Servers |-> LastLogIndex(s) + 1]]
                      /\ matchIndex' = [matchIndex EXCEPT ![s] = [p \in Servers |-> 0]]
                      /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![s] = 0]
                      /\ LET lastIdx == LastLogIndex(s)
                             lastTerm == LastLogTerm(s)
                             newMsgs == { Message("MsgApp", peer, s, currentTerm[s], lastTerm, lastIdx, <<>>, commitIndex[s], FALSE) : peer \in Servers \ {s} }
                         IN messages' = (messages \- Bag({m})) \+ Bag(newMsgs)
                      /\ votesGranted' = [votesGranted EXCEPT ![s] = newVotes]
                      /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, electionElapsed>>
                 ELSE (* Not enough votes yet *)
                      /\ votesGranted' = [votesGranted EXCEPT ![s] = newVotes]
                      /\ messages' = messages \- Bag({m})
                      /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader,
                                     electionElapsed, heartbeatElapsed, matchIndex, nextIndex>>

HandleAppendEntriesRequest(s, m) ==
    /\ m.type = "MsgApp"
    /\ IF m.term < currentTerm[s]
       THEN /\ messages' = (messages \- Bag({m})) \+ Bag({Message("MsgAppResp", m.from, s, currentTerm[s], 0, 0, <<>>, 0, TRUE)})
            /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader,
                           electionElapsed, heartbeatElapsed, votesGranted, matchIndex, nextIndex>>
       ELSE /\ state' = [state EXCEPT ![s] = "Follower"]
            /\ leader' = [leader EXCEPT ![s] = m.from]
            /\ electionElapsed' = [electionElapsed EXCEPT ![s] = 0]
            /\ LET logOK == /\ m.logIndex <= LastLogIndex(s)
                          /\ (m.logIndex = 0 \/ log[s][m.logIndex].term = m.logTerm)
               IN IF logOK
                  THEN /\ log' = [log EXCEPT ![s] = SubSeq(log[s], 1, m.logIndex) \o m.entries]
                       /\ LET newLastIndex = m.logIndex + Len(m.entries)
                       IN commitIndex' = [commitIndex EXCEPT ![s] = max(commitIndex[s], min(m.commit, newLastIndex))]
                       /\ messages' = (messages \- Bag({m})) \+ Bag({Message("MsgAppResp", m.from, s, currentTerm[s], 0, newLastIndex, <<>>, 0, FALSE)})
                       /\ UNCHANGED <<currentTerm, votedFor, heartbeatElapsed, votesGranted, matchIndex, nextIndex>>
                  ELSE /\ messages' = (messages \- Bag({m})) \+ Bag({Message("MsgAppResp", m.from, s, currentTerm[s], 0, 0, <<>>, 0, TRUE)})
                       /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, heartbeatElapsed, votesGranted, matchIndex, nextIndex>>

HandleAppendEntriesResponse(s, m) ==
    /\ m.type = "MsgAppResp"
    /\ state[s] = "Leader"
    /\ m.term = currentTerm[s]
    /\ messages' = messages \- Bag({m})
    /\ IF m.reject
       THEN /\ nextIndex' = [nextIndex EXCEPT ![s] = [nextIndex[s] EXCEPT ![m.from] = max(1, @ - 1)]]
            /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader,
                           electionElapsed, heartbeatElapsed, votesGranted, matchIndex>>
       ELSE /\ matchIndex' = [matchIndex EXCEPT ![s] = [matchIndex[s] EXCEPT ![m.from] = m.logIndex]]
            /\ nextIndex' = [nextIndex EXCEPT ![s] = [nextIndex[s] EXCEPT ![m.from] = m.logIndex + 1]]
            /\ LET mi == [matchIndex[s] EXCEPT ![m.from] = m.logIndex]
                   fullMatchIndex == [p \in Servers |-> IF p=s THEN LastLogIndex(s) ELSE mi[p]]
                   newCommitIndexSet ==
                     { N \in commitIndex[s]+1 .. LastLogIndex(s) |
                         /\ log[s][N].term = currentTerm[s]
                         /\ Cardinality({p \in Servers | fullMatchIndex[p] >= N}) >= Quorum }
               IN commitIndex' = IF newCommitIndexSet = {}
                                 THEN commitIndex
                                 ELSE [commitIndex EXCEPT ![s] = Max(newCommitIndexSet)]
            /\ UNCHANGED <<state, currentTerm, votedFor, log, leader,
                           electionElapsed, heartbeatElapsed, votesGranted>>

LeaderSendHeartbeat(s) ==
    /\ state[s] = "Leader"
    /\ heartbeatElapsed[s] >= HeartbeatInterval
    /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![s] = 0]
    /\ LET newMsgs == { LET prevIdx == nextIndex[s][peer] - 1
                           prevTerm == IF prevIdx > 0 THEN log[s][prevIdx].term ELSE 0
                       IN Message("MsgApp", peer, s, currentTerm[s], prevTerm, prevIdx, <<>>, commitIndex[s], FALSE)
                       : peer \in Servers \ {s} }
    IN messages' = messages \+ Bag(newMsgs)
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader,
                   electionElapsed, votesGranted, matchIndex, nextIndex>>

ClientRequest(s, cmd) ==
    /\ state[s] = "Leader"
    /\ LET newEntry == LogEntry(currentTerm[s], cmd)
           newLog == Append(log[s], newEntry)
       IN /\ log' = [log EXCEPT ![s] = newLog]
          /\ matchIndex' = [matchIndex EXCEPT ![s] = [matchIndex[s] EXCEPT ![s] = Len(newLog)]]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, leader,
                   electionElapsed, heartbeatElapsed, votesGranted, nextIndex, messages>>

LeaderReplicateLog(s, peer) ==
    /\ state[s] = "Leader"
    /\ peer \in Servers \ {s}
    /\ LastLogIndex(s) >= nextIndex[s][peer]
    /\ LET prevIdx == nextIndex[s][peer] - 1
           prevTerm == IF prevIdx > 0 THEN log[s][prevIdx].term ELSE 0
           entriesToSend == SubSeq(log[s], nextIndex[s][peer], LastLogIndex(s))
       IN messages' = messages \+ Bag({Message("MsgApp", peer, s, currentTerm[s], prevTerm, prevIdx, entriesToSend, commitIndex[s], FALSE)})
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader,
                   electionElapsed, heartbeatElapsed, votesGranted, matchIndex, nextIndex>>

Receive(s, m) ==
    /\ m.to = s
    /\ IF m.term > currentTerm[s]
       THEN StepDown(s, m) /\ messages' = messages \- Bag({m})
       ELSE CASE m.type = "MsgPreVote" -> HandlePreVoteRequest(s, m)
              [] m.type = "MsgVote" -> HandleVoteRequest(s, m)
              [] m.term = currentTerm[s] /\ m.type = "MsgPreVoteResp" -> HandlePreVoteResponse(s, m)
              [] m.term = currentTerm[s] /\ m.type = "MsgVoteResp" -> HandleVoteResponse(s, m)
              [] m.type = "MsgApp" -> HandleAppendEntriesRequest(s, m)
              [] m.term = currentTerm[s] /\ m.type = "MsgAppResp" -> HandleAppendEntriesResponse(s, m)
              [] OTHER -> messages' = messages \- Bag({m})
                         /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader,
                                        electionElapsed, heartbeatElapsed, votesGranted, matchIndex, nextIndex>>

DropMessage(m) ==
    /\ messages' = messages \- Bag({m})
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader,
                   electionElapsed, heartbeatElapsed, votesGranted, matchIndex, nextIndex>>

Next ==
    \/ \E s \in Servers:
        \/ Tick(s)
        \/ LeaderTick(s)
        \/ Timeout(s)
        \/ LeaderSendHeartbeat(s)
        \/ \E cmd \in Commands: ClientRequest(s, cmd)
        \/ \E peer \in Servers \ {s}: LeaderReplicateLog(s, peer)
    \/ \E s \in Servers, m \in BagToSet(messages): Receive(s, m)
    \/ \E m \in BagToSet(messages): DropMessage(m)

Spec == Init /\ [][Next]_vars

====
