---- MODULE redisraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Nodes, MinElectionTimeout, MaxElectionTimeout, RequestTimeout

VARIABLES
    state,
    currentTerm,
    votedFor,
    log,
    commitIndex,
    lastApplied,
    nextIndex,
    matchIndex,
    electionTimeout,
    timeoutElapsed,
    leaderId,
    messages,
    votingCfgChangeLogIdx,
    snapshotLastIdx,
    snapshotLastTerm

vars == <<state, currentTerm, votedFor, log, commitIndex, lastApplied, 
          nextIndex, matchIndex, electionTimeout, timeoutElapsed, 
          leaderId, messages, votingCfgChangeLogIdx, snapshotLastIdx, 
          snapshotLastTerm>>

NodeState == [Follower: {}, PreCandidate: {}, Candidate: {}, Leader: {}]

MessageType == {"AppendEntriesReq", "AppendEntriesResp", 
                "RequestVoteReq", "RequestVoteResp", "Timeout"}

Message == [type: MessageType, term: Nat, src: Nodes, dst: Nodes, 
            success: BOOLEAN, prevLogIdx: Nat, prevLogTerm: Nat,
            entries: Seq([term: Nat, type: {}]), leaderCommit: Nat,
            voteGranted: BOOLEAN, candidateId: Nodes, lastLogIdx: Nat,
            lastLogTerm: Nat, msgId: Nat, currentIdx: Nat]

Init ==
    /\ state = [n \in Nodes |-> Follower]
    /\ currentTerm = [n \in Nodes |-> 0]
    /\ votedFor = [n \in Nodes |-> Nil]
    /\ log = [n \in Nodes |-> <<>>]
    /\ commitIndex = [n \in Nodes |-> 0]
    /\ lastApplied = [n \in Nodes |-> 0]
    /\ nextIndex = [n \in Nodes |-> [m \in Nodes |-> 1]]
    /\ matchIndex = [n \in Nodes |-> [m \in Nodes |-> 0]]
    /\ electionTimeout = [n \in Nodes |-> MinElectionTimeout]
    /\ timeoutElapsed = [n \in Nodes |-> 0]
    /\ leaderId = [n \in Nodes |-> Nil]
    /\ messages = EmptyBag
    /\ votingCfgChangeLogIdx = [n \in Nodes |-> -1]
    /\ snapshotLastIdx = [n \in Nodes |-> 0]
    /\ snapshotLastTerm = [n \in Nodes |-> 0]

TypeInvariant ==
    /\ state \in [Nodes -> NodeState]
    /\ currentTerm \in [Nodes -> Nat]
    /\ votedFor \in [Nodes -> Nodes \cup {Nil}]
    /\ commitIndex \in [Nodes -> Nat]
    /\ lastApplied \in [Nodes -> Nat]
    /\ \A n \in Nodes: lastApplied[n] <= commitIndex[n]
    /\ electionTimeout \in [Nodes -> MinElectionTimeout..MaxElectionTimeout]

BecomeFollower(n, term, leader) ==
    /\ state[n] \in {PreCandidate, Candidate, Leader}
    /\ currentTerm' = [currentTerm EXCEPT ![n] = term]
    /\ state' = [state EXCEPT ![n] = Follower]
    /\ votedFor' = [votedFor EXCEPT ![n] = Nil]
    /\ leaderId' = [leaderId EXCEPT ![n] = leader]
    /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = 0]
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, 
                  electionTimeout, messages, votingCfgChangeLogIdx,
                  snapshotLastIdx, snapshotLastTerm>>

BecomePreCandidate(n) ==
    /\ state[n] = Follower
    /\ state' = [state EXCEPT ![n] = PreCandidate]
    /\ \A m \in Nodes: ~votedForMe(m, n)
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied,
                  nextIndex, matchIndex, electionTimeout, timeoutElapsed,
                  leaderId, messages, votingCfgChangeLogIdx, snapshotLastIdx,
                  snapshotLastTerm>>

BecomeCandidate(n) ==
    /\ state[n] \in {Follower, PreCandidate}
    /\ currentTerm' = [currentTerm EXCEPT ![n] = currentTerm[n] + 1]
    /\ state' = [state EXCEPT ![n] = Candidate]
    /\ votedFor' = [votedFor EXCEPT ![n] = n]
    /\ leaderId' = [leaderId EXCEPT ![n] = Nil]
    /\ \A m \in Nodes: ~votedForMe(m, n)
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex,
                  electionTimeout, timeoutElapsed, messages,
                  votingCfgChangeLogIdx, snapshotLastIdx, snapshotLastTerm>>

BecomeLeader(n) ==
    /\ state[n] = Candidate
    /\ IsQuorum(n, {m \in Nodes: votedForMe(m, n)})
    /\ state' = [state EXCEPT ![n] = Leader]
    /\ nextIndex' = [nextIndex EXCEPT ![n] = [m \in Nodes |-> Len(log[n]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![n] = [m \in Nodes |-> 0]]
    /\ leaderId' = [leaderId EXCEPT ![n] = n]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied,
                  electionTimeout, timeoutElapsed, messages,
                  votingCfgChangeLogIdx, snapshotLastIdx, snapshotLastTerm>>

SendRequestVote(n) ==
    /\ state[n] \in {PreCandidate, Candidate}
    /\ \E m \in Nodes \ {n}:
        LET req == [type |-> "RequestVoteReq",
                    term |-> IF state[n] = PreCandidate THEN currentTerm[n] + 1
                            ELSE currentTerm[n],
                    src |-> n,
                    dst |-> m,
                    prevote |-> (state[n] = PreCandidate),
                    candidateId |-> n,
                    lastLogIdx |-> Len(log[n]),
                    lastLogTerm |-> IF Len(log[n]) > 0 THEN log[n][Len(log[n])].term
                                   ELSE 0]
        IN messages' = messages \union {req}
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied,
                  nextIndex, matchIndex, electionTimeout, timeoutElapsed,
                  leaderId, votingCfgChangeLogIdx, snapshotLastIdx, 
                  snapshotLastTerm>>

RecvRequestVote(n, m) ==
    /\ \E msg \in messages:
        /\ msg.type = "RequestVoteReq"
        /\ msg.dst = n
        /\ msg.src = m
        /\ messages' = messages \ {msg}
        /\ \/ /\ msg.term > currentTerm[n]
              /\ BecomeFollower(n, msg.term, Nil)
           \/ /\ msg.term = currentTerm[n]
              /\ \/ /\ state[n] = Follower
                    /\ votedFor[n] \in {Nil, m}
                    /\ LogIsUpToDate(n, msg.lastLogIdx, msg.lastLogTerm)
                    /\ votedFor' = [votedFor EXCEPT ![n] = m]
                 \/ ~LogIsUpToDate(n, msg.lastLogIdx, msg.lastLogTerm)
                    \/ votedFor[n] \notin {Nil, m}
              /\ UNCHANGED state
        /\ LET resp == [type |-> "RequestVoteResp",
                        term |-> currentTerm[n],
                        src |-> n,
                        dst |-> m,
                        voteGranted |-> (votedFor[n] = m),
                        requestTerm |-> msg.term,
                        prevote |-> msg.prevote]
           IN messages' = messages' \union {resp}
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex,
                  electionTimeout, timeoutElapsed, leaderId,
                  votingCfgChangeLogIdx, snapshotLastIdx, snapshotLastTerm>>

RecvRequestVoteResponse(n, m) ==
    /\ \E msg \in messages:
        /\ msg.type = "RequestVoteResp"
        /\ msg.dst = n
        /\ msg.src = m
        /\ messages' = messages \ {msg}
        /\ \/ /\ msg.term > currentTerm[n]
              /\ BecomeFollower(n, msg.term, Nil)
           \/ /\ msg.term <= currentTerm[n]
              /\ \/ /\ msg.voteGranted
                    /\ votedForMe' = [votedForMe EXCEPT ![m][n] = TRUE]
                    /\ \E quorum \in SUBSET(Nodes):
                         /\ IsQuorum(n, quorum)
                         /\ \A node \in quorum: votedForMe(node, n)
                         /\ IF state[n] = PreCandidate 
                            THEN BecomeCandidate(n)
                            ELSE BecomeLeader(n)
                 \/ ~msg.voteGranted
                    /\ UNCHANGED state
        /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied,
                      nextIndex, matchIndex, electionTimeout, timeoutElapsed,
                      leaderId, votingCfgChangeLogIdx, snapshotLastIdx,
                      snapshotLastTerm>>

SendAppendEntries(n) ==
    /\ state[n] = Leader
    /\ \E m \in Nodes \ {n}:
        LET prevLogIdx == nextIndex[n][m] - 1
            prevLogTerm == IF prevLogIdx > 0 THEN log[n][prevLogIdx].term ELSE 0
            entries == SubSeq(log[n], nextIndex[n][m], Len(log[n]))
            req == [type |-> "AppendEntriesReq",
                    term |-> currentTerm[n],
                    src |-> n,
                    dst |-> m,
                    prevLogIdx |-> prevLogIdx,
                    prevLogTerm |-> prevLogTerm,
                    entries |-> entries,
                    leaderCommit |-> commitIndex[n],
                    msgId |-> ChooseNewMsgId(n)]
        IN messages' = messages \union {req}
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied,
                  nextIndex, matchIndex, electionTimeout, timeoutElapsed,
                  leaderId, votingCfgChangeLogIdx, snapshotLastIdx,
                  snapshotLastTerm>>

RecvAppendEntries(n, m) ==
    /\ \E msg \in messages:
        /\ msg.type = "AppendEntriesReq"
        /\ msg.dst = n
        /\ msg.src = m
        /\ messages' = messages \ {msg}
        /\ \/ /\ msg.term > currentTerm[n]
              /\ BecomeFollower(n, msg.term, msg.src)
           \/ /\ msg.term = currentTerm[n]
              /\ \/ /\ state[n] \in {Candidate, PreCandidate}
                    /\ BecomeFollower(n, currentTerm[n], msg.src)
                 \/ /\ state[n] = Follower
                    /\ leaderId' = [leaderId EXCEPT ![n] = msg.src]
                    /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = 0]
              /\ \/ /\ CheckLogMatch(n, msg.prevLogIdx, msg.prevLogTerm)
                    /\ log' = [log EXCEPT ![n] = 
                               Append(SubSeq(log[n], 1, msg.prevLogIdx),
                                      msg.entries)]
                    /\ commitIndex' = [commitIndex EXCEPT ![n] = 
                                      Min(msg.leaderCommit, Len(log'[n]))]
                    /\ success = TRUE
                 \/ ~CheckLogMatch(n, msg.prevLogIdx, msg.prevLogTerm)
                    /\ success = FALSE
        /\ LET resp == [type |-> "AppendEntriesResp",
                        term |-> currentTerm[n],
                        src |-> n,
                        dst |-> m,
                        success |-> success,
                        currentIdx |-> IF success THEN Len(log'[n]) 
                                        ELSE Len(log[n])]
           IN messages' = messages' \union {resp}
    /\ UNCHANGED <<currentTerm, votedFor, nextIndex, matchIndex,
                  electionTimeout, votingCfgChangeLogIdx, snapshotLastIdx,
                  snapshotLastTerm>>

RecvAppendEntriesResponse(n, m) ==
    /\ \E msg \in messages:
        /\ msg.type = "AppendEntriesResp"
        /\ msg.dst = n
        /\ msg.src = m
        /\ messages' = messages \ {msg}
        /\ \/ /\ msg.term > currentTerm[n]
              /\ BecomeFollower(n, msg.term, Nil)
           \/ /\ msg.term <= currentTerm[n]
              /\ \/ /\ msg.success
                    /\ matchIndex' = [matchIndex EXCEPT 
                                     ![n][m] = msg.currentIdx]
                    /\ nextIndex' = [nextIndex EXCEPT 
                                    ![n][m] = msg.currentIdx + 1]
                    /\ \E quorum \in SUBSET(Nodes):
                         /\ IsQuorum(n, quorum)
                         /\ \A node \in quorum: 
                              matchIndex[n][node] >= commitIndex[n] + 1
                         /\ commitIndex' = [commitIndex EXCEPT 
                                           ![n] = commitIndex[n] + 1]
                 \/ ~msg.success
                    /\ nextIndex' = [nextIndex EXCEPT 
                                    ![n][m] = Max(1, nextIndex[n][m] - 1)]
        /\ UNCHANGED <<state, currentTerm, votedFor, log, lastApplied,
                      electionTimeout, timeoutElapsed, leaderId,
                      votingCfgChangeLogIdx, snapshotLastIdx, snapshotLastTerm>>

ElectionTimeout(n) ==
    /\ state[n] \in {Follower, Candidate}
    /\ timeoutElapsed[n] >= electionTimeout[n]
    /\ electionTimeout' = [electionTimeout EXCEPT 
                          ![n] = ChooseRandomTimeout()]
    /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = 0]
    /\ \/ /\ state[n] = Follower
          /\ BecomePreCandidate(n)
       \/ /\ state[n] = Candidate
          /\ BecomeCandidate(n)
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied,
                  nextIndex, matchIndex, leaderId, messages,
                  votingCfgChangeLogIdx, snapshotLastIdx, snapshotLastTerm>>

HeartbeatTimeout(n) ==
    /\ state[n] = Leader
    /\ timeoutElapsed[n] >= RequestTimeout
    /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = 0]
    /\ SendAppendEntries(n)
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied,
                  nextIndex, matchIndex, electionTimeout, leaderId,
                  votingCfgChangeLogIdx, snapshotLastIdx, snapshotLastTerm>>

Next ==
    \/ \E n \in Nodes: ElectionTimeout(n)
    \/ \E n \in Nodes: HeartbeatTimeout(n)
    \/ \E n \in Nodes: SendRequestVote(n)
    \/ \E n, m \in Nodes: RecvRequestVote(n, m)
    \/ \E n, m \in Nodes: RecvRequestVoteResponse(n, m)
    \/ \E n \in Nodes: SendAppendEntries(n)
    \/ \E n, m \in Nodes: RecvAppendEntries(n, m)
    \/ \E n, m \in Nodes: RecvAppendEntriesResponse(n, m)

IsQuorum(n, set) ==
    LET votingNodes == {m \in Nodes: IsVotingMember(m)}
    IN Cardinality(set \cap votingNodes) > Cardinality(votingNodes) \div 2

LogIsUpToDate(n, lastLogIdx, lastLogTerm) ==
    \/ lastLogTerm > LastLogTerm(n)
    \/ lastLogTerm = LastLogTerm(n) /\ lastLogIdx >= Len(log[n])

CheckLogMatch(n, prevLogIdx, prevLogTerm) ==
    \/ prevLogIdx = 0
    \/ prevLogIdx <= Len(log[n]) /\ log[n][prevLogIdx].term = prevLogTerm

LastLogTerm(n) ==
    IF Len(log[n]) > 0 THEN log[n][Len(log[n])].term ELSE 0

ChooseRandomTimeout() ==
    CHOOSE t \in MinElectionTimeout..MaxElectionTimeout: TRUE

ChooseNewMsgId(n) ==
    CHOOSE id \in Nat: TRUE

IsVotingMember(n) == TRUE

votedForMe(m, n) == (votedFor[m] = n)

Nil == CHOOSE nil: nil \notin Nodes

====