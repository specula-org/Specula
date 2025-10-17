---- MODULE etcdraft ----
EXTENDS TLC, Sequences, Naturals, FiniteSets, Bags

CONSTANTS
    Nodes,
    ClientValues,
    DefaultVote,
    ElectionTimeout,
    HeartbeatInterval

ASSUME
    /\ Nodes = { "n1", "n2", "n3" }
    /\ ClientValues = { "v1", "v2" }
    /\ DefaultVote \notin Nodes
    /\ ElectionTimeout = 5
    /\ HeartbeatInterval = 2

VARIABLES
    state,
    currentTerm,
    votedFor,
    log,
    commitIndex,
    electionTimer,
    heartbeatTimer,
    network,
    \* Leader-specific state
    nextIndex,
    matchIndex

vars == << state, currentTerm, votedFor, log, commitIndex, electionTimer, heartbeatTimer, network, nextIndex, matchIndex >>

Quorum == (Cardinality(Nodes) \div 2) + 1

LastLogIndex(l) == Len(l)
LastLogTerm(l) == IF Len(l) > 0 THEN l[Len(l)].term ELSE 0

IsUpToDate(nodeLog, candIndex, candTerm) ==
    LET lastTerm == LastLogTerm(nodeLog)
        lastIndex == LastLogIndex(nodeLog)
    IN (candTerm > lastTerm) \/ (candTerm = lastTerm /\ candIndex >= lastIndex)

TypeOK ==
    /\ state \in [Nodes -> {"Follower", "PreCandidate", "Candidate", "Leader"}]
    /\ currentTerm \in [Nodes -> Nat]
    /\ votedFor \in [Nodes -> Nodes \cup {DefaultVote}]
    /\ \A n \in Nodes: log[n] \in Seq([term: Nat, value: ClientValues])
    /\ commitIndex \in [Nodes -> Nat]
    /\ electionTimer \in [Nodes -> 0..ElectionTimeout]
    /\ heartbeatTimer \in [Nodes -> [Nodes -> 0..HeartbeatInterval]]
    /\ nextIndex \in [Nodes -> [Nodes -> Nat]]
    /\ matchIndex \in [Nodes -> [Nodes -> Nat]]

Init ==
    /\ state = [n \in Nodes |-> "Follower"]
    /\ currentTerm = [n \in Nodes |-> 0]
    /\ votedFor = [n \in Nodes |-> DefaultVote]
    /\ log = [n \in Nodes |-> << >>]
    /\ commitIndex = [n \in Nodes |-> 0]
    /\ electionTimer = [n \in Nodes |-> 0]
    /\ heartbeatTimer = [n \in Nodes |-> [m \in Nodes |-> 0]]
    /\ network = EmptyBag
    /\ nextIndex = [n \in Nodes |-> [m \in Nodes |-> 1]]
    /\ matchIndex = [n \in Nodes |-> [m \in Nodes |-> 0]]

\* Actions

Tick(i) ==
    /\ state[i] \in {"Follower", "PreCandidate", "Candidate"}
    /\ electionTimer[i] < ElectionTimeout
    /\ electionTimer' = [electionTimer EXCEPT ![i] = @ + 1]
    /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, heartbeatTimer, network, nextIndex, matchIndex >>

HeartbeatTick(i) ==
    /\ state[i] = "Leader"
    /\ \E j \in Nodes \ {i}: heartbeatTimer[i][j] < HeartbeatInterval
    /\ LET newTimers == [j \in DOMAIN heartbeatTimer[i] |->
                            IF heartbeatTimer[i][j] < HeartbeatInterval
                            THEN heartbeatTimer[i][j] + 1
                            ELSE heartbeatTimer[i][j]]
       IN heartbeatTimer' = [heartbeatTimer EXCEPT ![i] = newTimers]
    /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, electionTimer, network, nextIndex, matchIndex >>

Timeout(i) ==
    /\ state[i] \in {"Follower", "PreCandidate", "Candidate"}
    /\ electionTimer[i] = ElectionTimeout
    /\ network' = network (+) Bag({[
            type |-> "MsgHup",
            from |-> i,
            to   |-> i
        ]})
    /\ electionTimer' = [electionTimer EXCEPT ![i] = 0]
    /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, heartbeatTimer, nextIndex, matchIndex >>

HeartbeatTimeout(i, j) ==
    /\ state[i] = "Leader"
    /\ j \in Nodes \ {i}
    /\ heartbeatTimer[i][j] = HeartbeatInterval
    /\ LET prevIdx == nextIndex[i][j] - 1
           prevTerm == IF prevIdx > 0 THEN log[i][prevIdx].term ELSE 0
       IN network' = network (+) Bag({[
            type         |-> "MsgApp",
            from         |-> i,
            to           |-> j,
            term         |-> currentTerm[i],
            prevLogIndex |-> prevIdx,
            prevLogTerm  |-> prevTerm,
            entries      |-> << >>,
            commit       |-> commitIndex[i]
        ]})
    /\ heartbeatTimer' = [heartbeatTimer EXCEPT ![i] = [@ EXCEPT ![j] = 0]]
    /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, electionTimer, network, nextIndex, matchIndex >>

ClientRequest(val, i) ==
    /\ val \in ClientValues
    /\ i \in Nodes
    /\ network' = network (+) Bag({[
            type  |-> "MsgProp",
            value |-> val,
            to    |-> i
        ]})
    /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, electionTimer, heartbeatTimer, nextIndex, matchIndex >>

Handle(m) ==
    LET i == m.to IN
    /\ \/ m.type = "MsgHup"
       \/ m.type = "MsgProp"
       \/ m.term >= currentTerm[i]
    /\ LET termAdvanced == m.type # "MsgHup" /\ m.type # "MsgProp" /\ m.term > currentTerm[i]
       IN IF termAdvanced
          THEN /\ state' = [state EXCEPT ![i] = "Follower"]
               /\ currentTerm' = [currentTerm EXCEPT ![i] = m.term]
               /\ votedFor' = [votedFor EXCEPT ![i] = DefaultVote]
               /\ electionTimer' = [electionTimer EXCEPT ![i] = 0]
               /\ UNCHANGED << log, commitIndex, heartbeatTimer, network, nextIndex, matchIndex >>
          ELSE
            CASE state[i] = "Follower" ->
                CASE m.type = "MsgApp" ->
                    /\ electionTimer' = [electionTimer EXCEPT ![i] = 0]
                    /\ LET prevIdx == m.prevLogIndex
                           prevTerm == m.prevLogTerm
                           logOK == prevIdx = 0 \/
                                    (prevIdx <= LastLogIndex(log[i]) /\ log[i][prevIdx].term = prevTerm)
                       IN IF logOK
                          THEN /\ LET newLog == SubSeq(log[i], 1, prevIdx) \o m.entries
                                 IN log' = [log EXCEPT ![i] = newLog]
                               /\ commitIndex' = [commitIndex EXCEPT ![i] = IF m.commit <= LastLogIndex(newLog) THEN m.commit ELSE LastLogIndex(newLog)]
                               /\ network' = network (+) Bag({[
                                    type   |-> "MsgAppResp",
                                    from   |-> i,
                                    to     |-> m.from,
                                    term   |-> currentTerm[i],
                                    reject |-> FALSE,
                                    lastLogIndex |-> LastLogIndex(newLog)
                                ]})
                          ELSE /\ network' = network (+) Bag({[
                                    type   |-> "MsgAppResp",
                                    from   |-> i,
                                    to     |-> m.from,
                                    term   |-> currentTerm[i],
                                    reject |-> TRUE
                                ]})
                               /\ UNCHANGED << log, commitIndex >>
                    /\ UNCHANGED << state, currentTerm, votedFor, heartbeatTimer, nextIndex, matchIndex >>

                [] m.type = "MsgVote" \/ m.type = "MsgPreVote" ->
                    /\ LET voteGranted ==
                            /\ IsUpToDate(log[i], m.lastLogIndex, m.logTerm)
                            /\ (m.type = "MsgPreVote" \/ (votedFor[i] = DefaultVote \/ votedFor[i] = m.from))
                       IN IF voteGranted
                          THEN /\ votedFor' = IF m.type = "MsgVote"
                                             THEN [votedFor EXCEPT ![i] = m.from]
                                             ELSE votedFor
                               /\ network' = network (+) Bag({[
                                    type   |-> IF m.type = "MsgVote" THEN "MsgVoteResp" ELSE "MsgPreVoteResp",
                                    from   |-> i,
                                    to     |-> m.from,
                                    term   |-> m.term,
                                    reject |-> FALSE
                                ]})
                          ELSE /\ network' = network (+) Bag({[
                                    type   |-> IF m.type = "MsgVote" THEN "MsgVoteResp" ELSE "MsgPreVoteResp",
                                    from   |-> i,
                                    to     |-> m.from,
                                    term   |-> currentTerm[i],
                                    reject |-> TRUE
                                ]})
                               /\ UNCHANGED << votedFor >>
                    /\ UNCHANGED << state, currentTerm, log, commitIndex, electionTimer, heartbeatTimer, nextIndex, matchIndex >>

                [] m.type = "MsgHup" ->
                    /\ state' = [state EXCEPT ![i] = "PreCandidate"]
                    /\ electionTimer' = [electionTimer EXCEPT ![i] = 0]
                    /\ LET nextTerm == currentTerm[i] + 1
                           lastIdx == LastLogIndex(log[i])
                           lastTerm == LastLogTerm(log[i])
                       IN network' = network (+) Bag({[
                            type         |-> "MsgPreVote",
                            from         |-> i,
                            to           |-> j,
                            term         |-> nextTerm,
                            lastLogIndex |-> lastIdx,
                            logTerm      |-> lastTerm
                        ] : j \in Nodes \ {i}})
                    /\ UNCHANGED << currentTerm, votedFor, log, commitIndex, heartbeatTimer, nextIndex, matchIndex >>

                [] OTHER -> UNCHANGED << vars >>

            [] state[i] = "PreCandidate" ->
                CASE m.type = "MsgPreVoteResp" ->
                    /\ LET votesSoFar == {i} \cup {n \in Nodes :
                                            \E msg \in BagToSet(network):
                                                msg.type = "MsgPreVoteResp" /\ msg.from = n /\ msg.to = i /\ msg.reject = FALSE}
                       IN IF Cardinality(votesSoFar) >= Quorum
                          THEN /\ state' = [state EXCEPT ![i] = "Candidate"]
                               /\ currentTerm' = [currentTerm EXCEPT ![i] = @ + 1]
                               /\ votedFor' = [votedFor EXCEPT ![i] = i]
                               /\ electionTimer' = [electionTimer EXCEPT ![i] = 0]
                               /\ LET newTerm == currentTerm[i] + 1
                                      lastIdx == LastLogIndex(log[i])
                                      lastTerm == LastLogTerm(log[i])
                                  IN network' = network (+) Bag({[
                                        type         |-> "MsgVote",
                                        from         |-> i,
                                        to           |-> j,
                                        term         |-> newTerm,
                                        lastLogIndex |-> lastIdx,
                                        logTerm      |-> lastTerm
                                    ] : j \in Nodes \ {i}})
                               /\ UNCHANGED << heartbeatTimer >>
                          ELSE /\ UNCHANGED << state, currentTerm, votedFor, electionTimer, heartbeatTimer >>
                               /\ network' = network
                    /\ UNCHANGED << log, commitIndex, nextIndex, matchIndex >>

                [] m.type = "MsgApp" ->
                    /\ state' = [state EXCEPT ![i] = "Follower"]
                    /\ currentTerm' = [currentTerm EXCEPT ![i] = m.term]
                    /\ votedFor' = [votedFor EXCEPT ![i] = DefaultVote]
                    /\ electionTimer' = [electionTimer EXCEPT ![i] = 0]
                    /\ UNCHANGED << log, commitIndex, heartbeatTimer, network, nextIndex, matchIndex >>

                [] OTHER -> UNCHANGED << vars >>

            [] state[i] = "Candidate" ->
                CASE m.type = "MsgVoteResp" ->
                    /\ LET votesSoFar == {i} \cup {n \in Nodes :
                                            \E msg \in BagToSet(network):
                                                msg.type = "MsgVoteResp" /\ msg.from = n /\ msg.to = i /\ msg.reject = FALSE}
                       IN IF Cardinality(votesSoFar) >= Quorum
                          THEN /\ state' = [state EXCEPT ![i] = "Leader"]
                               /\ nextIndex' = [nextIndex EXCEPT ![i] = [j \in Nodes |-> LastLogIndex(log[i]) + 1]]
                               /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in Nodes |-> 0]]
                               /\ heartbeatTimer' = [heartbeatTimer EXCEPT ![i] = [j \in Nodes |-> HeartbeatInterval]]
                               /\ LET prevIdx == LastLogIndex(log[i])
                                      prevTerm == LastLogTerm(log[i])
                                  IN network' = network (+) Bag({[
                                        type         |-> "MsgApp",
                                        from         |-> i,
                                        to           |-> j,
                                        term         |-> currentTerm[i],
                                        prevLogIndex |-> prevIdx,
                                        prevLogTerm  |-> prevTerm,
                                        entries      |-> << >>,
                                        commit       |-> commitIndex[i]
                                    ] : j \in Nodes \ {i}})
                               /\ UNCHANGED << electionTimer >>
                          ELSE /\ UNCHANGED << state, nextIndex, matchIndex, electionTimer, heartbeatTimer >>
                               /\ network' = network
                    /\ UNCHANGED << currentTerm, votedFor, log, commitIndex >>

                [] m.type = "MsgApp" ->
                    /\ state' = [state EXCEPT ![i] = "Follower"]
                    /\ currentTerm' = [currentTerm EXCEPT ![i] = m.term]
                    /\ votedFor' = [votedFor EXCEPT ![i] = DefaultVote]
                    /\ electionTimer' = [electionTimer EXCEPT ![i] = 0]
                    /\ UNCHANGED << log, commitIndex, heartbeatTimer, network, nextIndex, matchIndex >>

                [] OTHER -> UNCHANGED << vars >>

            [] state[i] = "Leader" ->
                CASE m.type = "MsgProp" ->
                    /\ LET newEntry == [term |-> currentTerm[i], value |-> m.value]
                           newLog == Append(log[i], newEntry)
                       IN log' = [log EXCEPT ![i] = newLog]
                    /\ matchIndex' = [matchIndex EXCEPT ![i] = [@ EXCEPT ![i] = LastLogIndex(newLog)]]
                    /\ nextIndex' = [nextIndex EXCEPT ![i] = [@ EXCEPT ![i] = LastLogIndex(newLog) + 1]]
                    /\ UNCHANGED << state, currentTerm, votedFor, commitIndex, electionTimer, heartbeatTimer, network >>

                [] m.type = "MsgAppResp" ->
                    /\ IF m.reject = FALSE
                       THEN /\ LET mi_prime == [matchIndex EXCEPT ![i] = [@ EXCEPT ![m.from] = m.lastLogIndex]]
                            IN /\ matchIndex' = mi_prime
                               /\ nextIndex' = [nextIndex EXCEPT ![i] = [@ EXCEPT ![m.from] = m.lastLogIndex + 1]]
                               /\ LET possibleCIs == { N \in (commitIndex[i]+1)..LastLogIndex(log[i]) :
                                                         /\ log[i][N].term = currentTerm[i]
                                                         /\ Cardinality({j \in Nodes : mi_prime[i][j] >= N}) >= Quorum }
                                  IN IF possibleCIs /= {}
                                     THEN LET newCommitIndex == Max(possibleCIs)
                                          IN commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
                                     ELSE UNCHANGED << commitIndex >>
                       ELSE /\ nextIndex' = [nextIndex EXCEPT ![i] = [@ EXCEPT ![m.from] = @[m.from] - 1]]
                            /\ UNCHANGED << matchIndex, commitIndex >>
                    /\ UNCHANGED << state, currentTerm, votedFor, log, electionTimer, heartbeatTimer, network >>

                [] OTHER -> UNCHANGED << vars >>

Receive(m) ==
    /\ Handle(m)
    /\ network' = network \ Bag({m})

Next ==
    \/ \E i \in Nodes: Tick(i)
    \/ \E i \in Nodes: HeartbeatTick(i)
    \/ \E i \in Nodes: Timeout(i)
    \/ \E i \in Nodes, j \in Nodes: HeartbeatTimeout(i, j)
    \/ \E val \in ClientValues, i \in Nodes: ClientRequest(val, i)
    \/ \E m \in BagToSet(network): Receive(m)

Spec == Init /\ [][Next]_vars

====
