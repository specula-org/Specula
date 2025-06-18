---- MODULE RaftConsensus ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Nodes, MaxLogLength, MaxTerm

VARIABLES 
    currentTerm,
    votedFor,
    log,
    commitIndex,
    state,
    leaderId,
    nextIndex,
    matchIndex,
    votes,
    electionTimeout,
    messages

vars == <<currentTerm, votedFor, log, commitIndex, state, leaderId, nextIndex, matchIndex, votes, electionTimeout, messages>>

States == {"Follower", "Candidate", "Leader"}
MessageTypes == {"RequestVote", "RequestVoteResponse", "AppendEntries", "AppendEntriesResponse", "Heartbeat", "HeartbeatResponse"}

Min(turple) == IF turple[1] > turple[2] THEN turple[2] ELSE turple[1]
Max(turple) == IF turple[1] > turple[2] THEN turple[1] ELSE turple[2]

TypeInvariant == 
    /\ currentTerm \in [Nodes -> 0..MaxTerm]
    /\ votedFor \in [Nodes -> Nodes \cup {0}]
    /\ log \in [Nodes -> Seq(Nat \times Nat)]
    /\ commitIndex \in [Nodes -> Nat]
    /\ state \in [Nodes -> States]
    /\ leaderId \in [Nodes -> Nodes \cup {0}]
    /\ nextIndex \in [Nodes -> [Nodes -> Nat]]
    /\ matchIndex \in [Nodes -> [Nodes -> Nat]]
    /\ votes \in [Nodes -> SUBSET Nodes]
    /\ electionTimeout \in [Nodes -> BOOLEAN]
    /\ messages \in SUBSET [type: MessageTypes, from: Nodes, to: Nodes, term: Nat, logTerm: Nat, logIndex: Nat, commitIndex: Nat, entries: Seq(Nat \times Nat), success: BOOLEAN]

Init == 
    /\ currentTerm = [n \in Nodes |-> 0]
    /\ votedFor = [n \in Nodes |-> 0]
    /\ log = [n \in Nodes |-> <<>>]
    /\ commitIndex = [n \in Nodes |-> 0]
    /\ state = [n \in Nodes |-> "Follower"]
    /\ leaderId = [n \in Nodes |-> 0]
    /\ nextIndex = [n \in Nodes |-> [m \in Nodes |-> 1]]
    /\ matchIndex = [n \in Nodes |-> [m \in Nodes |-> 0]]
    /\ votes = [n \in Nodes |-> {}]
    /\ electionTimeout = [n \in Nodes |-> FALSE]
    /\ messages = {}

BecomeFollower(n, term, leader) ==
    /\ state' = [state EXCEPT ![n] = "Follower"]
    /\ currentTerm' = [currentTerm EXCEPT ![n] = term]
    /\ votedFor' = [votedFor EXCEPT ![n] = 0]
    /\ leaderId' = [leaderId EXCEPT ![n] = leader]
    /\ electionTimeout' = [electionTimeout EXCEPT ![n] = FALSE]
    /\ votes' = [votes EXCEPT ![n] = {}]
    /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, messages>>

BecomeCandidate(n) ==
    /\ state[n] \in {"Follower", "Candidate"}
    /\ electionTimeout[n] = TRUE
    /\ state' = [state EXCEPT ![n] = "Candidate"]
    /\ currentTerm' = [currentTerm EXCEPT ![n] = currentTerm[n] + 1]
    /\ votedFor' = [votedFor EXCEPT ![n] = n]
    /\ leaderId' = [leaderId EXCEPT ![n] = 0]
    /\ votes' = [votes EXCEPT ![n] = {n}]
    /\ electionTimeout' = [electionTimeout EXCEPT ![n] = FALSE]
    /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, messages>>

BecomeLeader(n) ==
    /\ state[n] = "Candidate"
    /\ Cardinality(votes[n]) * 2 > Cardinality(Nodes)
    /\ state' = [state EXCEPT ![n] = "Leader"]
    /\ leaderId' = [leaderId EXCEPT ![n] = n]
    /\ nextIndex' = [nextIndex EXCEPT ![n] = [m \in Nodes |-> Len(log[n]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![n] = [m \in Nodes |-> IF m = n THEN Len(log[n]) ELSE 0]]
    /\ log' = [log EXCEPT ![n] = Append(log[n], <<currentTerm[n], 0>>)]
    /\ UNCHANGED <<currentTerm, votedFor, commitIndex, votes, electionTimeout, messages>>

RequestVote(n) ==
    /\ state[n] = "Candidate"
    /\ \E m \in Nodes : 
        /\ m # n
        /\ ~\E msg \in messages : msg.type = "RequestVote" /\ msg.from = n /\ msg.to = m /\ msg.term = currentTerm[n]
        /\ messages' = messages \cup {[
            type |-> "RequestVote",
            from |-> n,
            to |-> m,
            term |-> currentTerm[n],
            logTerm |-> IF Len(log[n]) > 0 THEN log[n][Len(log[n])][1] ELSE 0,
            logIndex |-> Len(log[n]),
            commitIndex |-> 0,
            entries |-> <<>>,
            success |-> FALSE
            ]}
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, state, leaderId, nextIndex, matchIndex, votes, electionTimeout>>

HandleVoteRequest(n, msg) ==
    /\ msg.type = "RequestVote"
    /\ msg.to = n
    /\ LET canVote == \/ votedFor[n] = 0
                     \/ votedFor[n] = msg.from
                     \/ msg.term > currentTerm[n]
           logOk == \/ msg.logTerm > (IF Len(log[n]) > 0 THEN log[n][Len(log[n])][1] ELSE 0)
                    \/ /\ msg.logTerm = (IF Len(log[n]) > 0 THEN log[n][Len(log[n])][1] ELSE 0)
                       /\ msg.logIndex >= Len(log[n])
           grant == /\ msg.term >= currentTerm[n]
                    /\ canVote
                    /\ logOk
       IN /\ IF msg.term > currentTerm[n]
             THEN /\ currentTerm' = [currentTerm EXCEPT ![n] = msg.term]
                  /\ votedFor' = [votedFor EXCEPT ![n] = IF grant THEN msg.from ELSE 0]
                  /\ state' = [state EXCEPT ![n] = "Follower"]
                  /\ leaderId' = [leaderId EXCEPT ![n] = 0]
             ELSE /\ IF grant THEN votedFor' = [votedFor EXCEPT ![n] = msg.from]
                               ELSE UNCHANGED votedFor
                  /\ UNCHANGED <<currentTerm, state, leaderId>>
          /\ messages' = (messages \ {msg}) \cup {[
              type |-> "RequestVoteResponse",
              from |-> n,
              to |-> msg.from,
              term |-> IF msg.term > currentTerm[n] THEN msg.term ELSE currentTerm[n],
              logTerm |-> 0,
              logIndex |-> 0,
              commitIndex |-> 0,
              entries |-> <<>>,
              success |-> grant
            ]}
          /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, votes, electionTimeout>>

HandleVoteResponse(n, msg) ==
    /\ msg.type = "RequestVoteResponse"
    /\ msg.to = n
    /\ state[n] = "Candidate"
    /\ msg.term = currentTerm[n]
    /\ IF msg.success
       THEN /\ votes' = [votes EXCEPT ![n] = votes[n] \cup {msg.from}]
            /\ IF Cardinality(votes[n] \cup {msg.from}) * 2 > Cardinality(Nodes)
               THEN /\ state' = [state EXCEPT ![n] = "Leader"]
                    /\ leaderId' = [leaderId EXCEPT ![n] = n]
                    /\ nextIndex' = [nextIndex EXCEPT ![n] = [m \in Nodes |-> Len(log[n]) + 1]]
                    /\ matchIndex' = [matchIndex EXCEPT ![n] = [m \in Nodes |-> IF m = n THEN Len(log[n]) ELSE 0]]
               ELSE UNCHANGED <<state, leaderId, nextIndex, matchIndex>>
       ELSE UNCHANGED <<votes, state, leaderId, nextIndex, matchIndex>>
    /\ messages' = messages \ {msg}
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, electionTimeout>>

AppendEntries(n) ==
    /\ state[n] = "Leader"
    /\ \E m \in Nodes :
        /\ m # n
        /\ LET prevIndex == nextIndex[n][m] - 1
               prevTerm == IF prevIndex > 0 /\ prevIndex <= Len(log[n]) 
                          THEN log[n][prevIndex][1] 
                          ELSE 0
               entries == IF nextIndex[n][m] <= Len(log[n])
                         THEN SubSeq(log[n], nextIndex[n][m], Len(log[n]))
                         ELSE <<>>
           IN messages' = messages \cup {[
               type |-> "AppendEntries",
               from |-> n,
               to |-> m,
               term |-> currentTerm[n],
               logTerm |-> prevTerm,
               logIndex |-> prevIndex,
               commitIndex |-> commitIndex[n],
               entries |-> entries,
               success |-> FALSE
           ]}
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, state, leaderId, nextIndex, matchIndex, votes, electionTimeout>>

HandleAppendRequest(n, msg) ==
    /\ msg.type = "AppendEntries"
    /\ msg.to = n
    /\ IF msg.term > currentTerm[n]
       THEN /\ currentTerm' = [currentTerm EXCEPT ![n] = msg.term]
            /\ state' = [state EXCEPT ![n] = "Follower"]
            /\ votedFor' = [votedFor EXCEPT ![n] = 0]
            /\ leaderId' = [leaderId EXCEPT ![n] = msg.from]
            /\ electionTimeout' = [electionTimeout EXCEPT ![n] = FALSE]
       ELSE /\ leaderId' = [leaderId EXCEPT ![n] = msg.from]
            /\ electionTimeout' = [electionTimeout EXCEPT ![n] = FALSE]
            /\ UNCHANGED <<currentTerm, state, votedFor>>
    /\ LET logOk == \/ msg.logIndex = 0
                    \/ /\ msg.logIndex <= Len(log[n])
                       /\ msg.logIndex > 0
                       /\ log[n][msg.logIndex][1] = msg.logTerm
           success == /\ msg.term >= currentTerm[n]
                      /\ logOk
       IN /\ IF success /\ Len(msg.entries) > 0
             THEN /\ log' = [log EXCEPT ![n] = SubSeq(log[n], 1, msg.logIndex) \o msg.entries]
             ELSE UNCHANGED log
          /\ IF success
             THEN commitIndex' = [commitIndex EXCEPT ![n] = 
                     IF msg.commitIndex > commitIndex[n]
                     THEN Min({msg.commitIndex, Len(log'[n])})
                     ELSE commitIndex[n]]
             ELSE UNCHANGED commitIndex
          /\ messages' = (messages \ {msg}) \cup {[
              type |-> "AppendEntriesResponse",
              from |-> n,
              to |-> msg.from,
              term |-> currentTerm'[n],
              logTerm |-> 0,
              logIndex |-> IF success THEN msg.logIndex + Len(msg.entries) ELSE 0,
              commitIndex |-> 0,
              entries |-> <<>>,
              success |-> success
            ]}
    /\ UNCHANGED <<nextIndex, matchIndex, votes>>

HandleAppendResponse(n, msg) ==
    /\ msg.type = "AppendEntriesResponse"
    /\ msg.to = n
    /\ state[n] = "Leader"
    /\ msg.term = currentTerm[n]
    /\ IF msg.success
       THEN /\ nextIndex' = [nextIndex EXCEPT ![n][msg.from] = msg.logIndex + 1]
            /\ matchIndex' = [matchIndex EXCEPT ![n][msg.from] = msg.logIndex]
       ELSE /\ nextIndex' = [nextIndex EXCEPT ![n][msg.from] = Max({1, nextIndex[n][msg.from] - 1})]
            /\ UNCHANGED matchIndex
    /\ messages' = messages \ {msg}
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, state, leaderId, votes, electionTimeout>>

AdvanceCommitIndex(n) ==
    /\ state[n] = "Leader"
    /\ \E index \in (commitIndex[n] + 1)..Len(log[n]) :
        /\ log[n][index][1] = currentTerm[n]
        /\ Cardinality({m \in Nodes : matchIndex[n][m] >= index}) * 2 > Cardinality(Nodes)
        /\ commitIndex' = [commitIndex EXCEPT ![n] = index]
    /\ UNCHANGED <<currentTerm, votedFor, log, state, leaderId, nextIndex, matchIndex, votes, electionTimeout, messages>>

ElectionTimeout(n) ==
    /\ state[n] \in {"Follower", "Candidate"}
    /\ electionTimeout' = [electionTimeout EXCEPT ![n] = TRUE]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, state, leaderId, nextIndex, matchIndex, votes, messages>>

HeartbeatTimeout(n) ==
    /\ state[n] = "Leader"
    /\ \E m \in Nodes :
        /\ m # n
        /\ messages' = messages \cup {[
            type |-> "Heartbeat",
            from |-> n,
            to |-> m,
            term |-> currentTerm[n],
            logTerm |-> 0,
            logIndex |-> 0,
            commitIndex |-> commitIndex[n],
            entries |-> <<>>,
            success |-> FALSE
            ]}
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, state, leaderId, nextIndex, matchIndex, votes, electionTimeout>>

HandleHeartbeat(n, msg) ==
    /\ msg.type = "Heartbeat"
    /\ msg.to = n
    /\ IF msg.term >= currentTerm[n]
       THEN /\ currentTerm' = [currentTerm EXCEPT ![n] = msg.term]
            /\ state' = [state EXCEPT ![n] = "Follower"]
            /\ leaderId' = [leaderId EXCEPT ![n] = msg.from]
            /\ electionTimeout' = [electionTimeout EXCEPT ![n] = FALSE]
            /\ IF msg.commitIndex > commitIndex[n]
               THEN commitIndex' = [commitIndex EXCEPT ![n] = Min({msg.commitIndex, Len(log[n])})]
               ELSE UNCHANGED commitIndex
       ELSE UNCHANGED <<currentTerm, state, leaderId, electionTimeout, commitIndex>>
    /\ messages' = (messages \ {msg}) \cup {[
        type |-> "HeartbeatResponse",
        from |-> n,
        to |-> msg.from,
        term |-> currentTerm'[n],
        logTerm |-> 0,
        logIndex |-> 0,
        commitIndex |-> 0,
        entries |-> <<>>,
        success |-> msg.term >= currentTerm[n]
        ]}
    /\ UNCHANGED <<votedFor, log, nextIndex, matchIndex, votes>>

HandleHeartbeatResponse(n, msg) ==
    /\ msg.type = "HeartbeatResponse"
    /\ msg.to = n
    /\ state[n] = "Leader"
    /\ messages' = messages \ {msg}
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, state, leaderId, nextIndex, matchIndex, votes, electionTimeout>>

Next == 
    \/ \E n \in Nodes : BecomeCandidate(n)
    \/ \E n \in Nodes : BecomeLeader(n)
    \/ \E n \in Nodes : RequestVote(n)
    \/ \E n \in Nodes, msg \in messages : HandleVoteRequest(n, msg)
    \/ \E n \in Nodes, msg \in messages : HandleVoteResponse(n, msg)
    \/ \E n \in Nodes : AppendEntries(n)
    \/ \E n \in Nodes, msg \in messages : HandleAppendRequest(n, msg)
    \/ \E n \in Nodes, msg \in messages : HandleAppendResponse(n, msg)
    \/ \E n \in Nodes : AdvanceCommitIndex(n)
    \/ \E n \in Nodes : ElectionTimeout(n)
    \/ \E n \in Nodes : HeartbeatTimeout(n)
    \/ \E n \in Nodes, msg \in messages : HandleHeartbeat(n, msg)
    \/ \E n \in Nodes, msg \in messages : HandleHeartbeatResponse(n, msg)

Spec == Init /\ [][Next]_vars

TypeOK == TypeInvariant

ElectionSafety == 
    \A n1, n2 \in Nodes : 
        /\ state[n1] = "Leader" 
        /\ state[n2] = "Leader" 
        /\ currentTerm[n1] = currentTerm[n2]
        => n1 = n2

LeaderAppendOnly == 
    \A n \in Nodes : state[n] = "Leader" =>
        \A i \in 1..Len(log[n]) : 
            [][\A j \in 1..Len(log'[n]) : j <= i => log'[n][j] = log[n][j]]_vars

LogMatching == 
    \A n1, n2 \in Nodes, i \in Nat :
        /\ i <= Len(log[n1])
        /\ i <= Len(log[n2])
        /\ log[n1][i][1] = log[n2][i][1]
        => \A j \in 1..i : log[n1][j] = log[n2][j]

====