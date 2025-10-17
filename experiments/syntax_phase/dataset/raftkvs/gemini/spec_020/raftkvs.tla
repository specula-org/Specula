---- MODULE raftkvs ----
EXTENDS TLC, Sequences, Naturals, FiniteSets, Bags

CONSTANTS
    NumServers,
    NumClients,
    Nil,
    AllKeys,
    AllValues

ASSUME NumServers \in Nat \ {0}
ASSUME NumClients \in Nat

Server == 1..NumServers
Client == (NumServers + 1)..(NumServers + NumClients)

StateVal == {"follower", "candidate", "leader"}
MsgTypeVal == {"rvq", "rvp", "aer", "aep", "cpq", "cgq", "cpp", "cgp"}

Max(S) == CHOOSE x \in S : \A y \in S : y <= x
Min(S) == CHOOSE x \in S : \A y \in S : x <= y

IsQuorum(S) == Cardinality(S) * 2 > NumServers

LastTerm(lg) == IF Len(lg) = 0 THEN 0 ELSE (lg[Len(lg)])["term"]
LastIndex(lg) == Len(lg)

VARIABLES
    net,
    state,
    currentTerm,
    votedFor,
    log,
    commitIndex,
    lastApplied,
    votesGranted,
    nextIndex,
    matchIndex,
    sm,
    leaderHint

vars == <<net, state, currentTerm, votedFor, log, commitIndex, lastApplied,
          votesGranted, nextIndex, matchIndex, sm, leaderHint>>

Init ==
    /\ net = EmptyBag
    /\ state = [s \in Server |-> "follower"]
    /\ currentTerm = [s \in Server |-> 0]
    /\ votedFor = [s \in Server |-> Nil]
    /\ log = [s \in Server |-> <<>>]
    /\ commitIndex = [s \in Server |-> 0]
    /\ lastApplied = [s \in Server |-> 0]
    /\ votesGranted = [s \in Server |-> {}]
    /\ nextIndex = [s \in Server |-> [t \in Server |-> 1]]
    /\ matchIndex = [s \in Server |-> [t \in Server |-> 0]]
    /\ sm = [s \in Server |-> [k \in AllKeys |-> Nil]]
    /\ leaderHint = [s \in Server |-> Nil]

BecomeFollower(i, term) ==
    /\ state' = [state EXCEPT ![i] = "follower"]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = term]
    /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
    /\ leaderHint' = [leaderHint EXCEPT ![i] = Nil]
    /\ UNCHANGED <<net, log, commitIndex, lastApplied, votesGranted, nextIndex, matchIndex, sm>>

Timeout(i) ==
    /\ i \in Server
    /\ state[i] \in {"follower", "candidate"}
    /\ state' = [state EXCEPT ![i] = "candidate"]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
    /\ votedFor' = [votedFor EXCEPT ![i] = i]
    /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}]
    /\ leaderHint' = [leaderHint EXCEPT ![i] = Nil]
    /\ LET newTerm == currentTerm[i] + 1
           req(j) == [type |-> "rvq", term |-> newTerm, candidateId |-> i,
                       lastLogIndex |-> LastIndex(log[i]),
                       lastLogTerm |-> LastTerm(log[i]),
                       source |-> i, dest |-> j]
       IN net' = net (+) Bag({req(j) : j \in Server \ {i}})
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, sm>>

HandleRequestVoteRequest(i, msg) ==
    /\ i \in Server
    /\ msg \in BagToSet(net)
    /\ msg["type"] = "rvq"
    /\ msg["dest"] = i
    /\ IF msg["term"] > currentTerm[i] THEN
        /\ BecomeFollower(i, msg["term"])
        /\ net' = net \- ({msg} @@ 1)
    ELSE
        /\ LET logIsOk == \/ msg["lastLogTerm"] > LastTerm(log[i])
                        \/ /\ msg["lastLogTerm"] = LastTerm(log[i])
                           /\ msg["lastLogIndex"] >= LastIndex(log[i])
               grantVote == /\ msg["term"] = currentTerm[i]
                            /\ votedFor[i] \in {Nil, msg["candidateId"]}
                            /\ logIsOk
               resp(granted) == [type |-> "rvp", term |-> currentTerm[i], voteGranted |-> granted,
                                 source |-> i, dest |-> msg["source"]]
           IN /\ net' = (net \- ({msg} @@ 1)) (+) ({resp(grantVote)} @@ 1)
              /\ votedFor' = IF grantVote THEN
                                 [votedFor EXCEPT ![i] = msg["candidateId"]]
                             ELSE
                                 votedFor
              /\ UNCHANGED <<state, currentTerm, log, commitIndex, lastApplied,
                             votesGranted, nextIndex, matchIndex, sm, leaderHint>>

HandleRequestVoteResponse(i, msg) ==
    /\ i \in Server
    /\ msg \in BagToSet(net)
    /\ msg["type"] = "rvp"
    /\ msg["dest"] = i
    /\ net' = net \- ({msg} @@ 1)
    /\ IF msg["term"] > currentTerm[i] THEN
        BecomeFollower(i, msg["term"])
    ELSE
        /\ votesGranted' = IF state[i] = "candidate" /\ msg["term"] = currentTerm[i] /\ msg["voteGranted"] THEN
                               [votesGranted EXCEPT ![i] = @ \cup {msg["source"]}]
                           ELSE
                               votesGranted
        /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied,
                       nextIndex, matchIndex, sm, leaderHint>>

BecomeLeader(i) ==
    /\ i \in Server
    /\ state[i] = "candidate"
    /\ IsQuorum(votesGranted[i])
    /\ state' = [state EXCEPT ![i] = "leader"]
    /\ leaderHint' = [leaderHint EXCEPT ![i] = i]
    /\ nextIndex' = [nextIndex EXCEPT ![i] = [j \in Server |-> LastIndex(log[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ UNCHANGED <<net, currentTerm, votedFor, log, commitIndex, lastApplied,
                   votesGranted, sm>>

LeaderSendAppendEntries(i, j) ==
    /\ i \in Server
    /\ j \in Server \ {i}
    /\ state[i] = "leader"
    /\ LET prevLogIndex == nextIndex[i][j] - 1
           prevLogTerm == IF prevLogIndex > 0 THEN log[i][prevLogIndex]["term"] ELSE 0
           entries == SubSeq(log[i], nextIndex[i][j], Len(log[i]))
           msg == [type |-> "aer", term |-> currentTerm[i], leaderId |-> i,
                   prevLogIndex |-> prevLogIndex, prevLogTerm |-> prevLogTerm,
                   entries |-> entries, leaderCommit |-> commitIndex[i],
                   source |-> i, dest |-> j]
    /\ net' = net (+) ({msg} @@ 1)
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied,
                   votesGranted, nextIndex, matchIndex, sm, leaderHint>>

HandleAppendEntriesRequest(i, msg) ==
    /\ i \in Server
    /\ msg \in BagToSet(net)
    /\ msg["type"] = "aer"
    /\ msg["dest"] = i
    /\ IF msg["term"] > currentTerm[i] THEN
        /\ BecomeFollower(i, msg["term"])
        /\ net' = net \- ({msg} @@ 1)
    ELSE
        /\ LET
            logOk == msg["prevLogIndex"] = 0 \/
                     ( /\ msg["prevLogIndex"] <= Len(log[i])
                       /\ log[i][msg["prevLogIndex"]]["term"] = msg["prevLogTerm"] )
            resp(success, mIndex) == [type |-> "aep", term |-> currentTerm[i],
                                      success |-> success, matchIndex |-> mIndex,
                                      source |-> i, dest |-> msg["source"]]
        /\ IF msg["term"] < currentTerm[i] \/ (msg["term"] = currentTerm[i] /\ NOT logOk) THEN
            /\ net' = (net \- ({msg} @@ 1)) (+) ({resp(FALSE, 0)} @@ 1)
            /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied,
                           votesGranted, nextIndex, matchIndex, sm, leaderHint>>
        ELSE
            /\ LET newLog == Append(SubSeq(log[i], 1, msg["prevLogIndex"]), msg["entries"])
               IN /\ net' = (net \- ({msg} @@ 1)) (+) ({resp(TRUE, msg["prevLogIndex"] + Len(msg["entries"]))} @@ 1)
                  /\ state' = [state EXCEPT ![i] = IF @ = "candidate" THEN "follower" ELSE @]
                  /\ leaderHint' = [leaderHint EXCEPT ![i] = msg["leaderId"]]
                  /\ log' = [log EXCEPT ![i] = newLog]
                  /\ commitIndex' = IF msg["leaderCommit"] > commitIndex[i] THEN
                                        [commitIndex EXCEPT ![i] = Min({msg["leaderCommit"], Len(newLog)})]
                                    ELSE
                                        commitIndex
                  /\ UNCHANGED <<currentTerm, votedFor, lastApplied, votesGranted,
                                 nextIndex, matchIndex, sm>>

HandleAppendEntriesResponse(i, msg) ==
    /\ i \in Server
    /\ msg \in BagToSet(net)
    /\ msg["type"] = "aep"
    /\ msg["dest"] = i
    /\ net' = net \- ({msg} @@ 1)
    /\ IF msg["term"] > currentTerm[i] THEN
        BecomeFollower(i, msg["term"])
    ELSE
        /\ IF state[i] = "leader" /\ msg["term"] = currentTerm[i] THEN
            /\ nextIndex' = IF msg["success"] THEN
                                [nextIndex EXCEPT ![i] = [@ EXCEPT ![msg["source"]] = msg["matchIndex"] + 1]]
                            ELSE
                                [nextIndex EXCEPT ![i] = [@ EXCEPT ![msg["source"]] = Max({1, @[msg["source"]] - 1})]]
            /\ matchIndex' = IF msg["success"] THEN
                                [matchIndex EXCEPT ![i] = [@ EXCEPT ![msg["source"]] = msg["matchIndex"]]]
                             ELSE
                                matchIndex
        ELSE
            /\ UNCHANGED <<nextIndex, matchIndex>>
        /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied,
                       votesGranted, sm, leaderHint>>

LeaderAdvanceCommitIndex(i) ==
    /\ i \in Server
    /\ state[i] = "leader"
    /\ LET
        possibleN == { N \in (commitIndex[i]+1)..Len(log[i]) |
                        /\ log[i][N]["term"] = currentTerm[i]
                        /\ IsQuorum({i} \cup {k \in Server | matchIndex[i][k] >= N}) }
    /\ IF possibleN /= {} THEN
        /\ commitIndex' = [commitIndex EXCEPT ![i] = Max(possibleN)]
    ELSE
        /\ commitIndex' = commitIndex
    /\ UNCHANGED <<net, state, currentTerm, votedFor, log, lastApplied,
                   votesGranted, nextIndex, matchIndex, sm, leaderHint>>

ApplyToStateMachine(i) ==
    /\ i \in Server
    /\ commitIndex[i] > lastApplied[i]
    /\ LET newLastApplied == lastApplied[i] + 1
           entry == log[i][newLastApplied]
           cmd == entry["cmd"]
    /\ lastApplied' = [lastApplied EXCEPT ![i] = newLastApplied]
    /\ sm' = IF cmd["type"] = "put" THEN
                 [sm EXCEPT ![i] = [@ EXCEPT ![cmd["key"]] = cmd["value"]]]
             ELSE
                 sm
    /\ net' = IF state[i] = "leader" /\ cmd["client"] /= Nil THEN
                  LET
                      respType == IF cmd["type"] = "put" THEN "cpp" ELSE "cgp"
                      respVal == IF cmd["type"] = "get" THEN sm[i][cmd["key"]] ELSE Nil
                      respMsg == [type |-> respType, success |-> TRUE,
                                  value |-> respVal, reqId |-> cmd["reqId"],
                                  source |-> i, dest |-> cmd["client"]]
                  IN net (+) ({respMsg} @@ 1)
              ELSE
                  net
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex,
                   votesGranted, nextIndex, matchIndex, leaderHint>>

ClientRequest(c, srv) ==
    /\ c \in Client
    /\ srv \in Server
    /\ \E key \in AllKeys, val \in AllValues, type \in {"put", "get"}, reqId \in Nat:
        /\ LET cmd == [type |-> type, key |-> key, value |-> val,
                       client |-> c, reqId |-> reqId]
               msgType == IF type = "put" THEN "cpq" ELSE "cgq"
               msg == [type |-> msgType, cmd |-> cmd, source |-> c, dest |-> srv]
        /\ net' = net (+) ({msg} @@ 1)
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied,
                   votesGranted, nextIndex, matchIndex, sm, leaderHint>>

HandleClientRequest(i, msg) ==
    /\ i \in Server
    /\ msg \in BagToSet(net)
    /\ msg["type"] \in {"cpq", "cgq"}
    /\ msg["dest"] = i
    /\ IF state[i] = "leader" THEN
        /\ LET newEntry == [term |-> currentTerm[i], cmd |-> msg["cmd"]]
        /\ log' = [log EXCEPT ![i] = Append(@, newEntry)]
        /\ net' = net \- ({msg} @@ 1)
        /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied,
                       votesGranted, nextIndex, matchIndex, sm, leaderHint>>
    ELSE
        /\ LET
            respType == IF msg["type"] = "cpq" THEN "cpp" ELSE "cgp"
            respMsg == [type |-> respType, success |-> FALSE,
                        leaderHint |-> leaderHint[i], reqId |-> msg["cmd"]["reqId"],
                        source |-> i, dest |-> msg["source"]]
        /\ net' = (net \- ({msg} @@ 1)) (+) ({respMsg} @@ 1)
        /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied,
                       votesGranted, nextIndex, matchIndex, sm, leaderHint>>

HandleClientResponse(c, msg) ==
    /\ c \in Client
    /\ msg \in BagToSet(net)
    /\ msg["type"] \in {"cpp", "cgp"}
    /\ msg["dest"] = c
    /\ net' = net \- ({msg} @@ 1)
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied,
                   votesGranted, nextIndex, matchIndex, sm, leaderHint>>

DropMessage(msg) ==
    /\ msg \in BagToSet(net)
    /\ net' = net \- ({msg} @@ 1)
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied,
                   votesGranted, nextIndex, matchIndex, sm, leaderHint>>

Next ==
    \/ \E i \in Server : Timeout(i)
    \/ \E i \in Server, msg \in BagToSet(net) : HandleRequestVoteRequest(i, msg)
    \/ \E i \in Server, msg \in BagToSet(net) : HandleRequestVoteResponse(i, msg)
    \/ \E i \in Server : BecomeLeader(i)
    \/ \E i \in Server, j \in Server : LeaderSendAppendEntries(i, j)
    \/ \E i \in Server, msg \in BagToSet(net) : HandleAppendEntriesRequest(i, msg)
    \/ \E i \in Server, msg \in BagToSet(net) : HandleAppendEntriesResponse(i, msg)
    \/ \E i \in Server : LeaderAdvanceCommitIndex(i)
    \/ \E i \in Server : ApplyToStateMachine(i)
    \/ \E c \in Client, srv \in Server : ClientRequest(c, srv)
    \/ \E i \in Server, msg \in BagToSet(net) : HandleClientRequest(i, msg)
    \/ \E c \in Client, msg \in BagToSet(net) : HandleClientResponse(c, msg)
    \/ \E msg \in BagToSet(net) : DropMessage(msg)

ServerStep(i) ==
    \/ Timeout(i)
    \/ \E msg \in BagToSet(net) : HandleRequestVoteRequest(i, msg)
    \/ \E msg \in BagToSet(net) : HandleRequestVoteResponse(i, msg)
    \/ BecomeLeader(i)
    \/ \E j \in Server : LeaderSendAppendEntries(i, j)
    \/ \E msg \in BagToSet(net) : HandleAppendEntriesRequest(i, msg)
    \/ \E msg \in BagToSet(net) : HandleAppendEntriesResponse(i, msg)
    \/ LeaderAdvanceCommitIndex(i)
    \/ ApplyToStateMachine(i)
    \/ \E msg \in BagToSet(net) : HandleClientRequest(i, msg)

ClientStep(c) ==
    \/ \E srv \in Server : ClientRequest(c, srv)
    \/ \E msg \in BagToSet(net) : HandleClientResponse(c, msg)

Fairness ==
    /\ \A i \in Server : WF_vars(ServerStep(i))
    /\ \A c \in Client : WF_vars(ClientStep(c))

Spec == Init /\ [][Next]_vars /\ Fairness

====
