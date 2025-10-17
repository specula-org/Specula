---- MODULE raftkvs ----
EXTENDS TLC, Sequences, Naturals, FiniteSets, Bags

CONSTANTS
    NumServers,
    NumClients,
    Key,
    Value,
    Nil

ASSUME NumServers \in Nat /\ NumServers > 0
ASSUME NumClients \in Nat

Server == 1..NumServers
Client == (NumServers + 1)..(NumServers + NumClients)
Node == Server \union Client

StateVal == {"follower", "candidate", "leader"}
CmdType == {"put", "get"}
Request == { [type |-> "put", key |-> k, value |-> v, idx |-> i] : k \in Key, v \in Value, i \in Nat}
           \cup
           { [type |-> "get", key |-> k, idx |-> i] : k \in Key, i \in Nat}

VARIABLES
    net,
    state,
    currentTerm,
    votedFor,
    log,
    commitIndex,
    nextIndex,
    matchIndex,
    votesGranted,
    sm,
    leaderTimeout,
    netEnabled

vars == <<net, state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votesGranted, sm, leaderTimeout, netEnabled>>

\* Helper operators
IsQuorum(S) == Cardinality(S) * 2 > NumServers
LastTerm(lg) == IF Len(lg) = 0 THEN 0 ELSE lg[Len(lg)]["term"]
LastIndex(lg) == Len(lg)

\* Message type constructors
RequestVoteRequestMsg(term, lastLogTerm, lastLogIndex, src, dest) ==
    [mtype |-> "rvq", mterm |-> term, mlastLogTerm |-> lastLogTerm, mlastLogIndex |-> lastLogIndex, msource |-> src, mdest |-> dest]

RequestVoteResponseMsg(term, voteGranted, src, dest) ==
    [mtype |-> "rvp", mterm |-> term, mvoteGranted |-> voteGranted, msource |-> src, mdest |-> dest]

AppendEntriesRequestMsg(term, prevLogIndex, prevLogTerm, entries, commitIdx, src, dest) ==
    [mtype |-> "apq", mterm |-> term, mprevLogIndex |-> prevLogIndex, mprevLogTerm |-> prevLogTerm, mentries |-> entries, mcommitIndex |-> commitIdx, msource |-> src, mdest |-> dest]

AppendEntriesResponseMsg(term, success, matchIdx, src, dest) ==
    [mtype |-> "app", mterm |-> term, msuccess |-> success, mmatchIndex |-> matchIdx, msource |-> src, mdest |-> dest]

ClientPutRequestMsg(cmd, src, dest) ==
    [mtype |-> "cpq", mcmd |-> cmd, msource |-> src, mdest |-> dest]

ClientGetRequestMsg(cmd, src, dest) ==
    [mtype |-> "cgq", mcmd |-> cmd, msource |-> src, mdest |-> dest]

ClientPutResponseMsg(success, response, leaderHint, src, dest) ==
    [mtype |-> "cpp", msuccess |-> success, mresponse |-> response, mleaderHint |-> leaderHint, msource |-> src, mdest |-> dest]

ClientGetResponseMsg(success, response, leaderHint, src, dest) ==
    [mtype |-> "cgp", msuccess |-> success, mresponse |-> response, mleaderHint |-> leaderHint, msource |-> src, mdest |-> dest]

\* Initial state
Init ==
    /\ net = {}
    /\ state = [i \in Server |-> "follower"]
    /\ currentTerm = [i \in Server |-> 0]
    /\ votedFor = [i \in Server |-> Nil]
    /\ log = [i \in Server |-> << >>]
    /\ commitIndex = [i \in Server |-> 0]
    /\ nextIndex = [i \in Server |-> [j \in Server |-> 1]]
    /\ matchIndex = [i \in Server |-> [j \in Server |-> 0]]
    /\ votesGranted = [i \in Server |-> {}]
    /\ sm = [i \in Server |-> [k \in Key |-> Nil]]
    /\ leaderTimeout = [i \in Server |-> FALSE]
    /\ netEnabled = [i \in Node |-> TRUE]

\* Actions

\* Non-deterministically trigger a timeout for a follower.
SetTimeout(i) ==
    /\ state[i] = "follower"
    /\ ~leaderTimeout[i]
    /\ leaderTimeout' = [leaderTimeout EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<net, state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votesGranted, sm, netEnabled>>

\* A follower times out and starts an election.
TimeoutAndStartElection(i) ==
    /\ state[i] = "follower"
    /\ leaderTimeout[i]
    /\ netEnabled[i]
    /\ state' = [state EXCEPT ![i] = "candidate"]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
    /\ votedFor' = [votedFor EXCEPT ![i] = i]
    /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}]
    /\ leaderTimeout' = [leaderTimeout EXCEPT ![i] = FALSE]
    /\ net' = net \union { RequestVoteRequestMsg(currentTerm[i] + 1, LastTerm(log[i]), LastIndex(log[i]), i, j) : j \in Server \ {i} }
    /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, sm, netEnabled>>

\* A candidate becomes leader after receiving a majority of votes.
BecomeLeader(i) ==
    /\ state[i] = "candidate"
    /\ netEnabled[i]
    /\ IsQuorum(votesGranted[i])
    /\ state' = [state EXCEPT ![i] = "leader"]
    /\ nextIndex' = [nextIndex EXCEPT ![i] = [j \in Server |-> LastIndex(log[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ UNCHANGED <<net, currentTerm, votedFor, log, commitIndex, votesGranted, sm, leaderTimeout, netEnabled>>

\* A leader sends AppendEntries RPCs (including heartbeats) to its followers.
LeaderSendAppendEntries(i, j) ==
    /\ state[i] = "leader"
    /\ j \in Server \ {i}
    /\ netEnabled[i]
    /\ LET prevLogIdx == nextIndex[i][j] - 1
           prevLogTerm == IF prevLogIdx > 0 THEN log[i][prevLogIdx]["term"] ELSE 0
           entries == SubSeq(log[i], nextIndex[i][j], Len(log[i]))
    IN net' = net \union { AppendEntriesRequestMsg(currentTerm[i], prevLogIdx, prevLogTerm, entries, commitIndex[i], i, j) }
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votesGranted, sm, leaderTimeout, netEnabled>>

\* A leader advances its commit index after an entry is replicated on a majority.
AdvanceCommitIndex(i) ==
    /\ state[i] = "leader"
    /\ netEnabled[i]
    /\ LET possible_N == { n \in (commitIndex[i]+1)..Len(log[i]) |
                            /\ log[i][n]["term"] = currentTerm[i]
                            /\ IsQuorum({i} \union {k \in Server | matchIndex[i][k] >= n}) }
    IN \/ /\ possible_N # {}
          /\ LET newCommitIndex == CHOOSE n \in possible_N : \A m \in possible_N : n >= m
                 applyRange == (commitIndex[i] + 1)..newCommitIndex
                 newlyCommitted == {idx \in applyRange | log[i][idx]["cmd"]["type"] = "put"}
                 updated_sm == [sm EXCEPT ![i] = [k \in Key |->
                                     LET updates = {log[i][idx]["cmd"]["value"] : idx \in newlyCommitted | log[i][idx]["cmd"]["key"] = k}
                                     IN IF updates # {} THEN CHOOSE v \in updates : TRUE ELSE sm[i][k]]]
                 clientResponses ==
                     { IF log[i][idx]["cmd"]["type"] = "put"
                       THEN ClientPutResponseMsg(TRUE, [idx |-> log[i][idx]["cmd"]["idx"], key |-> log[i][idx]["cmd"]["key"]], i, i, log[i][idx]["client"])
                       ELSE ClientGetResponseMsg(TRUE, [idx |-> log[i][idx]["cmd"]["idx"], key |-> log[i][idx]["cmd"]["key"], value |-> sm[i][log[i][idx]["cmd"]["key"]], ok |-> TRUE], i, i, log[i][idx]["client"])
                       : idx \in applyRange }
          IN /\ commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
             /\ sm' = updated_sm
             /\ net' = net \union clientResponses
       \/ /\ possible_N = {}
          /\ UNCHANGED <<commitIndex, sm, net>>
    /\ UNCHANGED <<state, currentTerm, votedFor, log, nextIndex, matchIndex, votesGranted, leaderTimeout, netEnabled>>

\* A server receives a message.
Receive(i, m) ==
    /\ m \in net
    /\ m["mdest"] = i
    /\ netEnabled[i]
    /\ LET
        \* If message's term is higher, update term and become follower.
        UpdateTermStep(varsTuple) ==
            LET s == varsTuple[1]
                ct == varsTuple[2]
                vf == varsTuple[3]
            IN IF m["mterm"] > ct[i]
               THEN <<[s EXCEPT ![i] = "follower"],
                      [ct EXCEPT ![i] = m["mterm"]],
                      [vf EXCEPT ![i] = Nil]>>
               ELSE <<s, ct, vf>>
        _updated_vars == UpdateTermStep(<<state, currentTerm, votedFor>>)
        next_state == _updated_vars[1]
        next_currentTerm == _updated_vars[2]
        next_votedFor == _updated_vars[3]
    IN
        \/ /\ m["mtype"] = "rvq"
           /\ LET logIsOk == \/ m["mlastLogTerm"] > LastTerm(log[i])
                             \/ /\ m["mlastLogTerm"] = LastTerm(log[i])
                                /\ m["mlastLogIndex"] >= LastIndex(log[i])
                  grantVote == /\ m["mterm"] = next_currentTerm[i]
                               /\ logIsOk
                               /\ next_votedFor[i] \in {Nil, m["msource"]}
           IN /\ IF grantVote
                 THEN votedFor' = [next_votedFor EXCEPT ![i] = m["msource"]]
                 ELSE votedFor' = next_votedFor
              /\ net' = (net \ {m}) \union {RequestVoteResponseMsg(next_currentTerm[i], grantVote, i, m["msource"])}
              /\ state' = next_state
              /\ currentTerm' = next_currentTerm
              /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, votesGranted, sm, leaderTimeout, netEnabled>>

        \/ /\ m["mtype"] = "rvp"
           /\ IF m["mterm"] = next_currentTerm[i] /\ state[i] = "candidate"
              THEN /\ IF m["mvoteGranted"]
                      THEN votesGranted' = [votesGranted EXCEPT ![i] = votesGranted[i] \union {m["msource"]}]
                      ELSE votesGranted' = votesGranted
                   /\ UNCHANGED <<votedFor, log, commitIndex, nextIndex, matchIndex, sm, leaderTimeout>>
              ELSE /\ UNCHANGED <<votedFor, log, commitIndex, nextIndex, matchIndex, votesGranted, sm, leaderTimeout>>
           /\ net' = net \ {m}
           /\ state' = next_state
           /\ currentTerm' = next_currentTerm
           /\ UNCHANGED <<netEnabled>>

        \/ /\ m["mtype"] = "apq"
           /\ IF m["mterm"] < next_currentTerm[i]
              THEN /\ net' = (net \ {m}) \union {AppendEntriesResponseMsg(next_currentTerm[i], FALSE, 0, i, m["msource"])}
                   /\ state' = next_state
                   /\ currentTerm' = next_currentTerm
                   /\ UNCHANGED <<votedFor, log, commitIndex, nextIndex, matchIndex, votesGranted, sm, leaderTimeout, netEnabled>>
              ELSE /\ leaderTimeout' = [leaderTimeout EXCEPT ![i] = FALSE]
                   /\ LET logOK == \/ m["mprevLogIndex"] = 0
                                   \/ /\ m["mprevLogIndex"] > 0
                                      /\ m["mprevLogIndex"] <= Len(log[i])
                                      /\ log[i][m["mprevLogIndex"]]["term"] = m["mprevLogTerm"]
                   IN IF logOK
                      THEN LET newLog == Append(SubSeq(log[i], 1, m["mprevLogIndex"]), m["mentries"])
                               newCommitIndex == MinOfSet({m["mcommitIndex"], Len(newLog)})
                               applyRange == (commitIndex[i] + 1)..newCommitIndex
                               newlyCommitted == {idx \in applyRange | newLog[idx]["cmd"]["type"] = "put"}
                               updated_sm == [sm EXCEPT ![i] = [k \in Key |->
                                                   LET updates = {newLog[idx]["cmd"]["value"] : idx \in newlyCommitted | newLog[idx]["cmd"]["key"] = k}
                                                   IN IF updates # {} THEN CHOOSE v \in updates : TRUE ELSE sm[i][k]]]
                           IN /\ log' = [log EXCEPT ![i] = newLog]
                              /\ commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
                              /\ sm' = updated_sm
                              /\ net' = (net \ {m}) \union {AppendEntriesResponseMsg(next_currentTerm[i], TRUE, m["mprevLogIndex"] + Len(m["mentries"]), i, m["msource"])}
                      ELSE /\ net' = (net \ {m}) \union {AppendEntriesResponseMsg(next_currentTerm[i], FALSE, 0, i, m["msource"])}
                           /\ UNCHANGED <<log, commitIndex, sm>>
                   /\ state' = next_state
                   /\ currentTerm' = next_currentTerm
                   /\ UNCHANGED <<votedFor, nextIndex, matchIndex, votesGranted, netEnabled>>

        \/ /\ m["mtype"] = "app"
           /\ IF m["mterm"] = next_currentTerm[i] /\ state[i] = "leader"
              THEN /\ IF m["msuccess"]
                      THEN /\ matchIndex' = [matchIndex EXCEPT ![i][m["msource"]] = m["mmatchIndex"]]
                           /\ nextIndex' = [nextIndex EXCEPT ![i][m["msource"]] = m["mmatchIndex"] + 1]
                      ELSE /\ nextIndex' = [nextIndex EXCEPT ![i][m["msource"]] = MaxOfSet({nextIndex[i][m["msource"]] - 1, 1})]
                           /\ UNCHANGED <<matchIndex>>
                   /\ UNCHANGED <<votedFor, log, commitIndex, votesGranted, sm, leaderTimeout>>
              ELSE /\ UNCHANGED <<votedFor, log, commitIndex, nextIndex, matchIndex, votesGranted, sm, leaderTimeout>>
           /\ net' = net \ {m}
           /\ state' = next_state
           /\ currentTerm' = next_currentTerm
           /\ UNCHANGED <<netEnabled>>

        \/ /\ m["mtype"] \in {"cpq", "cgq"}
           /\ IF state[i] = "leader"
              THEN /\ LET entry == [term |-> currentTerm[i], cmd |-> m["mcmd"], client |-> m["msource"]]
                   IN log' = [log EXCEPT ![i] = Append(log[i], entry)]
                   /\ net' = net \ {m}
                   /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, nextIndex, matchIndex, votesGranted, sm, leaderTimeout, netEnabled>>
              ELSE /\ LET leaderHint == IF state[i] = "follower" /\ votedFor[i] # Nil THEN votedFor[i] ELSE Nil
                       respType == IF m["mtype"] = "cpq" THEN ClientPutResponseMsg ELSE ClientGetResponseMsg
                   IN net' = (net \ {m}) \union {respType(FALSE, m["mcmd"], leaderHint, i, m["msource"])}
                   /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votesGranted, sm, leaderTimeout, netEnabled>>

\* A client sends a request.
ClientRequest(c, cmd) ==
    /\ c \in Client
    /\ netEnabled[c]
    /\ \E s \in Server:
        /\ LET reqType == IF cmd["type"] = "put" THEN ClientPutRequestMsg ELSE ClientGetRequestMsg
        IN net' = net \union {reqType(cmd, c, s)}
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votesGranted, sm, leaderTimeout, netEnabled>>

\* A node crashes.
NodeCrash(i) ==
    /\ i \in Server
    /\ netEnabled[i]
    /\ netEnabled' = [netEnabled EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<net, state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votesGranted, sm, leaderTimeout>>

\* A message is lost.
DropMessage(m) ==
    /\ m \in net
    /\ net' = net \ {m}
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votesGranted, sm, leaderTimeout, netEnabled>>

Next ==
    \/ \E i \in Server:
        \/ SetTimeout(i)
        \/ TimeoutAndStartElection(i)
        \/ BecomeLeader(i)
        \/ (\E j \in Server: LeaderSendAppendEntries(i, j))
        \/ AdvanceCommitIndex(i)
        \/ (\E m \in net: Receive(i, m))
        \/ NodeCrash(i)
    \/ \E c \in Client, cmd \in Request: ClientRequest(c, cmd)
    \/ \E m \in net: DropMessage(m)

ServerProc(i) ==
    \/ SetTimeout(i)
    \/ TimeoutAndStartElection(i)
    \/ BecomeLeader(i)
    \/ (\E j \in Server: LeaderSendAppendEntries(i, j))
    \/ AdvanceCommitIndex(i)
    \/ (\E m \in net: Receive(i, m))
    \/ NodeCrash(i)

ClientProc(c) == \E cmd \in Request: ClientRequest(c, cmd)

Fairness ==
    /\ \A i \in Server: WF_vars(ServerProc(i))
    /\ \A c \in Client: WF_vars(ClientProc(c))

Spec == Init /\ [][Next]_vars /\ Fairness

====