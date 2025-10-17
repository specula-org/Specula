---- MODULE raftkvs ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS
    NumServers,
    NumClients,
    AllStrings,
    Commands,
    Nil

ASSUME NumServers \in Nat /\ NumServers > 0
ASSUME NumClients \in Nat
ASSUME Nil \notin (1..(NumServers + NumClients))

Server == 1..NumServers
Client == (NumServers + 1)..(NumServers + NumClients)
Node == Server \cup Client

Quorum == (NumServers \div 2) + 1
IsQuorum(S) == Cardinality(S) >= Quorum

StateVal == {"Follower", "Candidate", "Leader"}
MsgType ==
    { "RequestVoteRequest", "RequestVoteResponse",
      "AppendEntriesRequest", "AppendEntriesResponse",
      "ClientGetRequest", "ClientPutRequest",
      "ClientGetResponse", "ClientPutResponse" }

LastLogIndex(log) == Len(log)
LastLogTerm(log) == IF Len(log) = 0 THEN 0 ELSE log[Len(log)]["term"]

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
    leaderHint,
    clientNextReqId,
    clientResponses

vars == << net, state, currentTerm, votedFor, log, commitIndex, lastApplied,
           votesGranted, nextIndex, matchIndex, sm, leaderHint,
           clientNextReqId, clientResponses >>

Init ==
    /\ net = [n \in Node |-> EmptyBag]
    /\ state = [s \in Server |-> "Follower"]
    /\ currentTerm = [s \in Server |-> 0]
    /\ votedFor = [s \in Server |-> Nil]
    /\ log = [s \in Server |-> << >>]
    /\ commitIndex = [s \in Server |-> 0]
    /\ lastApplied = [s \in Server |-> 0]
    /\ votesGranted = [s \in Server |-> {}]
    /\ nextIndex = [s \in Server |-> [j \in Server |-> 1]]
    /\ matchIndex = [s \in Server |-> [j \in Server |-> 0]]
    /\ sm = [s \in Server |-> [k \in AllStrings |-> ""]]
    /\ leaderHint = [c \in Client |-> Nil]
    /\ clientNextReqId = [c \in Client |-> 1]
    /\ clientResponses = [c \in Client |-> [i \in {} |-> ""]]

\* A follower or candidate times out and starts an election.
TimeoutAndStartElection(i) ==
    /\ state[i] \in {"Follower", "Candidate"}
    /\ state' = [state EXCEPT ![i] = "Candidate"]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
    /\ votedFor' = [votedFor EXCEPT ![i] = i]
    /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}]
    /\ LET OutgoingMessages ==
            { [ type       |-> "RequestVoteRequest",
                term       |-> currentTerm'[i],
                source     |-> i,
                dest       |-> j,
                payload    |-> [ lastLogIndex |-> LastLogIndex(log[i]),
                                 lastLogTerm  |-> LastLogTerm(log[i]) ]
              ] : j \in Server \ {i} }
       IN net' = [n \in Node |-> BagUnion(net[n], SetToBag({m \in OutgoingMessages | m["dest"] = n}))]
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, sm, leaderHint, clientNextReqId, clientResponses>>

\* A server receives a RequestVoteRequest.
HandleRequestVoteRequest(i) ==
    \E msg \in BagToSet(net[i]):
        /\ msg["type"] = "RequestVoteRequest"
        /\ LET newNet == BagRemove(net[i], msg)
               mterm == msg["term"]
               candidateId == msg["source"]
               candidateLogIndex == msg["payload"]["lastLogIndex"]
               candidateLogTerm == msg["payload"]["lastLogTerm"]
           IN
           IF mterm > currentTerm[i] THEN
                LET logIsUpToDate ==
                        \/ candidateLogTerm > LastLogTerm(log[i])
                        \/ (candidateLogTerm = LastLogTerm(log[i]) /\
                            candidateLogIndex >= LastLogIndex(log[i]))
                   grantVote == logIsUpToDate
                IN
                /\ state' = [state EXCEPT ![i] = "Follower"]
                /\ currentTerm' = [currentTerm EXCEPT ![i] = mterm]
                /\ votedFor' = [votedFor EXCEPT ![i] = IF grantVote THEN candidateId ELSE Nil]
                /\ LET resp == [ type |-> "RequestVoteResponse",
                                term |-> mterm,
                                source |-> i,
                                dest |-> candidateId,
                                payload |-> [ voteGranted |-> grantVote ] ]
                   IN net' = [net EXCEPT ![i] = newNet, ![candidateId] = BagUnion(net[candidateId], {resp})]
                /\ UNCHANGED <<log, commitIndex, lastApplied, votesGranted, nextIndex, matchIndex, sm, leaderHint, clientNextReqId, clientResponses>>
           ELSE
                LET logIsUpToDate ==
                        \/ candidateLogTerm > LastLogTerm(log[i])
                        \/ (candidateLogTerm = LastLogTerm(log[i]) /\
                            candidateLogIndex >= LastLogIndex(log[i]))
                   grantVote ==
                      mterm = currentTerm[i] /\
                      (votedFor[i] = Nil \/ votedFor[i] = candidateId) /\
                      logIsUpToDate
                IN
                /\ (IF grantVote THEN
                     votedFor' = [votedFor EXCEPT ![i] = candidateId]
                   ELSE
                     UNCHANGED votedFor)
                /\ LET resp == [ type |-> "RequestVoteResponse",
                                term |-> currentTerm[i],
                                source |-> i,
                                dest |-> candidateId,
                                payload |-> [ voteGranted |-> grantVote ] ]
                   IN net' = [net EXCEPT ![i] = newNet, ![candidateId] = BagUnion(net[candidateId], {resp})]
                /\ UNCHANGED <<state, currentTerm, log, commitIndex, lastApplied, votesGranted, nextIndex, matchIndex, sm, leaderHint, clientNextReqId, clientResponses>>

\* A candidate receives a RequestVoteResponse.
HandleRequestVoteResponse(i) ==
    \E msg \in BagToSet(net[i]):
        /\ msg["type"] = "RequestVoteResponse"
        /\ LET newNet == BagRemove(net[i], msg)
               mterm == msg["term"]
               voter == msg["source"]
               granted == msg["payload"]["voteGranted"]
           IN
           /\ net' = [net EXCEPT ![i] = newNet]
           /\ IF mterm > currentTerm[i] THEN
                /\ state' = [state EXCEPT ![i] = "Follower"]
                /\ currentTerm' = [currentTerm EXCEPT ![i] = mterm]
                /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
                /\ UNCHANGED <<log, commitIndex, lastApplied, votesGranted, nextIndex, matchIndex, sm, leaderHint, clientNextReqId, clientResponses>>
           ELSE IF mterm = currentTerm[i] /\ state[i] = "Candidate" THEN
                /\ (IF granted THEN
                     LET newVotes == votesGranted[i] \cup {voter} IN
                     /\ votesGranted' = [votesGranted EXCEPT ![i] = newVotes]
                     /\ (IF IsQuorum(newVotes) THEN
                          /\ state' = [state EXCEPT ![i] = "Leader"]
                          /\ nextIndex' = [nextIndex EXCEPT ![i] = [j \in Server |-> LastLogIndex(log[i]) + 1]]
                          /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
                        ELSE
                          UNCHANGED <<state, nextIndex, matchIndex>>)
                   ELSE
                     UNCHANGED <<state, votesGranted, nextIndex, matchIndex>>)
                /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied, sm, leaderHint, clientNextReqId, clientResponses>>
           ELSE
                UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, votesGranted, nextIndex, matchIndex, sm, leaderHint, clientNextReqId, clientResponses>>

\* A leader sends AppendEntries (can be heartbeat).
LeaderSendAppendEntries(i, j) ==
    /\ state[i] = "Leader"
    /\ j \in Server \ {i}
    /\ LET ni == nextIndex[i][j]
           prevLogIndex == ni - 1
           prevLogTerm == IF prevLogIndex > 0 THEN log[i][prevLogIndex]["term"] ELSE 0
           entries == SubSeq(log[i], ni, Len(log[i]))
           msg == [ type |-> "AppendEntriesRequest",
                    term |-> currentTerm[i],
                    source |-> i,
                    dest |-> j,
                    payload |-> [ prevLogIndex |-> prevLogIndex,
                                  prevLogTerm |-> prevLogTerm,
                                  entries |-> entries,
                                  leaderCommit |-> commitIndex[i] ] ]
       IN net' = [net EXCEPT ![j] = BagUnion(net[j], {msg})]
    /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, lastApplied,
                    votesGranted, nextIndex, matchIndex, sm, leaderHint,
                    clientNextReqId, clientResponses >>

\* A server receives an AppendEntriesRequest.
HandleAppendEntriesRequest(i) ==
    \E msg \in BagToSet(net[i]):
        /\ msg["type"] = "AppendEntriesRequest"
        /\ LET newNet == BagRemove(net[i], msg)
               mterm == msg["term"]
               leaderId == msg["source"]
               pIndex == msg["payload"]["prevLogIndex"]
               pTerm == msg["payload"]["prevLogTerm"]
               entries == msg["payload"]["entries"]
               lCommit == msg["payload"]["leaderCommit"]
           IN
           IF mterm > currentTerm[i] THEN
                /\ state' = [state EXCEPT ![i] = "Follower"]
                /\ currentTerm' = [currentTerm EXCEPT ![i] = mterm]
                /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
                /\ LET resp == [ type |-> "AppendEntriesResponse", term |-> mterm, source |-> i, dest |-> leaderId, payload |-> [ success |-> FALSE, matchIndex |-> 0 ] ]
                   IN net' = [net EXCEPT ![i] = newNet, ![leaderId] = BagUnion(net[leaderId], {resp})]
                /\ UNCHANGED <<log, commitIndex, lastApplied, votesGranted, nextIndex, matchIndex, sm, leaderHint, clientNextReqId, clientResponses>>
           ELSE
                LET success ==
                         mterm = currentTerm[i] /\
                         (pIndex = 0 \/
                          (pIndex <= Len(log[i]) /\ log[i][pIndex]["term"] = pTerm))
                IN
                /\ (IF mterm = currentTerm[i] THEN
                     /\ state' = [state EXCEPT ![i] = "Follower"]
                     /\ (IF success THEN
                          /\ log' = [log EXCEPT ![i] = Append(SubSeq(log[i], 1, pIndex), entries)]
                          /\ (IF lCommit > commitIndex[i] THEN
                               commitIndex' = [commitIndex EXCEPT ![i] = Min({lCommit, LastLogIndex(log'[i])})]
                             ELSE
                               UNCHANGED commitIndex)
                        ELSE
                          UNCHANGED <<log, commitIndex>>)
                   ELSE
                     UNCHANGED <<state, log, commitIndex>>)
                /\ LET resp == [ type |-> "AppendEntriesResponse",
                                 term |-> currentTerm[i],
                                 source |-> i,
                                 dest |-> leaderId,
                                 payload |-> [ success |-> success,
                                               matchIndex |-> IF success THEN pIndex + Len(entries) ELSE 0 ] ]
                   IN net' = [net EXCEPT ![i] = newNet, ![leaderId] = BagUnion(net[leaderId], {resp})]
                /\ UNCHANGED <<currentTerm, votedFor, lastApplied, votesGranted, nextIndex, matchIndex, sm, leaderHint, clientNextReqId, clientResponses>>

\* A leader receives an AppendEntriesResponse.
HandleAppendEntriesResponse(i) ==
    \E msg \in BagToSet(net[i]):
        /\ msg["type"] = "AppendEntriesResponse"
        /\ LET newNet == BagRemove(net[i], msg)
               mterm == msg["term"]
               follower == msg["source"]
               success == msg["payload"]["success"]
               mIndex == msg["payload"]["matchIndex"]
           IN
           /\ net' = [net EXCEPT ![i] = newNet]
           /\ IF mterm > currentTerm[i] THEN
                /\ state' = [state EXCEPT ![i] = "Follower"]
                /\ currentTerm' = [currentTerm EXCEPT ![i] = mterm]
                /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
                /\ UNCHANGED <<log, commitIndex, lastApplied, votesGranted, nextIndex, matchIndex, sm, leaderHint, clientNextReqId, clientResponses>>
           ELSE IF mterm = currentTerm[i] /\ state[i] = "Leader" THEN
                /\ (IF success THEN
                     /\ nextIndex' = [nextIndex EXCEPT ![i] = [nextIndex[i] EXCEPT ![follower] = mIndex + 1]]
                     /\ matchIndex' = [matchIndex EXCEPT ![i] = [matchIndex[i] EXCEPT ![follower] = mIndex]]
                   ELSE
                     /\ nextIndex' = [nextIndex EXCEPT ![i] = [nextIndex[i] EXCEPT ![follower] = Max({1, nextIndex[i][follower] - 1})]]
                     /\ UNCHANGED matchIndex)
                /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, votesGranted, sm, leaderHint, clientNextReqId, clientResponses>>
           ELSE
                UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, votesGranted, nextIndex, matchIndex, sm, leaderHint, clientNextReqId, clientResponses>>

\* A leader advances its commit index.
LeaderAdvanceCommitIndex(i) ==
    /\ state[i] = "Leader"
    /\ LET PossibleCommits ==
            { N \in (commitIndex[i]+1)..LastLogIndex(log[i]) :
                /\ log[i][N]["term"] = currentTerm[i]
                /\ IsQuorum({j \in Server : matchIndex[i][j] >= N} \cup {i})
            }
       IN IF PossibleCommits /= {} THEN
            commitIndex' = [commitIndex EXCEPT ![i] = Max(PossibleCommits)]
          ELSE
            UNCHANGED commitIndex
    /\ UNCHANGED << net, state, currentTerm, votedFor, log, lastApplied,
                    votesGranted, nextIndex, matchIndex, sm, leaderHint,
                    clientNextReqId, clientResponses >>

\* Any server applies committed entries to its state machine.
ApplyCommittedEntries(i) ==
    /\ commitIndex[i] > lastApplied[i]
    /\ LET newLastApplied == lastApplied[i] + 1
           entryToApply == log[i][newLastApplied]
           cmd == entryToApply["cmd"]
       IN
       /\ lastApplied' = [lastApplied EXCEPT ![i] = newLastApplied]
       /\ (IF cmd["type"] = "put" THEN
            sm' = [sm EXCEPT ![i] = [sm[i] EXCEPT ![cmd["key"]] = cmd["value"]]]
          ELSE
            UNCHANGED sm)
       /\ (IF state[i] = "Leader" THEN
            LET client == entryToApply["client"]
                reqId == entryToApply["reqId"]
                respPayload ==
                    IF cmd["type"] = "put" THEN
                        [ success |-> TRUE, value |-> Nil ]
                    ELSE \* "get"
                        [ success |-> TRUE, value |-> sm[i][cmd["key"]] ]
                resp == [ type |-> IF cmd["type"] = "put" THEN "ClientPutResponse" ELSE "ClientGetResponse",
                          term |-> 0,
                          source |-> i,
                          dest |-> client,
                          payload |-> [ reqId |-> reqId, resp |-> respPayload, leaderHint |-> i ] ]
            IN net' = [net EXCEPT ![client] = BagUnion(net[client], {resp})]
          ELSE
            UNCHANGED net)
    /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex,
                    votesGranted, nextIndex, matchIndex, leaderHint,
                    clientNextReqId, clientResponses >>

\* A client sends a request.
ClientRequest(c, cmd) ==
    /\ cmd \in Commands
    /\ LET reqId == clientNextReqId[c]
           target == IF leaderHint[c] = Nil THEN CHOOSE s \in Server : TRUE ELSE leaderHint[c]
           msg == [ type |-> IF cmd["type"] = "put" THEN "ClientPutRequest" ELSE "ClientGetRequest",
                    term |-> 0,
                    source |-> c,
                    dest |-> target,
                    payload |-> [ cmd |-> cmd, reqId |-> reqId ] ]
       IN net' = [net EXCEPT ![target] = BagUnion(net[target], {msg})]
    /\ clientNextReqId' = [clientNextReqId EXCEPT ![c] = reqId + 1]
    /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, lastApplied,
                    votesGranted, nextIndex, matchIndex, sm, leaderHint, clientResponses >>

\* A server handles a client request.
ServerHandleClientRequest(i) ==
    \E msg \in BagToSet(net[i]):
        /\ msg["type"] \in {"ClientPutRequest", "ClientGetRequest"}
        /\ LET newNet == BagRemove(net[i], msg)
               client == msg["source"]
               cmd == msg["payload"]["cmd"]
               reqId == msg["payload"]["reqId"]
           IN
           IF state[i] /= "Leader" THEN
                LET maybeLeader == {l \in Server | state[l] = "Leader"}
                   resp == [ type |-> IF cmd["type"] = "put" THEN "ClientPutResponse" ELSE "ClientGetResponse",
                             term |-> 0,
                             source |-> i,
                             dest |-> client,
                             payload |-> [ reqId |-> reqId,
                                           resp |-> [ success |-> FALSE, value |-> Nil ],
                                           leaderHint |-> IF maybeLeader = {} THEN Nil ELSE CHOOSE l \in maybeLeader : TRUE ] ]
                IN
                /\ net' = [net EXCEPT ![i] = newNet, ![client] = BagUnion(net[client], {resp})]
                /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, lastApplied,
                                votesGranted, nextIndex, matchIndex, sm, leaderHint,
                                clientNextReqId, clientResponses >>
           ELSE
                /\ LET newEntry == [ term |-> currentTerm[i],
                                     cmd |-> cmd,
                                     client |-> client,
                                     reqId |-> reqId ]
                   IN log' = [log EXCEPT ![i] = Append(log[i], newEntry)]
                /\ net' = [net EXCEPT ![i] = newNet]
                /\ UNCHANGED << state, currentTerm, votedFor, commitIndex, lastApplied,
                                votesGranted, nextIndex, matchIndex, sm, leaderHint,
                                clientNextReqId, clientResponses >>

\* A client receives a response.
ClientHandleResponse(c) ==
    \E msg \in BagToSet(net[c]):
        /\ msg["type"] \in {"ClientPutResponse", "ClientGetResponse"}
        /\ LET newNet == BagRemove(net[c], msg)
               reqId == msg["payload"]["reqId"]
               resp == msg["payload"]["resp"]
               hint == msg["payload"]["leaderHint"]
           IN
           /\ net' = [net EXCEPT ![c] = newNet]
           /\ (IF resp["success"] THEN
                clientResponses' = [clientResponses EXCEPT ![c] = [clientResponses[c] EXCEPT ![reqId] = resp]]
              ELSE
                UNCHANGED clientResponses)
           /\ leaderHint' = [leaderHint EXCEPT ![c] = hint]
           /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, lastApplied,
                           votesGranted, nextIndex, matchIndex, sm, clientNextReqId >>

\* Network can lose messages.
DropMessage(n) ==
    \E msg \in BagToSet(net[n]):
        /\ net' = [net EXCEPT ![n] = BagRemove(net[n], msg)]
        /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, lastApplied,
                        votesGranted, nextIndex, matchIndex, sm, leaderHint,
                        clientNextReqId, clientResponses >>

ServerAction(i) ==
    \/ TimeoutAndStartElection(i)
    \/ HandleRequestVoteRequest(i)
    \/ HandleRequestVoteResponse(i)
    \/ (\E j \in Server \ {i} : LeaderSendAppendEntries(i, j))
    \/ HandleAppendEntriesRequest(i)
    \/ HandleAppendEntriesResponse(i)
    \/ LeaderAdvanceCommitIndex(i)
    \/ ApplyCommittedEntries(i)
    \/ ServerHandleClientRequest(i)

ClientAction(c) ==
    \/ (\E cmd \in Commands : ClientRequest(c, cmd))
    \/ ClientHandleResponse(c)

NetworkAction(n) == DropMessage(n)

Next ==
    \/ (\E i \in Server : ServerAction(i))
    \/ (\E c \in Client : ClientAction(c))
    \/ (\E n \in Node : NetworkAction(n))

Fairness ==
    /\ \A i \in Server : WF_vars(ServerAction(i))
    /\ \A c \in Client : WF_vars(ClientAction(c))
    /\ \A n \in Node : WF_vars(NetworkAction(n))

Spec == Init /\ [][Next]_vars /\ Fairness

====
