---- MODULE raftkvs ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS
    NumServers,
    NumClients,
    AllStrings,
    Nil,
    DefaultValue

ASSUME
    /\ NumServers \in 1..Nat
    /\ NumClients \in 1..Nat
    /\ Nil = 0
    /\ AllStrings \subseteq STRING

Server == 1..NumServers
Client == (NumServers + 1)..(NumServers + NumClients)
Node == Server \cup Client
Term == Nat
Index == Nat
Value == AllStrings
Key == AllStrings
ServerState == {"follower", "candidate", "leader"}

RequestType == {"put", "get"}
ClientRequestRecord == [type: RequestType, key: Key, value: Value, idx: Nat, client: Client]
LogEntry == [term: Term, cmd: ClientRequestRecord]
Log == Seq(LogEntry)

MessageTypes ==
    {"rvq", "rvp", "apq", "app", "cpq", "cgq", "cpp", "cgp"}

IsQuorum(S) == Cardinality(S) * 2 > NumServers
LastTerm(lg) == IF Len(lg) = 0 THEN 0 ELSE lg[Len(lg)].term
LastIndex(lg) == Len(lg)

VARIABLES
    currentTerm,
    votedFor,
    state,
    log,
    commitIndex,
    lastApplied,
    leader,
    nextIndex,
    matchIndex,
    votesGranted,
    sm,
    net,
    netEnabled,
    client_leader_hint,
    client_req_idx,
    client_outstanding_req,
    client_responses

vars == <<
    currentTerm, votedFor, state, log, commitIndex, lastApplied, leader,
    nextIndex, matchIndex, votesGranted, sm, net, netEnabled,
    client_leader_hint, client_req_idx, client_outstanding_req, client_responses
>>

TypeOK ==
    /\ currentTerm \in [Server -> Term]
    /\ votedFor \in [Server -> Server \cup {Nil}]
    /\ state \in [Server -> ServerState]
    /\ log \in [Server -> Log]
    /\ commitIndex \in [Server -> Index]
    /\ lastApplied \in [Server -> Index]
    /\ leader \in [Server -> Server \cup {Nil}]
    /\ nextIndex \in [Server -> [Server -> Index]]
    /\ matchIndex \in [Server -> [Server -> Index]]
    /\ votesGranted \in [Server -> SUBSET Server]
    /\ sm \in [Server -> [Key -> Value]]
    /\ netEnabled \in [Server -> BOOLEAN]
    /\ client_leader_hint \in [Client -> Server \cup {Nil}]
    /\ client_req_idx \in [Client -> Nat]
    /\ \A c \in Client:
        LET r == client_outstanding_req[c] IN
        \/ r = [type |-> "none"]
        \/ r.type \in RequestType
    /\ client_responses \in Seq(Any)

Init ==
    /\ currentTerm = [i \in Server |-> 0]
    /\ votedFor = [i \in Server |-> Nil]
    /\ state = [i \in Server |-> "follower"]
    /\ log = [i \in Server |-> <<>>]
    /\ commitIndex = [i \in Server |-> 0]
    /\ lastApplied = [i \in Server |-> 0]
    /\ leader = [i \in Server |-> Nil]
    /\ nextIndex = [i \in Server |-> [j \in Server |-> 1]]
    /\ matchIndex = [i \in Server |-> [j \in Server |-> 0]]
    /\ votesGranted = [i \in Server |-> {}]
    /\ sm = [i \in Server |-> [k \in AllStrings |-> DefaultValue]]
    /\ net = EmptyBag
    /\ netEnabled = [i \in Server |-> TRUE]
    /\ client_leader_hint = [c \in Client |-> 1]
    /\ client_req_idx = [c \in Client |-> 0]
    /\ client_outstanding_req = [c \in Client |-> [type |-> "none"]]
    /\ client_responses = <<>>

\* Actions for servers

ServerTimeout(i) ==
    /\ i \in Server
    /\ netEnabled[i]
    /\ state[i] \in {"follower", "candidate"}
    /\ state' = [state EXCEPT ![i] = "candidate"]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = @ + 1]
    /\ votedFor' = [votedFor EXCEPT ![i] = i]
    /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}]
    /\ leader' = [leader EXCEPT ![i] = Nil]
    /\ LET
        newTerm == currentTerm[i] + 1
        request(j) == [
            mtype |-> "rvq",
            mterm |-> newTerm,
            mlastLogTerm |-> LastTerm(log[i]),
            mlastLogIndex |-> LastIndex(log[i]),
            msource |-> i,
            mdest |-> j
        ]
       IN net' = net (+) Bag({request(j) : j \in Server \ {i}})
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, sm, netEnabled,
                   client_leader_hint, client_req_idx, client_outstanding_req, client_responses>>

BecomeLeader(i) ==
    /\ i \in Server
    /\ netEnabled[i]
    /\ state[i] = "candidate"
    /\ IsQuorum(votesGranted[i])
    /\ state' = [state EXCEPT ![i] = "leader"]
    /\ leader' = [leader EXCEPT ![i] = i]
    /\ nextIndex' = [nextIndex EXCEPT ![i] = [j \in Server |-> LastIndex(log[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied, votesGranted, sm, net, netEnabled,
                   client_leader_hint, client_req_idx, client_outstanding_req, client_responses>>

LeaderSendAppendEntries(i, j) ==
    /\ i \in Server
    /\ j \in Server
    /\ netEnabled[i]
    /\ state[i] = "leader"
    /\ LET
        prevIdx == nextIndex[i][j] - 1
        prevTerm == IF prevIdx > 0 THEN log[i][prevIdx].term ELSE 0
        entries == SubSeq(log[i], nextIndex[i][j], Len(log[i]))
        msg == [
            mtype |-> "apq",
            mterm |-> currentTerm[i],
            mprevLogIndex |-> prevIdx,
            mprevLogTerm |-> prevTerm,
            mentries |-> entries,
            mcommitIndex |-> commitIndex[i],
            msource |-> i,
            mdest |-> j
        ]
       IN net' = net (+) Bag({msg})
    /\ UNCHANGED <<currentTerm, votedFor, state, log, commitIndex, lastApplied, leader,
                   nextIndex, matchIndex, votesGranted, sm, netEnabled,
                   client_leader_hint, client_req_idx, client_outstanding_req, client_responses>>

LeaderAdvanceCommitIndex(i) ==
    /\ i \in Server
    /\ netEnabled[i]
    /\ state[i] = "leader"
    /\ LET
        \* Find the highest index N such that a quorum of servers has matchIndex >= N
        \* and log[i][N].term is in the current leader's term.
        AgreeableIndices == {
            idx \in (commitIndex[i] + 1)..Len(log[i]) :
                /\ log[i][idx].term = currentTerm[i]
                /\ IsQuorum({i} \cup {k \in Server : matchIndex[i][k] >= idx})
        }
        newCommitIndex == IF AgreeableIndices = {} THEN commitIndex[i] ELSE Max(AgreeableIndices)
       IN commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
    /\ UNCHANGED <<currentTerm, votedFor, state, log, lastApplied, leader,
                   nextIndex, matchIndex, votesGranted, sm, net, netEnabled,
                   client_leader_hint, client_req_idx, client_outstanding_req, client_responses>>

ServerApply(i) ==
    /\ i \in Server
    /\ netEnabled[i]
    /\ lastApplied[i] < commitIndex[i]
    /\ LET
        newLastApplied == lastApplied[i] + 1
        entry == log[i][newLastApplied]
        cmd == entry.cmd
        newSm ==
            IF cmd.type = "put"
            THEN [sm[i] EXCEPT ![cmd.key] = cmd.value]
            ELSE sm[i]
        respMsg ==
            [
                mtype |-> IF cmd.type = "put" THEN "cpp" ELSE "cgp",
                msuccess |-> TRUE,
                mresponse |-> [
                    idx |-> cmd.idx,
                    key |-> cmd.key,
                    value |-> IF cmd.type = "get" THEN newSm[cmd.key] ELSE Nil,
                    ok |-> TRUE
                ],
                mleaderHint |-> i,
                msource |-> i,
                mdest |-> cmd.client
            ]
       IN /\ lastApplied' = [lastApplied EXCEPT ![i] = newLastApplied]
          /\ sm' = [sm EXCEPT ![i] = newSm]
          /\ net' = net (+) Bag({respMsg})
    /\ UNCHANGED <<currentTerm, votedFor, state, log, commitIndex, leader,
                   nextIndex, matchIndex, votesGranted, netEnabled,
                   client_leader_hint, client_req_idx, client_outstanding_req, client_responses>>

\* Actions for handling received messages

HandleRequestVoteRequest(i, msg) ==
    /\ msg.mtype = "rvq"
    /\ LET
        j == msg.msource
        newCurrentTerm == IF msg.mterm > currentTerm[i] THEN msg.mterm ELSE currentTerm[i]
        votedForAfterTermUpdate == IF msg.mterm > currentTerm[i] THEN Nil ELSE votedFor[i]
        logOK == \/ msg.mlastLogTerm > LastTerm(log[i])
                 \/ /\ msg.mlastLogTerm = LastTerm(log[i])
                    /\ msg.mlastLogIndex >= LastIndex(log[i])
        grant == /\ msg.mterm >= currentTerm[i]
                 /\ logOK
                 /\ (votedForAfterTermUpdate = Nil \/ votedForAfterTermUpdate = j)
        respMsg == [
            mtype |-> "rvp",
            mterm |-> newCurrentTerm,
            mvoteGranted |-> grant,
            msource |-> i,
            mdest |-> j
        ]
       IN /\ IF msg.mterm > currentTerm[i]
             THEN /\ currentTerm' = [currentTerm EXCEPT ![i] = msg.mterm]
                  /\ state' = [state EXCEPT ![i] = "follower"]
                  /\ leader' = [leader EXCEPT ![i] = Nil]
                  /\ votedFor' = [votedFor EXCEPT ![i] = IF grant THEN j ELSE Nil]
             ELSE /\ UNCHANGED <<currentTerm, state, leader>>
                  /\ votedFor' = [votedFor EXCEPT ![i] = IF grant THEN j ELSE votedFor[i]]
          /\ net' = (net (-) Bag({msg})) (+) Bag({respMsg})
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, sm, netEnabled,
                   client_leader_hint, client_req_idx, client_outstanding_req, client_responses>>

HandleRequestVoteResponse(i, msg) ==
    /\ msg.mtype = "rvp"
    /\ net' = net (-) Bag({msg})
    /\ IF msg.mterm > currentTerm[i]
       THEN /\ currentTerm' = [currentTerm EXCEPT ![i] = msg.mterm]
            /\ state' = [state EXCEPT ![i] = "follower"]
            /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
            /\ leader' = [leader EXCEPT ![i] = Nil]
            /\ UNCHANGED votesGranted
       ELSE /\ IF state[i] = "candidate" /\ msg.mterm = currentTerm[i] /\ msg.mvoteGranted
               THEN votesGranted' = [votesGranted EXCEPT ![i] = @ \cup {msg.msource}]
               ELSE UNCHANGED votesGranted
            /\ UNCHANGED <<currentTerm, state, votedFor, leader>>
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, sm, netEnabled,
                   client_leader_hint, client_req_idx, client_outstanding_req, client_responses>>

HandleAppendEntriesRequest(i, msg) ==
    /\ msg.mtype = "apq"
    /\ LET
        termOK == msg.mterm >= currentTerm[i]
        logMatch == \/ msg.mprevLogIndex = 0
                    \/ /\ msg.mprevLogIndex <= Len(log[i])
                       /\ log[i][msg.mprevLogIndex].term = msg.mprevLogTerm
        success == termOK /\ logMatch
        newCurrentTerm == IF msg.mterm > currentTerm[i] THEN msg.mterm ELSE currentTerm[i]
        newLog == IF success
                  THEN SubSeq(log[i], 1, msg.mprevLogIndex) \o msg.mentries
                  ELSE log[i]
        newCommitIndex == IF success
                          THEN Max({commitIndex[i], Min({msg.mcommitIndex, Len(newLog)})})
                          ELSE commitIndex[i]
        respMsg == [
            mtype |-> "app",
            mterm |-> newCurrentTerm,
            msuccess |-> success,
            mmatchIndex |-> IF success THEN Len(newLog) ELSE 0,
            msource |-> i,
            mdest |-> msg.msource
        ]
       IN /\ IF msg.mterm > currentTerm[i]
             THEN /\ currentTerm' = [currentTerm EXCEPT ![i] = msg.mterm]
                  /\ state' = [state EXCEPT ![i] = "follower"]
                  /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
                  /\ leader' = [leader EXCEPT ![i] = msg.msource]
             ELSE /\ IF msg.mterm = currentTerm[i]
                     THEN /\ state' = [state EXCEPT ![i] = "follower"]
                          /\ leader' = [leader EXCEPT ![i] = msg.msource]
                     ELSE UNCHANGED <<state, leader>>
                  /\ UNCHANGED <<currentTerm, votedFor>>
          /\ log' = [log EXCEPT ![i] = newLog]
          /\ commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
          /\ net' = (net (-) Bag({msg})) (+) Bag({respMsg})
    /\ UNCHANGED <<lastApplied, nextIndex, matchIndex, votesGranted, sm, netEnabled,
                   client_leader_hint, client_req_idx, client_outstanding_req, client_responses>>

HandleAppendEntriesResponse(i, msg) ==
    /\ msg.mtype = "app"
    /\ net' = net (-) Bag({msg})
    /\ IF msg.mterm > currentTerm[i]
       THEN /\ currentTerm' = [currentTerm EXCEPT ![i] = msg.mterm]
            /\ state' = [state EXCEPT ![i] = "follower"]
            /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
            /\ leader' = [leader EXCEPT ![i] = Nil]
            /\ UNCHANGED <<nextIndex, matchIndex>>
       ELSE /\ IF state[i] = "leader" /\ msg.mterm = currentTerm[i]
               THEN
                  IF msg.msuccess
                  THEN /\ nextIndex' = [nextIndex EXCEPT ![i][msg.msource] = msg.mmatchIndex + 1]
                       /\ matchIndex' = [matchIndex EXCEPT ![i][msg.msource] = msg.mmatchIndex]
                  ELSE /\ nextIndex' = [nextIndex EXCEPT ![i][msg.msource] = Max({1, @ - 1})]
                       /\ UNCHANGED matchIndex
               ELSE UNCHANGED <<nextIndex, matchIndex>>
            /\ UNCHANGED <<currentTerm, state, votedFor, leader>>
    /\ UNCHANGED <<log, commitIndex, lastApplied, votesGranted, sm, netEnabled,
                   client_leader_hint, client_req_idx, client_outstanding_req, client_responses>>

HandleClientRequest(i, msg) ==
    /\ msg.mtype \in {"cpq", "cgq"}
    /\ IF state[i] = "leader"
       THEN
         /\ LET
              entry == [term |-> currentTerm[i], cmd |-> msg.mcmd]
            IN log' = [log EXCEPT ![i] = Append(@, entry)]
         /\ net' = net (-) Bag({msg})
         /\ UNCHANGED <<currentTerm, votedFor, state, commitIndex, lastApplied, leader,
                        nextIndex, matchIndex, votesGranted, sm, netEnabled,
                        client_leader_hint, client_req_idx, client_outstanding_req, client_responses>>
       ELSE
         /\ LET
              respType == IF msg.mcmd.type = "put" THEN "cpp" ELSE "cgp"
              respMsg == [
                  mtype |-> respType,
                  msuccess |-> FALSE,
                  mresponse |-> [idx |-> msg.mcmd.idx, key |-> msg.mcmd.key],
                  mleaderHint |-> leader[i],
                  msource |-> i,
                  mdest |-> msg.msource
              ]
            IN net' = (net (-) Bag({msg})) (+) Bag({respMsg})
         /\ UNCHANGED <<currentTerm, votedFor, state, log, commitIndex, lastApplied, leader,
                        nextIndex, matchIndex, votesGranted, sm, netEnabled,
                        client_leader_hint, client_req_idx, client_outstanding_req, client_responses>>

HandleMessage(i) ==
    \E msg \in DOMAIN net:
        /\ msg.mdest = i
        /\ netEnabled[i]
        /\ \/ HandleRequestVoteRequest(i, msg)
           \/ HandleRequestVoteResponse(i, msg)
           \/ HandleAppendEntriesRequest(i, msg)
           \/ HandleAppendEntriesResponse(i, msg)
           \/ HandleClientRequest(i, msg)

\* Actions for clients

ClientRequest(c) ==
    /\ c \in Client
    /\ client_outstanding_req[c].type = "none"
    /\ \E reqType \in RequestType, key \in AllStrings, val \in AllStrings:
        /\ LET
            newReqIdx == client_req_idx[c] + 1
            req == [type |-> reqType, key |-> key, value |-> val, idx |-> newReqIdx, client |-> c]
            msgType == IF reqType = "put" THEN "cpq" ELSE "cgq"
            dest == client_leader_hint[c]
            msg == [
                mtype |-> msgType,
                mcmd |-> req,
                msource |-> c,
                mdest |-> dest
            ]
           IN /\ client_req_idx' = [client_req_idx EXCEPT ![c] = newReqIdx]
              /\ client_outstanding_req' = [client_outstanding_req EXCEPT ![c] = req]
              /\ IF dest # Nil /\ netEnabled[dest]
                 THEN net' = net (+) Bag({msg})
                 ELSE UNCHANGED net
    /\ UNCHANGED <<currentTerm, votedFor, state, log, commitIndex, lastApplied, leader,
                   nextIndex, matchIndex, votesGranted, sm, netEnabled,
                   client_leader_hint, client_responses>>

ClientReceiveResponse(c) ==
    /\ c \in Client
    /\ \E msg \in DOMAIN net:
        /\ msg.mdest = c
        /\ msg.mresponse.idx = client_req_idx[c]
        /\ net' = net (-) Bag({msg})
        /\ IF msg.msuccess
           THEN /\ client_outstanding_req' = [client_outstanding_req EXCEPT ![c] = [type |-> "none"]]
                /\ client_responses' = Append(client_responses, msg)
                /\ UNCHANGED client_leader_hint
           ELSE /\ client_leader_hint' = [client_leader_hint EXCEPT ![c] = msg.mleaderHint]
                /\ client_outstanding_req' = [client_outstanding_req EXCEPT ![c] = [type |-> "none"]]
                /\ UNCHANGED client_responses
    /\ UNCHANGED <<currentTerm, votedFor, state, log, commitIndex, lastApplied, leader,
                   nextIndex, matchIndex, votesGranted, sm, netEnabled, client_req_idx>>

ClientTimeout(c) ==
    /\ c \in Client
    /\ client_outstanding_req[c].type /= "none"
    /\ LET dest == client_leader_hint[c] IN
        \/ dest = Nil
        \/ \lnot netEnabled[dest]
    /\ client_leader_hint' = [client_leader_hint EXCEPT ![c] = ((c - NumServers - 1 + 1) % NumServers) + 1]
    /\ UNCHANGED <<currentTerm, votedFor, state, log, commitIndex, lastApplied, leader,
                   nextIndex, matchIndex, votesGranted, sm, net, netEnabled,
                   client_req_idx, client_outstanding_req, client_responses>>

\* Action for failure

Crash(i) ==
    /\ i \in Server
    /\ netEnabled[i]
    /\ netEnabled' = [netEnabled EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<currentTerm, votedFor, state, log, commitIndex, lastApplied, leader,
                   nextIndex, matchIndex, votesGranted, sm, net,
                   client_leader_hint, client_req_idx, client_outstanding_req, client_responses>>

Next ==
    \/ \E i \in Server:
        \/ ServerTimeout(i)
        \/ BecomeLeader(i)
        \/ \E j \in Server: LeaderSendAppendEntries(i, j)
        \/ LeaderAdvanceCommitIndex(i)
        \/ ServerApply(i)
        \/ HandleMessage(i)
        \/ Crash(i)
    \/ \E c \in Client:
        \/ ClientRequest(c)
        \/ ClientReceiveResponse(c)
        \/ ClientTimeout(c)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A i \in Server: WF_vars(ServerTimeout(i))
    /\ \A i \in Server: WF_vars(BecomeLeader(i))
    /\ \A i \in Server: WF_vars(LeaderAdvanceCommitIndex(i))
    /\ \A i \in Server: WF_vars(ServerApply(i))
    /\ \A i, j \in Server: WF_vars(LeaderSendAppendEntries(i, j))
    /\ \A i \in Server: WF_vars(HandleMessage(i))
    /\ \A c \in Client: WF_vars(ClientRequest(c))
    /\ \A c \in Client: WF_vars(ClientReceiveResponse(c))
    /\ \A c \in Client: WF_vars(ClientTimeout(c))

====
