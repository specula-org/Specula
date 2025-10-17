---- MODULE raftkvs ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS
    NumServers,
    Clients,
    Keys,
    Values,
    Nil

ASSUME NumServers \in Nat \ {0}

Server == 1..NumServers

\* States
StateFollower == "follower"
StateCandidate == "candidate"
StateLeader == "leader"
ServerState == {StateFollower, StateCandidate, StateLeader}

\* Message Types
RequestVoteRequest == "rvq"
RequestVoteResponse == "rvp"
AppendEntriesRequest == "apq"
AppendEntriesResponse == "app"
ClientPutRequest == "cpq"
ClientPutResponse == "cpp"
ClientGetRequest == "cgq"
ClientGetResponse == "cgp"

\* Commands
CMD_Put == "put"
CMD_Get == "get"
CommandType == {CMD_Put, CMD_Get}
Command == [type: CommandType, key: Keys, value: Values \union {Nil}]

IsQuorum(S) == Cardinality(S) * 2 > NumServers

LastTerm(log) == IF Len(log) = 0 THEN 0 ELSE log[Len(log)]["term"]

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
    lastApplied

vars == <<net, state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votesGranted, sm, lastApplied>>

Init ==
    /\ net = {}
    /\ state = [s \in Server |-> StateFollower]
    /\ currentTerm = [s \in Server |-> 0]
    /\ votedFor = [s \in Server |-> Nil]
    /\ log = [s \in Server |-> <<>>]
    /\ commitIndex = [s \in Server |-> 0]
    /\ lastApplied = [s \in Server |-> 0]
    /\ nextIndex = [s \in Server |-> [p \in Server |-> 1]]
    /\ matchIndex = [s \in Server |-> [p \in Server |-> 0]]
    /\ votesGranted = [s \in Server |-> {}]
    /\ sm = [s \in Server |-> [k \in Keys |-> Nil]]

\* A server times out and starts an election.
TimeoutAndStartElection(s) ==
    /\ state[s] \in {StateFollower, StateCandidate}
    /\ state' = [state EXCEPT ![s] = StateCandidate]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = @ + 1]
    /\ votedFor' = [votedFor EXCEPT ![s] = s]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
    /\ net' = net \cup {
        [
            mtype |-> RequestVoteRequest,
            mterm |-> currentTerm[s] + 1,
            mlastLogIndex |-> Len(log[s]),
            mlastLogTerm |-> LastTerm(log[s]),
            msource |-> s,
            mdest |-> p
        ] : p \in Server
    }
    /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, sm, lastApplied>>

\* A candidate that has received a majority of votes becomes leader.
BecomeLeader(s) ==
    /\ state[s] = StateCandidate
    /\ IsQuorum(votesGranted[s])
    /\ state' = [state EXCEPT ![s] = StateLeader]
    /\ nextIndex' = [nextIndex EXCEPT ![s] = [p \in Server |-> Len(log[s]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![s] = [p \in Server |-> 0]]
    /\ UNCHANGED <<net, currentTerm, votedFor, log, commitIndex, votesGranted, sm, lastApplied>>

\* A helper operator to handle a server stepping down when it sees a higher term.
StepDown(s, newTerm) ==
    /\ currentTerm' = [currentTerm EXCEPT ![s] = newTerm]
    /\ state' = [state EXCEPT ![s] = StateFollower]
    /\ votedFor' = [votedFor EXCEPT ![s] = Nil]

\* A server s receives a RequestVoteRequest message m.
HandleRequestVoteRequest(m) ==
    /\ m["mtype"] = RequestVoteRequest
    /\ LET s == m["mdest"]
    /\ LET candLastTerm == m["mlastLogTerm"]
    /\ LET candLastIndex == m["mlastLogIndex"]
    /\ LET myLastTerm == LastTerm(log[s])
    /\ LET myLastIndex == Len(log[s])
    /\ LET logOK == (candLastTerm > myLastTerm) \/
                    (candLastTerm = myLastTerm /\ candLastIndex >= myLastIndex)
    /\ IF m["mterm"] > currentTerm[s] THEN
        /\ LET grant == logOK
        /\ currentTerm' = [currentTerm EXCEPT ![s] = m["mterm"]]
        /\ state' = [state EXCEPT ![s] = StateFollower]
        /\ votedFor' = [votedFor EXCEPT ![s] = IF grant THEN m["msource"] ELSE Nil]
        /\ net' = (net \ {m}) \cup {
            [
                mtype |-> RequestVoteResponse,
                mterm |-> m["mterm"],
                mvoteGranted |-> grant,
                msource |-> s,
                mdest |-> m["msource"]
            ]
        }
        /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, votesGranted, sm, lastApplied>>
    ELSE
        /\ LET grant == m["mterm"] = currentTerm[s] /\
                        logOK /\
                        (votedFor[s] = Nil \/ votedFor[s] = m["msource"])
        /\ votedFor' = IF grant THEN [votedFor EXCEPT ![s] = m["msource"]] ELSE votedFor
        /\ net' = (net \ {m}) \cup {
            [
                mtype |-> RequestVoteResponse,
                mterm |-> currentTerm[s],
                mvoteGranted |-> grant,
                msource |-> s,
                mdest |-> m["msource"]
            ]
        }
        /\ UNCHANGED <<state, currentTerm, log, commitIndex, nextIndex, matchIndex, votesGranted, sm, lastApplied>>

\* A candidate s receives a RequestVoteResponse message m.
HandleRequestVoteResponse(m) ==
    /\ m["mtype"] = RequestVoteResponse
    /\ LET s == m["mdest"]
    /\ IF m["mterm"] > currentTerm[s] THEN
        /\ StepDown(s, m["mterm"])
        /\ net' = net \ {m}
        /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, votesGranted, sm, lastApplied>>
    ELSE IF m["mterm"] = currentTerm[s] /\ state[s] = StateCandidate /\ m["mvoteGranted"] THEN
        /\ votesGranted' = [votesGranted EXCEPT ![s] = @ \cup {m["msource"]}]
        /\ net' = net \ {m}
        /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, sm, lastApplied>>
    ELSE
        /\ net' = net \ {m}
        /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votesGranted, sm, lastApplied>>

\* A leader l sends an AppendEntriesRequest to peer p. This covers both heartbeats and log replication.
SendAppendEntries(l, p) ==
    /\ state[l] = StateLeader
    /\ p /= l
    /\ LET prevLogIndex == nextIndex[l][p] - 1
    /\ LET prevLogTerm == IF prevLogIndex > 0 THEN log[l][prevLogIndex]["term"] ELSE 0
    /\ LET entries == SubSeq(log[l], nextIndex[l][p], Len(log[l]))
    /\ net' = net \cup {
        [
            mtype |-> AppendEntriesRequest,
            mterm |-> currentTerm[l],
            mprevLogIndex |-> prevLogIndex,
            mprevLogTerm |-> prevLogTerm,
            mentries |-> entries,
            mcommitIndex |-> commitIndex[l],
            msource |-> l,
            mdest |-> p
        ]
    }
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votesGranted, sm, lastApplied>>

\* A server s receives an AppendEntriesRequest message m.
HandleAppendEntriesRequest(m) ==
    /\ m["mtype"] = AppendEntriesRequest
    /\ LET s == m["mdest"]
    /\ IF m["mterm"] < currentTerm[s] THEN
        /\ net' = (net \ {m}) \cup {
            [
                mtype |-> AppendEntriesResponse,
                mterm |-> currentTerm[s],
                msuccess |-> FALSE,
                mmatchIndex |-> 0,
                msource |-> s,
                mdest |-> m["msource"]
            ]
        }
        /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votesGranted, sm, lastApplied>>
    ELSE
        /\ state' = [state EXCEPT ![s] = StateFollower]
        /\ currentTerm' = [currentTerm EXCEPT ![s] = m["mterm"]]
        /\ votedFor' = IF m["mterm"] > currentTerm[s]
                      THEN [votedFor EXCEPT ![s] = Nil]
                      ELSE votedFor
        /\ LET logOK == m["mprevLogIndex"] = 0 \/
                        (m["mprevLogIndex"] > 0 /\
                         m["mprevLogIndex"] <= Len(log[s]) /\
                         log[s][m["mprevLogIndex"]]["term"] = m["mprevLogTerm"])
        /\ IF logOK THEN
            /\ LET newLog == SubSeq(log[s], 1, m["mprevLogIndex"]) \o m["mentries"]
            /\ log' = [log EXCEPT ![s] = newLog]
            /\ LET newCommitIndex == Min({m["mcommitIndex"], Len(newLog)})
            /\ commitIndex' = [commitIndex EXCEPT ![s] = newCommitIndex]
            /\ LET oldApplied == lastApplied[s]
            /\ LET newSmAndApplied ==
                LET Apply(idx, currentSm) ==
                    LET entry == newLog[idx]
                    IN IF entry["cmd"]["type"] = CMD_Put
                       THEN [currentSm EXCEPT ![entry["cmd"]["key"]] = entry["cmd"]["value"]]
                       ELSE currentSm
                IN LET RECURSIVE rec(idx, currentSm) ==
                    IF idx > newCommitIndex
                    THEN <<currentSm, idx - 1>>
                    ELSE rec(idx + 1, Apply(idx, currentSm))
                IN rec(oldApplied + 1, sm[s])
            /\ sm' = [sm EXCEPT ![s] = newSmAndApplied[1]]
            /\ lastApplied' = [lastApplied EXCEPT ![s] = newSmAndApplied[2]]
            /\ net' = (net \ {m}) \cup {
                [
                    mtype |-> AppendEntriesResponse,
                    mterm |-> currentTerm'[s],
                    msuccess |-> TRUE,
                    mmatchIndex |-> m["mprevLogIndex"] + Len(m["mentries"]),
                    msource |-> s,
                    mdest |-> m["msource"]
                ]
            }
            /\ UNCHANGED <<nextIndex, matchIndex, votesGranted>>
        ELSE
            /\ net' = (net \ {m}) \cup {
                [
                    mtype |-> AppendEntriesResponse,
                    mterm |-> currentTerm'[s],
                    msuccess |-> FALSE,
                    mmatchIndex |-> 0,
                    msource |-> s,
                    mdest |-> m["msource"]
                ]
            }
            /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, votesGranted, sm, lastApplied>>

\* A leader s receives an AppendEntriesResponse message m.
HandleAppendEntriesResponse(m) ==
    /\ m["mtype"] = AppendEntriesResponse
    /\ LET s == m["mdest"]
    /\ IF m["mterm"] > currentTerm[s] THEN
        /\ StepDown(s, m["mterm"])
        /\ net' = net \ {m}
        /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, votesGranted, sm, lastApplied>>
    ELSE IF m["mterm"] = currentTerm[s] /\ state[s] = StateLeader THEN
        /\ LET peer == m["msource"]
        /\ (IF m["msuccess"] THEN
            /\ matchIndex' = [matchIndex EXCEPT ![s][peer] = m["mmatchIndex"]]
            /\ nextIndex' = [nextIndex EXCEPT ![s][peer] = m["mmatchIndex"] + 1]
        ELSE
            /\ nextIndex' = [nextIndex EXCEPT ![s][peer] = Max({nextIndex[s][peer] - 1, 1})]
            /\ UNCHANGED matchIndex)
        /\ net' = net \ {m}
        /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, votesGranted, sm, lastApplied>>
    ELSE
        /\ net' = net \ {m}
        /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votesGranted, sm, lastApplied>>

\* A leader l advances its commit index.
AdvanceCommitIndex(l) ==
    /\ state[l] = StateLeader
    /\ LET CanCommit(n) ==
        /\ n > commitIndex[l]
        /\ n <= Len(log[l])
        /\ log[l][n]["term"] = currentTerm[l]
        /\ IsQuorum({s \in Server | matchIndex[l][s] >= n} \cup {l})
    /\ \E newCommitIndex \in (commitIndex[l]+1)..Len(log[l]) :
        /\ CanCommit(newCommitIndex)
        /\ \A n \in (newCommitIndex+1)..Len(log[l]) : ~CanCommit(n)
        /\ commitIndex' = [commitIndex EXCEPT ![l] = newCommitIndex]
        /\ LET oldApplied == lastApplied[l]
        /\ LET newSmAndApplied ==
            LET Apply(idx, currentSm) ==
                LET entry == log[l][idx]
                IN IF entry["cmd"]["type"] = CMD_Put
                   THEN [currentSm EXCEPT ![entry["cmd"]["key"]] = entry["cmd"]["value"]]
                   ELSE currentSm
            IN LET RECURSIVE rec(idx, currentSm) ==
                IF idx > newCommitIndex
                THEN <<currentSm, idx - 1>>
                ELSE rec(idx + 1, Apply(idx, currentSm))
            IN rec(oldApplied + 1, sm[l])
        /\ sm' = [sm EXCEPT ![l] = newSmAndApplied[1]]
        /\ lastApplied' = [lastApplied EXCEPT ![l] = newSmAndApplied[2]]
        /\ LET newResponses ==
            LET MakeResp(idx) ==
                LET entry == log[l][idx]
                IN LET respType == IF entry["cmd"]["type"] = CMD_Put THEN ClientPutResponse ELSE ClientGetResponse
                IN LET value == IF entry["cmd"]["type"] = CMD_Get THEN sm'[l][entry["cmd"]["key"]] ELSE Nil
                IN [
                    mtype |-> respType,
                    msuccess |-> TRUE,
                    mresponse |-> [key |-> entry["cmd"]["key"], value |-> value],
                    mleaderHint |-> l,
                    msource |-> l,
                    mdest |-> entry["client"]
                ]
            IN {MakeResp(i) : i \in (oldApplied+1)..newCommitIndex}
        /\ net' = net \cup newResponses
        /\ UNCHANGED <<state, currentTerm, votedFor, log, nextIndex, matchIndex, votesGranted>>

\* A server s receives a client request message m.
HandleClientRequest(m) ==
    /\ m["mtype"] \in {ClientPutRequest, ClientGetRequest}
    /\ LET s == m["mdest"]
    /\ IF state[s] = StateLeader THEN
        /\ LET cmdType == IF m["mtype"] = ClientPutRequest THEN CMD_Put ELSE CMD_Get
        /\ LET newEntry == [
            term |-> currentTerm[s],
            cmd |-> [type |-> cmdType, key |-> m["mcmd"]["key"], value |-> m["mcmd"]["value"]],
            client |-> m["msource"]
        ]
        /\ log' = [log EXCEPT ![s] = Append(@, newEntry)]
        /\ net' = net \ {m}
        /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, nextIndex, matchIndex, votesGranted, sm, lastApplied>>
    ELSE
        /\ LET respType == IF m["mtype"] = ClientPutRequest THEN ClientPutResponse ELSE ClientGetResponse
        /\ net' = (net \ {m}) \cup {
            [
                mtype |-> respType,
                msuccess |-> FALSE,
                mresponse |-> [key |-> m["mcmd"]["key"], value |-> Nil],
                mleaderHint |-> Nil,
                msource |-> s,
                mdest |-> m["msource"]
            ]
        }
        /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votesGranted, sm, lastApplied>>

\* A message is lost from the network.
DropMessage(m) ==
    /\ m \in net
    /\ net' = net \ {m}
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votesGranted, sm, lastApplied>>

Next ==
    \/ \E s \in Server : TimeoutAndStartElection(s)
    \/ \E s \in Server : BecomeLeader(s)
    \/ \E l \in Server, p \in Server : SendAppendEntries(l, p)
    \/ \E l \in Server : AdvanceCommitIndex(l)
    \/ \E m \in net :
        \/ HandleRequestVoteRequest(m)
        \/ HandleRequestVoteResponse(m)
        \/ HandleAppendEntriesRequest(m)
        \/ HandleAppendEntriesResponse(m)
        \/ HandleClientRequest(m)
    \/ \E m \in net : DropMessage(m)

Fairness ==
    /\ \A s \in Server : WF_vars(TimeoutAndStartElection(s))
    /\ \A s \in Server : WF_vars(BecomeLeader(s))
    /\ \A l \in Server, p \in Server : WF_vars(SendAppendEntries(l, p))
    /\ \A l \in Server : WF_vars(AdvanceCommitIndex(l))
    /\ \A m \in net :
        \/ WF_vars(HandleRequestVoteRequest(m))
        \/ WF_vars(HandleRequestVoteResponse(m))
        \/ WF_vars(HandleAppendEntriesRequest(m))
        \/ WF_vars(HandleAppendEntriesResponse(m))
        \/ WF_vars(HandleClientRequest(m))
        \/ WF_vars(DropMessage(m))

Spec == Init /\ [][Next]_vars /\ Fairness

====
