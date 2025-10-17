---- MODULE raftkvs ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS
    NumServers,
    Clients,
    Keys,
    Values,
    Nil

ASSUME NumServers \in Nat /\ NumServers > 0
ASSUME IsFiniteSet(Clients)
ASSUME IsFiniteSet(Keys)
ASSUME IsFiniteSet(Values)
ASSUME Nil \notin ((1..NumServers) \cup Clients)

Servers == 1..NumServers
NodeStates == {"follower", "candidate", "leader"}
CommandTypes == {"put", "get"}

PutCommands == [type: {"put"}, key: Keys, value: Values]
GetCommands == [type: {"get"}, key: Keys]
Commands == PutCommands \cup GetCommands

LogEntry == [term: Nat, command: Commands, client: Clients, reqId: Nat]

RequestVoteRequest == "rvq"
RequestVoteResponse == "rvp"
AppendEntriesRequest == "apq"
AppendEntriesResponse == "app"
ClientPutRequest == "cpq"
ClientPutResponse == "cpp"
ClientGetRequest == "cgq"
ClientGetResponse == "cgp"

VARIABLES
    net,
    state,
    currentTerm,
    votedFor,
    log,
    commitIndex,
    lastApplied,
    sm,
    nextIndex,
    matchIndex,
    votesGranted,
    leader

vars == <<net, state, currentTerm, votedFor, log, commitIndex, lastApplied, sm, nextIndex, matchIndex, votesGranted, leader>>

IsQuorum(S) == Cardinality(S) * 2 > NumServers
LastTerm(l) == IF Len(l) = 0 THEN 0 ELSE l[Len(l)]["term"]
LastIndex(l) == Len(l)

Init ==
    /\ state = [i \in Servers |-> "follower"]
    /\ currentTerm = [i \in Servers |-> 0]
    /\ votedFor = [i \in Servers |-> Nil]
    /\ log = [i \in Servers |-> << >>]
    /\ commitIndex = [i \in Servers |-> 0]
    /\ lastApplied = [i \in Servers |-> 0]
    /\ sm = [i \in Servers |-> [k \in Keys |-> Nil]]
    /\ nextIndex = [i \in Servers |-> [j \in Servers |-> 1]]
    /\ matchIndex = [i \in Servers |-> [j \in Servers |-> 0]]
    /\ votesGranted = [i \in Servers |-> {}]
    /\ leader = [i \in Servers |-> Nil]
    /\ net = {}

StepDown(i, newTerm) ==
    /\ state' = [state EXCEPT ![i] = "follower"]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = newTerm]
    /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
    /\ leader' = [leader EXCEPT ![i] = Nil]
    /\ UNCHANGED <<log, commitIndex, lastApplied, sm, nextIndex, matchIndex, votesGranted>>

Timeout(i) ==
    /\ state[i] \in {"follower", "candidate"}
    /\ state' = [state EXCEPT ![i] = "candidate"]
    /\ leader' = [leader EXCEPT ![i] = Nil]
    /\ LET newTerm == currentTerm[i] + 1
    IN /\ currentTerm' = [currentTerm EXCEPT ![i] = newTerm]
       /\ votedFor' = [votedFor EXCEPT ![i] = i]
       /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}]
       /\ LET
            req == [
                type |-> RequestVoteRequest,
                term |-> newTerm,
                lastLogIndex |-> LastIndex(log[i]),
                lastLogTerm |-> LastTerm(log[i]),
                from |-> i
            ]
        IN net' = net \cup { [req EXCEPT !["to"] = j] : j \in Servers \ {i} }
    /\ UNCHANGED <<log, commitIndex, lastApplied, sm, nextIndex, matchIndex>>

HandleRequestVoteRequest(j) ==
    \E msg \in net:
        /\ msg["type"] = RequestVoteRequest
        /\ msg["to"] = j
        /\ LET i == msg["from"]
           IN \/ /\ msg["term"] > currentTerm[j]
                 /\ StepDown(j, msg["term"])
                 /\ net' = net
              \/ /\ msg["term"] <= currentTerm[j]
                 /\ LET
                       logIsUpToDate == \/ msg["lastLogTerm"] > LastTerm(log[j])
                                        \/ /\ msg["lastLogTerm"] = LastTerm(log[j])
                                           /\ msg["lastLogIndex"] >= LastIndex(log[j])
                       grantVote == /\ msg["term"] = currentTerm[j]
                                    /\ logIsUpToDate
                                    /\ votedFor[j] \in {Nil, i}
                    IN /\ IF grantVote THEN
                              votedFor' = [votedFor EXCEPT ![j] = i]
                          ELSE
                              votedFor' = votedFor
                       /\ LET resp == [
                               type |-> RequestVoteResponse,
                               term |-> currentTerm[j],
                               voteGranted |-> grantVote,
                               from |-> j,
                               to |-> i
                           ]
                       IN net' = (net \ {msg}) \cup {resp}
                 /\ UNCHANGED <<state, currentTerm, log, commitIndex, lastApplied, sm, nextIndex, matchIndex, votesGranted, leader>>

HandleRequestVoteResponse(i) ==
    \E msg \in net:
        /\ msg["type"] = RequestVoteResponse
        /\ msg["to"] = i
        /\ LET j == msg["from"]
        IN \/ /\ msg["term"] > currentTerm[i]
              /\ StepDown(i, msg["term"])
              /\ net' = net \ {msg}
           \/ /\ msg["term"] = currentTerm[i]
              /\ state[i] = "candidate"
              /\ IF msg["voteGranted"] THEN
                    /\ votesGranted' = [votesGranted EXCEPT ![i] = @ \cup {j}]
                    /\ IF IsQuorum(votesGranted'[i]) THEN
                        /\ state' = [state EXCEPT ![i] = "leader"]
                        /\ leader' = [leader EXCEPT ![i] = i]
                        /\ nextIndex' = [nextIndex EXCEPT ![i] = [k \in Servers |-> LastIndex(log[i]) + 1]]
                        /\ matchIndex' = [matchIndex EXCEPT ![i] = [k \in Servers |-> 0]]
                    ELSE
                        /\ UNCHANGED <<state, leader, nextIndex, matchIndex>>
                 ELSE
                    /\ UNCHANGED <<state, leader, nextIndex, matchIndex, votesGranted>>
              /\ net' = net \ {msg}
              /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied, sm>>

LeaderSendAppendEntries(i, j) ==
    /\ state[i] = "leader"
    /\ j \in Servers \ {i}
    /\ LET prevLogIndex == nextIndex[i][j] - 1
    IN /\ LET prevLogTerm == IF prevLogIndex > 0 THEN log[i][prevLogIndex]["term"] ELSE 0
       /\ LET entriesToSend == SubSeq(log[i], nextIndex[i][j], Len(log[i]))
       /\ LET req == [
            type |-> AppendEntriesRequest,
            term |-> currentTerm[i],
            prevLogIndex |-> prevLogIndex,
            prevLogTerm |-> prevLogTerm,
            entries |-> entriesToSend,
            commitIndex |-> commitIndex[i],
            from |-> i,
            to |-> j
          ]
       /\ net' = net \cup {req}
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, sm, nextIndex, matchIndex, votesGranted, leader>>

HandleAppendEntriesRequest(j) ==
    \E msg \in net:
        /\ msg["type"] = AppendEntriesRequest
        /\ msg["to"] = j
        /\ LET i == msg["from"] IN
           \/ /\ msg["term"] > currentTerm[j]
              /\ StepDown(j, msg["term"])
              /\ net' = net
           \/ /\ msg["term"] < currentTerm[j]
              /\ LET resp == [
                    type |-> AppendEntriesResponse,
                    term |-> currentTerm[j],
                    success |-> FALSE,
                    matchIndex |-> 0,
                    from |-> j,
                    to |-> i
                 ]
              /\ net' = (net \ {msg}) \cup {resp}
              /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, sm, nextIndex, matchIndex, votesGranted, leader>>
           \/ /\ msg["term"] = currentTerm[j]
              /\ state' = [state EXCEPT ![j] = "follower"]
              /\ leader' = [leader EXCEPT ![j] = i]
              /\ LET logOK == msg["prevLogIndex"] = 0
                           \/ ( /\ msg["prevLogIndex"] <= Len(log[j])
                                /\ log[j][msg["prevLogIndex"]]["term"] = msg["prevLogTerm"] )
              /\ IF logOK THEN
                    /\ LET newLog == SubSeq(log[j], 1, msg["prevLogIndex"]) \o msg["entries"]
                    /\ log' = [log EXCEPT ![j] = newLog]
                    /\ IF msg["commitIndex"] > commitIndex[j] THEN
                        commitIndex' = [commitIndex EXCEPT ![j] = Min({msg["commitIndex"], LastIndex(newLog)})]
                    ELSE
                        UNCHANGED commitIndex
                    /\ LET resp == [
                            type |-> AppendEntriesResponse,
                            term |-> currentTerm[j],
                            success |-> TRUE,
                            matchIndex |-> LastIndex(newLog),
                            from |-> j,
                            to |-> i
                        ]
                    /\ net' = (net \ {msg}) \cup {resp}
                 ELSE
                    /\ LET resp == [
                            type |-> AppendEntriesResponse,
                            term |-> currentTerm[j],
                            success |-> FALSE,
                            matchIndex |-> 0,
                            from |-> j,
                            to |-> i
                        ]
                    /\ net' = (net \ {msg}) \cup {resp}
                    /\ UNCHANGED <<log, commitIndex>>
              /\ UNCHANGED <<currentTerm, votedFor, lastApplied, sm, nextIndex, matchIndex, votesGranted>>

HandleAppendEntriesResponse(i) ==
    \E msg \in net:
        /\ msg["type"] = AppendEntriesResponse
        /\ msg["to"] = i
        /\ state[i] = "leader"
        /\ LET j == msg["from"]
        IN \/ /\ msg["term"] > currentTerm[i]
              /\ StepDown(i, msg["term"])
              /\ net' = net \ {msg}
           \/ /\ msg["term"] = currentTerm[i]
              /\ IF msg["success"] THEN
                    /\ matchIndex' = [matchIndex EXCEPT ![i] = [ @ EXCEPT ![j] = msg["matchIndex"] ]]
                    /\ nextIndex' = [nextIndex EXCEPT ![i] = [ @ EXCEPT ![j] = msg["matchIndex"] + 1 ]]
                 ELSE
                    /\ nextIndex' = [nextIndex EXCEPT ![i] = [ @ EXCEPT ![j] = Max({1, @[j] - 1}) ]]
                    /\ UNCHANGED matchIndex
              /\ net' = net \ {msg}
              /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, sm, votesGranted, leader>>

LeaderAdvanceCommitIndex(i) ==
    /\ state[i] = "leader"
    /\ LET
        ReplicatedOnMajority(n) == IsQuorum({k \in Servers | matchIndex[i][k] >= n})
        PossibleNewCommitIndices == { n \in (commitIndex[i]+1)..Len(log[i]) |
                                        /\ ReplicatedOnMajority(n)
                                        /\ log[i][n]["term"] = currentTerm[i] }
    IN /\ IF PossibleNewCommitIndices /= {} THEN
            /\ LET newCommitIndex == Max(PossibleNewCommitIndices)
            IN commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
         ELSE
            UNCHANGED commitIndex
    /\ UNCHANGED <<net, state, currentTerm, votedFor, log, lastApplied, sm, nextIndex, matchIndex, votesGranted, leader>>

ApplyCommittedEntries(k) ==
    /\ commitIndex[k] > lastApplied[k]
    /\ LET newLastApplied == lastApplied[k] + 1
    /\ lastApplied' = [lastApplied EXCEPT ![k] = newLastApplied]
    /\ LET entry == log[k][newLastApplied]
    /\ LET cmd == entry["command"]
    /\ IF cmd["type"] = "put" THEN
        sm' = [sm EXCEPT ![k] = [ @ EXCEPT ![cmd["key"]] = cmd["value"] ]]
    ELSE
        UNCHANGED sm
    /\ IF state[k] = "leader" THEN
        /\ LET client == entry["client"]
        /\ LET reqId == entry["reqId"]
        /\ LET resp ==
            IF cmd["type"] = "put" THEN
                [ type |-> ClientPutResponse,
                  success |-> TRUE,
                  leaderHint |-> k,
                  from |-> k,
                  to |-> client,
                  reqId |-> reqId ]
            ELSE
                [ type |-> ClientGetResponse,
                  success |-> TRUE,
                  value |-> sm[k][cmd["key"]],
                  leaderHint |-> k,
                  from |-> k,
                  to |-> client,
                  reqId |-> reqId ]
        /\ net' = net \cup {resp}
    ELSE
        UNCHANGED net
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votesGranted, leader>>

ClientRequest(c, i, reqId) ==
    /\ c \in Clients
    /\ i \in Servers
    /\ reqId \in Nat
    /\ \E cmd \in Commands:
        /\ LET msg ==
            IF cmd["type"] = "put" THEN
                [ type |-> ClientPutRequest,
                  command |-> cmd,
                  client |-> c,
                  reqId |-> reqId,
                  to |-> i ]
            ELSE
                [ type |-> ClientGetRequest,
                  command |-> cmd,
                  client |-> c,
                  reqId |-> reqId,
                  to |-> i ]
        /\ net' = net \cup {msg}
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, sm, nextIndex, matchIndex, votesGranted, leader>>

ServerHandleClientRequest(i) ==
    \E msg \in net:
        /\ msg["type"] \in {ClientPutRequest, ClientGetRequest}
        /\ msg["to"] = i
        /\ IF state[i] = "leader" THEN
            /\ LET newEntry == [
                    term |-> currentTerm[i],
                    command |-> msg["command"],
                    client |-> msg["client"],
                    reqId |-> msg["reqId"]
                ]
            /\ log' = [log EXCEPT ![i] = Append(log[i], newEntry)]
            /\ net' = net \ {msg}
            /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, sm, nextIndex, matchIndex, votesGranted, leader>>
        ELSE
            /\ LET resp ==
                IF msg["type"] = ClientPutRequest THEN
                    [ type |-> ClientPutResponse,
                      success |-> FALSE,
                      leaderHint |-> leader[i],
                      from |-> i,
                      to |-> msg["client"],
                      reqId |-> msg["reqId"] ]
                ELSE
                    [ type |-> ClientGetResponse,
                      success |-> FALSE,
                      value |-> Nil,
                      leaderHint |-> leader[i],
                      from |-> i,
                      to |-> msg["client"],
                      reqId |-> msg["reqId"] ]
            /\ net' = (net \ {msg}) \cup {resp}
            /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, sm, nextIndex, matchIndex, votesGranted, leader>>

DropMessage(msg) ==
    /\ msg \in net
    /\ net' = net \ {msg}
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, sm, nextIndex, matchIndex, votesGranted, leader>>

Next ==
    \/ \E i \in Servers: Timeout(i)
    \/ \E j \in Servers: HandleRequestVoteRequest(j)
    \/ \E i \in Servers: HandleRequestVoteResponse(i)
    \/ \E i, j \in Servers: i /= j /\ LeaderSendAppendEntries(i, j)
    \/ \E j \in Servers: HandleAppendEntriesRequest(j)
    \/ \E i \in Servers: HandleAppendEntriesResponse(i)
    \/ \E i \in Servers: LeaderAdvanceCommitIndex(i)
    \/ \E k \in Servers: ApplyCommittedEntries(k)
    \/ \E c \in Clients, i \in Servers, reqId \in Nat: ClientRequest(c, i, reqId)
    \/ \E i \in Servers: ServerHandleClientRequest(i)
    \/ \E msg \in net: DropMessage(msg)

Server(i) ==
    \/ Timeout(i)
    \/ HandleRequestVoteRequest(i)
    \/ HandleRequestVoteResponse(i)
    \/ (\E j \in Servers \ {i}: LeaderSendAppendEntries(i, j))
    \/ HandleAppendEntriesRequest(i)
    \/ HandleAppendEntriesResponse(i)
    \/ LeaderAdvanceCommitIndex(i)
    \/ ApplyCommittedEntries(i)
    \/ ServerHandleClientRequest(i)

Spec == Init /\ [][Next]_vars /\ \A i \in Servers : WF_vars(Server(i))

====