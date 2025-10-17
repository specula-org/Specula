---- MODULE raftkvs ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS NumServers, NumClients, AllStrings, ExploreFail, MaxNodeFail, Debug, LeaderTimeoutReset, LogPop, LogConcat

VARIABLES servers, clients, network, crashed, timer

vars == <<servers, clients, network, crashed, timer>>

ServerSet == 1..NumServers
ClientSet == (NumServers+1)..(NumServers+NumClients)
NodeSet == ServerSet \cup ClientSet

Nil == 0
Follower == "follower"
Candidate == "candidate"
Leader == "leader"
Put == "put"
Get == "get"
RequestVoteRequest == "rvq"
RequestVoteResponse == "rvp"
AppendEntriesRequest == "apq"
AppendEntriesResponse == "app"
ClientPutRequest == "cpq"
ClientPutResponse == "cpp"
ClientGetRequest == "cgq"
ClientGetResponse == "cgp"

IsQuorum(S) == Cardinality(S) * 2 > NumServers

LastTerm(log) == IF Len(log) = 0 THEN 0 ELSE log[Len(log)].term

Min(S) == CHOOSE x \in S : \A y \in S : x <= y
Max(S) == CHOOSE x \in S : \A y \in S : x >= y

FindMaxAgreeIndex(log, i, matchIndex) ==
  LET RECURSIVE FindMax(max) ==
    IF max = 0 THEN Nil
    ELSE IF IsQuorum({i} \cup {j \in ServerSet : matchIndex[j] >= max})
         THEN max
         ELSE FindMax(max-1)
  IN FindMax(Len(log))

ApplyLogEntry(entry, sm, smDomain) ==
  IF entry.cmd.type = Put THEN
    <<sm @@ (entry.cmd.key :> entry.cmd.value), smDomain \cup {entry.cmd.key}>>
  ELSE <<sm, smDomain>>

RECURSIVE ApplyLog(_, _, _, _, _)
ApplyLog(log, start, end, sm, smDomain) ==
  IF start > end THEN <<sm, smDomain>>
  ELSE LET result == ApplyLogEntry(log[start], sm, smDomain)
       IN ApplyLog(log, start+1, end, result[1], result[2])

AllReqs ==
  [type : {Put}, key : AllStrings, value : AllStrings] \cup
  [type : {Get}, key : AllStrings]

ServerState(server) ==
  [ state |-> servers[server].state,
    currentTerm |-> servers[server].currentTerm,
    log |-> servers[server].log,
    commitIndex |-> servers[server].commitIndex,
    nextIndex |-> [j \in ServerSet |-> servers[server].nextIndex[j]],
    matchIndex |-> [j \in ServerSet |-> servers[server].matchIndex[j]],
    votedFor |-> servers[server].votedFor,
    votesResponded |-> servers[server].votesResponded,
    votesGranted |-> servers[server].votesGranted,
    leader |-> servers[server].leader,
    sm |-> servers[server].sm,
    smDomain |-> servers[server].smDomain ]

ClientState(client) ==
  [ leader |-> clients[client].leader,
    req |-> clients[client].req,
    resp |-> clients[client].resp,
    reqIdx |-> clients[client].reqIdx ]

Init ==
  /\ servers = [i \in ServerSet |-> 
        [ state |-> Follower,
          currentTerm |-> 1,
          log |-> << >>,
          commitIndex |-> 0,
          nextIndex |-> [j \in ServerSet |-> 1],
          matchIndex |-> [j \in ServerSet |-> 0],
          votedFor |-> Nil,
          votesResponded |-> {},
          votesGranted |-> {},
          leader |-> Nil,
          sm |-> [k \in AllStrings |-> Nil],
          smDomain |-> {} ]]
  /\ clients = [c \in ClientSet |-> 
        [ leader |-> Nil,
          req |-> [type |-> Get, key |-> CHOOSE k \in AllStrings : TRUE],
          resp |-> [msuccess |-> FALSE, mresponse |-> [idx |-> 0, key |-> "", value |-> Nil, ok |-> FALSE]],
          reqIdx |-> 0 ]]
  /\ network = EmptyBag
  /\ crashed = {}
  /\ timer = [i \in ServerSet |-> LeaderTimeoutReset]

TypeInvariant ==
  /\ servers \in [ServerSet -> 
        [ state : {Follower, Candidate, Leader},
          currentTerm : Nat,
          log : Seq([term : Nat, cmd : AllReqs, client : ClientSet]),
          commitIndex : Nat,
          nextIndex : [ServerSet -> Nat],
          matchIndex : [ServerSet -> Nat],
          votedFor : ServerSet \cup {Nil},
          votesResponded : SUBSET ServerSet,
          votesGranted : SUBSET ServerSet,
          leader : ServerSet \cup {Nil},
          sm : [AllStrings -> AllStrings \cup {Nil}],
          smDomain : SUBSET AllStrings ]]
  /\ clients \in [ClientSet -> 
        [ leader : ServerSet \cup {Nil},
          req : AllReqs,
          resp : [msuccess : BOOLEAN, mresponse : [idx : Nat, key : AllStrings, value : AllStrings \cup {Nil}, ok : BOOLEAN]],
          reqIdx : Nat ]]
  /\ network \in Bag([ mtype : {RequestVoteRequest, RequestVoteResponse, AppendEntriesRequest, AppendEntriesResponse, ClientPutRequest, ClientPutResponse, ClientGetRequest, ClientGetResponse},
                      mterm : Nat,
                      mlastLogTerm : Nat,
                      mlastLogIndex : Nat,
                      mprevLogIndex : Nat,
                      mprevLogTerm : Nat,
                      mentries : Seq([term : Nat, cmd : AllReqs, client : ClientSet]),
                      mcommitIndex : Nat,
                      msuccess : BOOLEAN,
                      mmatchIndex : Nat,
                      mvoteGranted : BOOLEAN,
                      mcmd : AllReqs,
                      mresponse : [idx : Nat, key : AllStrings, value : AllStrings \cup {Nil}, ok : BOOLEAN],
                      mleaderHint : ServerSet \cup {Nil},
                      msource : NodeSet,
                      mdest : NodeSet ])
  /\ crashed \subseteq ServerSet
  /\ timer \in [ServerSet -> Nat]

RequestVote(server) ==
  /\ servers[server].state \in {Follower, Candidate}
  /\ timer[server] = 0
  /\ \/ servers[server].state = Follower
     \/ servers[server].state = Candidate
  /\ servers' = [servers EXCEPT ![server] = 
        [ state |-> Candidate,
          currentTerm |-> servers[server].currentTerm + 1,
          votedFor |-> server,
          votesResponded |-> {server},
          votesGranted |-> {server},
          leader |-> Nil ]]
  /\ network' = network \cup 
        [mtype :> RequestVoteRequest,
         mterm :> servers[server].currentTerm + 1,
         mlastLogTerm :> LastTerm(servers[server].log),
         mlastLogIndex :> Len(servers[server].log),
         msource :> server,
         mdest :> j] : j \in ServerSet \ {server}]
  /\ UNCHANGED <<clients, crashed, timer>>

HandleRequestVoteRequest(server, msg) ==
  /\ msg \in network
  /\ msg.mtype = RequestVoteRequest
  /\ msg.mdest = server
  /\ server \notin crashed
  /\ IF msg.mterm > servers[server].currentTerm THEN
        servers' = [servers EXCEPT ![server] = 
            [ state |-> Follower,
              currentTerm |-> msg.mterm,
              votedFor |-> Nil,
              leader |-> Nil ]]
    ELSE servers' = servers
  /\ LET logOK == \/ msg.mlastLogTerm > LastTerm(servers[server].log)
                 \/ /\ msg.mlastLogTerm = LastTerm(servers[server].log)
                    /\ msg.mlastLogIndex >= Len(servers[server].log)
        grant == /\ msg.mterm = servers[server].currentTerm
                 /\ logOK
                 /\ servers[server].votedFor \in {Nil, msg.msource}
    IN
    IF grant THEN
        servers'' = [servers' EXCEPT ![server] = [votedFor |-> msg.msource]]
    ELSE servers'' = servers'
  /\ network' = network \cup 
        [mtype :> RequestVoteResponse,
         mterm :> servers[server].currentTerm,
         mvoteGranted :> grant,
         msource :> server,
         mdest :> msg.msource]
  /\ UNCHANGED <<clients, crashed, timer>>

HandleRequestVoteResponse(server, msg) ==
  /\ msg \in network
  /\ msg.mtype = RequestVoteResponse
  /\ msg.mdest = server
  /\ server \notin crashed
  /\ IF msg.mterm > servers[server].currentTerm THEN
        servers' = [servers EXCEPT ![server] = 
            [ state |-> Follower,
              currentTerm |-> msg.mterm,
              votedFor |-> Nil,
              leader |-> Nil ]]
    ELSE servers' = servers
  /\ IF msg.mterm < servers[server].currentTerm THEN
        UNCHANGED servers
  ELSE
    /\ servers'' = [servers' EXCEPT ![server] = 
          [ votesResponded |-> servers[server].votesResponded \cup {msg.msource} ]]
    /\ IF msg.mvoteGranted THEN
          servers''' = [servers'' EXCEPT ![server] = 
              [ votesGranted |-> servers[server].votesGranted \cup {msg.msource} ]]
      ELSE servers''' = servers''
    /\ IF /\ servers[server].state = Candidate
          /\ IsQuorum(servers[server].votesGranted \cup {msg.msource}) THEN
          servers'''' = [servers''' EXCEPT ![server] = 
              [ state |-> Leader,
                nextIndex |-> [j \in ServerSet |-> Len(servers[server].log) + 1],
                matchIndex |-> [j \in ServerSet |-> 0],
                leader |-> server ]]
      ELSE servers'''' = servers'''
  /\ UNCHANGED <<clients, network, crashed, timer>>

HandleAppendEntriesRequest(server, msg) ==
  /\ msg \in network
  /\ msg.mtype = AppendEntriesRequest
  /\ msg.mdest = server
  /\ server \notin crashed
  /\ IF msg.mterm > servers[server].currentTerm THEN
        servers' = [servers EXCEPT ![server] = 
            [ state |-> Follower,
              currentTerm |-> msg.mterm,
              votedFor |-> Nil,
              leader |-> Nil ]]
    ELSE servers' = servers
  /\ LET logOK == \/ msg.mprevLogIndex = 0
                 \/ /\ msg.mprevLogIndex > 0
                    /\ msg.mprevLogIndex <= Len(servers[server].log)
                    /\ msg.mprevLogTerm = servers[server].log[msg.mprevLogIndex].term
    IN
    IF msg.mterm = servers[server].currentTerm THEN
        /\ servers'' = [servers' EXCEPT ![server] = 
              [ leader |-> msg.msource ]]
        /\ IF servers[server].state = Candidate THEN
              servers''' = [servers'' EXCEPT ![server] = [ state |-> Follower ]]
          ELSE servers''' = servers''
    ELSE servers''' = servers'
  /\ IF \/ msg.mterm < servers[server].currentTerm
        \/ /\ msg.mterm = servers[server].currentTerm
           /\ servers[server].state = Follower
           /\ ~logOK THEN
        network' = network \cup 
            [mtype :> AppendEntriesResponse,
             mterm :> servers[server].currentTerm,
             msuccess :> FALSE,
             mmatchIndex :> 0,
             msource :> server,
             mdest :> msg.msource]
    ELSE
        /\ LET newLog == 
                IF msg.mprevLogIndex + Len(msg.mentries) > Len(servers[server].log) THEN
                    SubSeq(servers[server].log, 1, msg.mprevLogIndex) \o msg.mentries
                ELSE servers[server].log
           newCommitIndex == 
                IF msg.mcommitIndex > servers[server].commitIndex THEN
                    Min({msg.mcommitIndex, Len(newLog)})
                ELSE servers[server].commitIndex
           result == ApplyLog(newLog, servers[server].commitIndex+1, newCommitIndex, servers[server].sm, servers[server].smDomain)
        IN
        /\ servers'''' = [servers''' EXCEPT ![server] = 
              [ log |-> newLog,
                commitIndex |-> newCommitIndex,
                sm |-> result[1],
                smDomain |-> result[2] ]]
        /\ network' = network \cup 
            [mtype :> AppendEntriesResponse,
             mterm :> servers[server].currentTerm,
             msuccess :> TRUE,
             mmatchIndex :> msg.mprevLogIndex + Len(msg.mentries),
             msource :> server,
             mdest :> msg.msource]
  /\ UNCHANGED <<clients, crashed, timer>>

HandleAppendEntriesResponse(server, msg) ==
  /\ msg \in network
  /\ msg.mtype = AppendEntriesResponse
  /\ msg.mdest = server
  /\ server \notin crashed
  /\ IF msg.mterm > servers[server].currentTerm THEN
        servers' = [servers EXCEPT ![server] = 
            [ state |-> Follower,
              currentTerm |-> msg.mterm,
              votedFor |-> Nil,
              leader |-> Nil ]]
    ELSE servers' = servers
  /\ IF msg.mterm < servers[server].currentTerm THEN
        UNCHANGED servers
  ELSE
    /\ IF msg.msuccess THEN
          servers'' = [servers' EXCEPT ![server] = 
              [ nextIndex |-> [nextIndex EXCEPT ![msg.msource] = msg.mmatchIndex + 1],
                matchIndex |-> [matchIndex EXCEPT ![msg.msource] = msg.mmatchIndex] ]]
      ELSE
          servers'' = [servers' EXCEPT ![server] = 
              [ nextIndex |-> [nextIndex EXCEPT ![msg.msource] = Max({servers[server].nextIndex[msg.msource] - 1, 1})] ]]
  /\ UNCHANGED <<clients, network, crashed, timer>>

SendAppendEntries(server) ==
  /\ servers[server].state = Leader
  /\ \E j \in ServerSet \ {server} :
        LET prevLogIndex == servers[server].nextIndex[j] - 1
            prevLogTerm == 
                IF prevLogIndex = 0 THEN 0
                ELSE servers[server].log[prevLogIndex].term
            entries == SubSeq(servers[server].log, servers[server].nextIndex[j], Len(servers[server].log))
        IN
        network' = network \cup 
            [mtype :> AppendEntriesRequest,
             mterm :> servers[server].currentTerm,
             mprevLogIndex :> prevLogIndex,
             mprevLogTerm :> prevLogTerm,
             mentries :> entries,
             mcommitIndex :> servers[server].commitIndex,
             msource :> server,
             mdest :> j]
  /\ UNCHANGED <<servers, clients, crashed, timer>>

AdvanceCommitIndex(server) ==
  /\ servers[server].state = Leader
  /\ LET N == FindMaxAgreeIndex(servers[server].log, server, servers[server].matchIndex)
    IN
    IF N > servers[server].commitIndex /\ servers[server].log[N].term = servers[server].currentTerm THEN
        servers' = [servers EXCEPT ![server] = [ commitIndex |-> N ]]
    ELSE servers' = servers
  /\ UNCHANGED <<clients, network, crashed, timer>>

ApplyCommittedEntries(server) ==
  /\ servers[server].commitIndex > servers[server].lastApplied
  /\ LET result == ApplyLog(servers[server].log, servers[server].lastApplied+1, servers[server].commitIndex, servers[server].sm, servers[server].smDomain)
    IN
    servers' = [servers EXCEPT ![server] = 
        [ lastApplied |-> servers[server].commitIndex,
          sm |-> result[1],
          smDomain |-> result[2] ]]
  /\ UNCHANGED <<clients, network, crashed, timer>>

HandleClientRequest(server, msg) ==
  /\ msg \in network
  /\ msg.mtype \in {ClientPutRequest, ClientGetRequest}
  /\ msg.mdest = server
  /\ server \notin crashed
  /\ IF servers[server].state = Leader THEN
        /\ LET entry == [term |-> servers[server].currentTerm, 
                         cmd |-> msg.mcmd,
                         client |-> msg.msource]
           newLog == servers[server].log \o <<entry>>
        IN
        /\ servers' = [servers EXCEPT ![server] = [ log |-> newLog ]]
        /\ network' = network \cup 
            [mtype :> IF msg.mcmd.type = Put THEN ClientPutResponse ELSE ClientGetResponse,
             msuccess :> TRUE,
             mresponse :> [idx |-> msg.mcmd.idx, key |-> msg.mcmd.key, value |-> Nil, ok |-> FALSE],
             mleaderHint :> server,
             msource :> server,
             mdest :> msg.msource]
    ELSE
        /\ network' = network \cup 
            [mtype :> IF msg.mcmd.type = Put THEN ClientPutResponse ELSE ClientGetResponse,
             msuccess :> FALSE,
             mresponse :> [idx |-> msg.mcmd.idx, key |-> msg.mcmd.key, value |-> Nil, ok |-> FALSE],
             mleaderHint :> servers[server].leader,
             msource :> server,
             mdest :> msg.msource]
        /\ UNCHANGED servers
  /\ UNCHANGED <<clients, crashed, timer>>

ClientSendRequest(client) ==
  /\ client \in ClientSet
  /\ LET leader == clients[client].leader
        req == clients[client].req
    IN
    IF leader = Nil THEN
        \E server \in ServerSet : 
            /\ network' = network \cup 
                [mtype :> IF req.type = Put THEN ClientPutRequest ELSE ClientGetRequest,
                 mcmd :> [req EXCEPT !.idx = clients[client].reqIdx],
                 msource :> client,
                 mdest :> server]
            /\ clients' = [clients EXCEPT ![client] = [ leader |-> server ]]
    ELSE
        network' = network \cup 
            [mtype :> IF req.type = Put THEN ClientPutRequest ELSE ClientGetRequest,
             mcmd :> [req EXCEPT !.idx = clients[client].reqIdx],
             msource :> client,
             mdest :> leader]
  /\ UNCHANGED <<servers, crashed, timer>>

ClientHandleResponse(client, msg) ==
  /\ msg \in network
  /\ msg.mtype \in {ClientPutResponse, ClientGetResponse}
  /\ msg.mdest = client
  /\ clients[client].reqIdx = msg.mresponse.idx
  /\ clients' = [clients EXCEPT ![client] = 
        [ resp |-> msg,
          leader |-> msg.mleaderHint ]]
  /\ IF msg.msuccess THEN
        clients'' = [clients' EXCEPT ![client] = [ reqIdx |-> clients[client].reqIdx + 1 ]]
    ELSE clients'' = clients'
  /\ UNCHANGED <<servers, network, crashed, timer>>

ServerCrash(server) ==
  /\ ExploreFail
  /\ server \in ServerSet \ crashed
  /\ Cardinality(crashed) < MaxNodeFail
  /\ crashed' = crashed \cup {server}
  /\ UNCHANGED <<servers, clients, network, timer>>

TimerDecrement ==
  /\ \A i \in ServerSet : 
        IF timer[i] > 0 THEN timer'[i] = timer[i] - 1 ELSE timer'[i] = 0
  /\ UNCHANGED <<servers, clients, network, crashed>>

Next ==
  \/ \E server \in ServerSet : RequestVote(server)
  \/ \E msg \in BagToList(network) : \E server \in ServerSet : HandleRequestVoteRequest(server, msg)
  \/ \E msg \in BagToList(network) : \E server \in ServerSet : HandleRequestVoteResponse(server, msg)
  \/ \E msg \in BagToList(network) : \E server \in ServerSet : HandleAppendEntriesRequest(server, msg)
  \/ \E msg \in BagToList(network) : \E server \in ServerSet : HandleAppendEntriesResponse(server, msg)
  \/ \E server \in ServerSet : SendAppendEntries(server)
  \/ \E server \in ServerSet : AdvanceCommitIndex(server)
  \/ \E server \in ServerSet : ApplyCommittedEntries(server)
  \/ \E msg \in BagToList(network) : \E server \in ServerSet : HandleClientRequest(server, msg)
  \/ \E client \in ClientSet : ClientSendRequest(client)
  \/ \E msg \in BagToList(network) : \E client \in ClientSet : ClientHandleResponse(client, msg)
  \/ \E server \in ServerSet : ServerCrash(server)
  \/ TimerDecrement

Spec == Init /\ [][Next]_vars

WF_vars(Next)

====