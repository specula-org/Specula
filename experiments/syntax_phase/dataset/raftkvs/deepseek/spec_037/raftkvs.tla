---- MODULE raftkvs ----
EXTENDS Sequences, Naturals, FiniteSets
CONSTANTS Servers, Clients, Command, Nil
VARIABLES currentTerm, state, log, commitIndex, votedFor, votesGranted, nextIndex, matchIndex, leader, network
vars == <<currentTerm, state, log, commitIndex, votedFor, votesGranted, nextIndex, matchIndex, leader, network>>
Init == 
    currentTerm = [n ∈ Servers |-> 0]
    ∧ state = [n ∈ Servers |-> "Follower"]
    ∧ log = [n ∈ Servers |-> <<>>]
    ∧ commitIndex = [n ∈ Servers |-> 0]
    ∧ votedFor = [n ∈ Servers |-> Nil]
    ∧ votesGranted = [n ∈ Servers |-> {}]
    ∧ nextIndex = [n ∈ Servers |-> [m ∈ Servers |-> 1]]
    ∧ matchIndex = [n ∈ Servers |-> [m ∈ Servers |-> 0]]
    ∧ leader = [n ∈ Servers |-> Nil]
    ∧ network = {}
LastTerm(logSeq) == IF logSeq = <<>> THEN 0 ELSE logSeq[Len(logSeq)]["term"]
IsQuorum(S) == Cardinality(S) > Cardinality(Servers) \div 2
Max(a,b) == IF a > b THEN a ELSE b
Min(a,b) == IF a < b THEN a ELSE b
ElectionTimeout(n) == 
    ∧ state[n] = "Follower"
    ∧ state' = [state EXCEPT ![n] = "Candidate"]
    ∧ currentTerm' = [currentTerm EXCEPT ![n] = currentTerm[n] + 1]
    ∧ votedFor' = [votedFor EXCEPT ![n] = n]
    ∧ votesGranted' = [votesGranted EXCEPT ![n] = {n}]
    ∧ leader' = [leader EXCEPT ![n] = Nil]
    ∧ network' = network ∪ { [ "mtype" |-> "RequestVoteRequest", "mterm" |-> currentTerm[n] + 1, "mlastLogTerm" |-> LastTerm(log[n]), "mlastLogIndex" |-> Len(log[n]), "msource" |-> n, "mdest" |-> m] : m ∈ Servers \ {n} }
    ∧ UNCHANGED <<log, commitIndex, nextIndex, matchIndex>>
HandleRequestVoteRequest(msg) == 
    LET n == msg["mdest"] IN
    LET j == msg["msource"] IN
    LET t == msg["mterm"] IN
    LET lastLogTerm == msg["mlastLogTerm"] IN
    LET lastLogIndex == msg["mlastLogIndex"] IN
    ∧ msg ∈ network
    ∧ IF t > currentTerm[n] THEN
        currentTerm' = [currentTerm EXCEPT ![n] = t]
        ∧ state' = [state EXCEPT ![n] = "Follower"]
        ∧ votedFor' = [votedFor EXCEPT ![n] = Nil]
        ∧ leader' = [leader EXCEPT ![n] = Nil]
        ∧ votesGranted' = [votesGranted EXCEPT ![n] = {}]
      ELSE
        currentTerm' = currentTerm
        ∧ state' = state
        ∧ votedFor' = votedFor
        ∧ leader' = leader
        ∧ votesGranted' = votesGranted
    ∧ LET logOK == ∨ lastLogTerm > LastTerm(log[n])
                   ∨ (lastLogTerm = LastTerm(log[n]) ∧ lastLogIndex ≥ Len(log[n])) IN
      LET grant == (t = currentTerm'[n] ∧ logOK ∧ votedFor'[n] ∈ {Nil, j}) IN
      IF grant THEN
          votedFor' = [votedFor' EXCEPT ![n] = j]
      ELSE
          TRUE
    ∧ network' = (network \ {msg}) ∪ { [ "mtype" |-> "RequestVoteResponse", "mterm" |-> currentTerm'[n], "mvoteGranted" |-> grant, "msource" |-> n, "mdest" |-> j] }
    ∧ UNCHANGED <<log, commitIndex, nextIndex, matchIndex>>
HandleRequestVoteResponse(msg) == 
    LET n == msg["mdest"] IN
    LET j == msg["msource"] IN
    LET t == msg["mterm"] IN
    LET voteGranted == msg["mvoteGranted"] IN
    ∧ msg ∈ network
    ∧ IF t > currentTerm[n] THEN
        currentTerm' = [currentTerm EXCEPT ![n] = t]
        ∧ state' = [state EXCEPT ![n] = "Follower"]
        ∧ votedFor' = [votedFor EXCEPT ![n] = Nil]
        ∧ leader' = [leader EXCEPT ![n] = Nil]
        ∧ votesGranted' = [votesGranted EXCEPT ![n] = {}]
        ∧ network' = network \ {msg}
        ∧ UNCHANGED <<log, commitIndex, nextIndex, matchIndex>>
      ELSE
        currentTerm' = currentTerm
        ∧ state' = state
        ∧ votedFor' = votedFor
        ∧ leader' = leader
        ∧ votesGranted' = votesGranted
        ∧ IF t = currentTerm[n] ∧ state[n] = "Candidate" THEN
            IF voteGranted THEN
                votesGranted' = [votesGranted' EXCEPT ![n] = votesGranted'[n] ∪ {j}]
            ELSE
                TRUE
            ∧ IF IsQuorum(votesGranted'[n]) THEN
                state' = [state' EXCEPT ![n] = "Leader"]
                ∧ nextIndex' = [nextIndex EXCEPT ![n] = [m ∈ Servers |-> Len(log[n]) + 1]]
                ∧ matchIndex' = [matchIndex EXCEPT ![n] = [m ∈ Servers |-> 0]]
                ∧ leader' = [leader EXCEPT ![n] = n]
              ELSE
                TRUE
          ELSE
            TRUE
        ∧ network' = network \ {msg}
        ∧ UNCHANGED <<log, commitIndex>>
HandleAppendEntriesRequest(msg) == 
    LET n == msg["mdest"] IN
    LET j == msg["msource"] IN
    LET t == msg["mterm"] IN
    LET prevLogIndex == msg["mprevLogIndex"] IN
    LET prevLogTerm == msg["mprevLogTerm"] IN
    LET entries == msg["mentries"] IN
    LET leaderCommit == msg["mcommitIndex"] IN
    ∧ msg ∈ network
    ∧ IF t > currentTerm[n] THEN
        currentTerm' = [currentTerm EXCEPT ![n] = t]
        ∧ state' = [state EXCEPT ![n] = "Follower"]
        ∧ votedFor' = [votedFor EXCEPT ![n] = Nil]
        ∧ leader' = [leader EXCEPT ![n] = Nil]
        ∧ votesGranted' = [votesGranted EXCEPT ![n] = {}]
      ELSE
        currentTerm' = currentTerm
        ∧ state' = state
        ∧ votedFor' = votedFor
        ∧ leader' = leader
        ∧ votesGranted' = votesGranted
    ∧ LET logOK == ∨ prevLogIndex = 0
                   ∨ (prevLogIndex > 0 ∧ prevLogIndex ≤ Len(log[n]) ∧ log[n][prevLogIndex]["term"] = prevLogTerm) IN
    ∧ IF t = currentTerm'[n] THEN
        leader' = [leader' EXCEPT ![n] = j]
        ∧ IF state[n] = "Candidate" THEN
            state' = [state' EXCEPT ![n] = "Follower"]
          ELSE
            TRUE
      ELSE
        TRUE
    ∧ IF t = currentTerm'[n] ∧ logOK THEN
        log' = [log EXCEPT ![n] = SubSeq(log[n], 1, prevLogIndex) ◦ entries]
        ∧ commitIndex' = [commitIndex EXCEPT ![n] = Min(leaderCommit, Len(log'[n]))]
        ∧ network' = (network \ {msg}) ∪ { [ "mtype" |-> "AppendEntriesResponse", "mterm" |-> currentTerm'[n], "msuccess" |-> TRUE, "mmatchIndex" |-> prevLogIndex + Len(entries), "msource" |-> n, "mdest" |-> j] }
      ELSE
        log' = log
        ∧ commitIndex' = commitIndex
        ∧ network' = (network \ {msg}) ∪ { [ "mtype" |-> "AppendEntriesResponse", "mterm" |-> currentTerm'[n], "msuccess" |-> FALSE, "mmatchIndex" |-> 0, "msource" |-> n, "mdest" |-> j] }
    ∧ UNCHANGED <<votedFor, votesGranted, nextIndex, matchIndex>>
HandleAppendEntriesResponse(msg) == 
    LET n == msg["mdest"] IN
    LET j == msg["msource"] IN
    LET t == msg["mterm"] IN
    LET success == msg["msuccess"] IN
    LET matchIndex_val == msg["mmatchIndex"] IN
    ∧ msg ∈ network
    ∧ state[n] = "Leader"
    ∧ IF t > currentTerm[n] THEN
        currentTerm' = [currentTerm EXCEPT ![n] = t]
        ∧ state' = [state EXCEPT ![n] = "Follower"]
        ∧ votedFor' = [votedFor EXCEPT ![n] = Nil]
        ∧ leader' = [leader EXCEPT ![n] = Nil]
        ∧ votesGranted' = [votesGranted EXCEPT ![n] = {}]
        ∧ network' = network \ {msg}
        ∧ UNCHANGED <<log, commitIndex, nextIndex, matchIndex>>
      ELSE
        currentTerm' = currentTerm
        ∧ state' = state
        ∧ votedFor' = votedFor
        ∧ leader' = leader
        ∧ votesGranted' = votesGranted
        ∧ IF success THEN
            nextIndex' = [nextIndex EXCEPT ![n][j] = matchIndex_val + 1]
            ∧ matchIndex' = [matchIndex EXCEPT ![n][j] = matchIndex_val]
          ELSE
            nextIndex' = [nextIndex EXCEPT ![n][j] = Max(1, nextIndex[n][j] - 1)]
            ∧ matchIndex' = matchIndex
        ∧ network' = network \ {msg}
        ∧ UNCHANGED <<log, commitIndex>>
SendAppendEntries(n) == 
    ∧ state[n] = "Leader"
    ∧ LET entriesToSend(m) == SubSeq(log[n], nextIndex[n][m], Len(log[n])) IN
    ∧ LET prevLogIndex(m) == nextIndex[n][m] - 1 IN
    ∧ LET prevLogTerm(m) == IF prevLogIndex(m) > 0 THEN log[n][prevLogIndex(m)]["term"] ELSE 0 IN
    ∧ network' = network ∪ { [ "mtype" |-> "AppendEntriesRequest", "mterm" |-> currentTerm[n], "mprevLogIndex" |-> prevLogIndex(m), "mprevLogTerm" |-> prevLogTerm(m), "mentries" |-> entriesToSend(m), "mcommitIndex" |-> commitIndex[n], "msource" |-> n, "mdest" |-> m] : m ∈ Servers \ {n} }
    ∧ UNCHANGED <<currentTerm, state, log, commitIndex, votedFor, votesGranted, nextIndex, matchIndex, leader>>
AdvanceCommitIndex(n) == 
    ∧ state[n] = "Leader"
    ∧ LET possibleN == {k ∈ {commitIndex[n] + 1 .. Len(log[n])} : IsQuorum({m ∈ Servers : matchIndex[n][m] ≥ k}) ∧ log[n][k]["term"] = currentTerm[n]} IN
    ∧ IF possibleN ≠ {} THEN
        LET N == CHOOSE k ∈ possibleN : ∀ l ∈ possibleN : l ≤ k IN
        commitIndex' = [commitIndex EXCEPT ![n] = N]
      ELSE
        commitIndex' = commitIndex
    ∧ UNCHANGED <<currentTerm, state, log, votedFor, votesGranted, nextIndex, matchIndex, leader, network>>
HandleClientRequest(msg) == 
    LET n == msg["mdest"] IN
    LET j == msg["msource"] IN
    LET cmd == msg["mcmd"] IN
    ∧ msg ∈ network
    ∧ IF state[n] = "Leader" THEN
        LET newEntry == [ "term" |-> currentTerm[n], "cmd" |-> cmd] IN
        log' = [log EXCEPT ![n] = log[n] ◦ <<newEntry>>]
        ∧ network' = network \ {msg}
        ∧ UNCHANGED <<currentTerm, state, commitIndex, votedFor, votesGranted, nextIndex, matchIndex, leader>>
      ELSE
        network' = (network \ {msg}) ∪ { [ "mtype" |-> IF cmd["type"] = "Put" THEN "ClientPutResponse" ELSE "ClientGetResponse", "msuccess" |-> FALSE, "mresponse" |-> [ "idx" |-> cmd["idx"], "key" |-> cmd["key"]], "mleaderHint" |-> leader[n], "msource" |-> n, "mdest" |-> j] }
        ∧ UNCHANGED <<currentTerm, state, log, commitIndex, votedFor, votesGranted, nextIndex, matchIndex, leader>>
ClientSendRequest(c) == 
    ∧ ∃ n ∈ Servers :
        LET cmd == [ "type" |-> CHOOSE type ∈ {"Put", "Get"} : TRUE, "key" |-> CHOOSE k : TRUE, "value" |-> CHOOSE v : TRUE, "idx" |-> CHOOSE i ∈ Nat : TRUE] IN
        network' = network ∪ { [ "mtype" |-> IF cmd["type"] = "Put" THEN "ClientPutRequest" ELSE "ClientGetRequest", "mcmd" |-> cmd, "msource" |-> c, "mdest" |-> n] }
    ∧ UNCHANGED <<currentTerm, state, log, commitIndex, votedFor, votesGranted, nextIndex, matchIndex, leader>>
ClientReceiveResponse(c) == 
    ∧ ∃ msg ∈ network : msg["mdest"] = c ∧ msg["mtype"] ∈ {"ClientPutResponse", "ClientGetResponse"}
    ∧ network' = network \ {msg}
    ∧ UNCHANGED <<currentTerm, state, log, commitIndex, votedFor, votesGranted, nextIndex, matchIndex, leader>>
DropMessage(msg) == 
    ∧ msg ∈ network
    ∧ network' = network \ {msg}
    ∧ UNCHANGED <<currentTerm, state, log, commitIndex, votedFor, votesGranted, nextIndex, matchIndex, leader>>
Next == 
    ∨ ∃ n ∈ Servers : ElectionTimeout(n)
    ∨ ∃ msg ∈ network : HandleRequestVoteRequest(msg)
    ∨ ∃ msg ∈ network : HandleRequestVoteResponse(msg)
    ∨ ∃ msg ∈ network : HandleAppendEntriesRequest(msg)
    ∨ ∃ msg ∈ network : HandleAppendEntriesResponse(msg)
    ∨ ∃ msg ∈ network : HandleClientRequest(msg)
    ∨ ∃ n ∈ Servers : SendAppendEntries(n)
    ∨ ∃ n ∈ Servers : AdvanceCommitIndex(n)
    ∨ ∃ c ∈ Clients : ClientSendRequest(c)
    ∨ ∃ c ∈ Clients : ClientReceiveResponse(c)
    ∨ ∃ msg ∈ network : DropMessage(msg)
Spec == Init ∧ [][Next]_vars
====