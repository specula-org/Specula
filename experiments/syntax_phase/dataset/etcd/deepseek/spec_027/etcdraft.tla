---- MODULE etcdraft ----
EXTENDS Naturals, Sequences, FiniteSets, TLC
CONSTANTS Nodes, NodeFaults, Keys, Values, Nil, DefaultValue
VARIABLES now, state, currentTerm, votedFor, log, commitIndex, lastApplied, 
          nextIndex, matchIndex, leader, votesReceived, electionDeadline, 
          heartbeatDeadline, msgs, sm, clientRequests, clientResponses

vars == <<now, state, currentTerm, votedFor, log, commitIndex, lastApplied, 
          nextIndex, matchIndex, leader, votesReceived, electionDeadline, 
          heartbeatDeadline, msgs, sm, clientRequests, clientResponses>>

NodeState == {"Follower", "Candidate", "Leader"}
MessageType == {"RequestVote", "RequestVoteResponse", "AppendEntries", 
                "AppendEntriesResponse", "ClientRequest", "ClientResponse", 
                "TimeoutNow", "ReadIndex", "ReadIndexResp"}

ElectionTimeout == 10
HeartbeatTimeout == 2
Majority(n) == Cardinality(n) \div 2 + 1

Init == 
    /\ now = 0
    /\ state = [n \in Nodes |-> "Follower"]
    /\ currentTerm = [n \in Nodes |-> 0]
    /\ votedFor = [n \in Nodes |-> Nil]
    /\ log = [n \in Nodes |-> <<>>]
    /\ commitIndex = [n \in Nodes |-> 0]
    /\ lastApplied = [n \in Nodes |-> 0]
    /\ nextIndex = [n \in Nodes |-> [m \in Nodes |-> 1]]
    /\ matchIndex = [n \in Nodes |-> [m \in Nodes |-> 0]]
    /\ leader = [n \in Nodes |-> Nil]
    /\ votesReceived = [n \in Nodes |-> {}]
    /\ electionDeadline = [n \in Nodes |-> ElectionTimeout]
    /\ heartbeatDeadline = [n \in Nodes |-> HeartbeatTimeout]
    /\ msgs = {}
    /\ sm = [n \in Nodes |-> [k \in Keys |-> DefaultValue]]
    /\ clientRequests = {}
    /\ clientResponses = {}

Type(entry) == IF "type" \in DOMAIN entry THEN entry.type ELSE "Nop"
Key(entry) == IF "key" \in DOMAIN entry THEN entry.key ELSE Nil
Value(entry) == IF "value" \in DOMAIN entry THEN entry.value ELSE Nil

IsLeader(node) == state[node] = "Leader"
LastLogTerm(node) == IF Len(log[node]) > 0 THEN log[node][Len(log[node])].term ELSE 0
LastLogIndex(node) == Len(log[node])
LogTerm(node, index) == IF index > 0 /\ index <= Len(log[node]) THEN log[node][index].term ELSE 0

LogUpToDate(candidateTerm, candidateIndex, node) == 
    candidateTerm > LastLogTerm(node)
    \/ (candidateTerm = LastLogTerm(node) /\ candidateIndex >= LastLogIndex(node))

GrantVote(node, candidate, term, lastLogIndex, lastLogTerm) == 
    /\ currentTerm[node] <= term
    /\ (votedFor[node] = Nil \/ votedFor[node] = candidate)
    /\ LogUpToDate(term, lastLogIndex, node)

AppendEntriesPrecondition(node, term, leaderId, prevLogIndex, prevLogTerm) == 
    /\ currentTerm[node] <= term
    /\ (leader[node] = Nil \/ leader[node] = leaderId)
    /\ prevLogIndex = 0 \/ (prevLogIndex <= Len(log[node]) /\ log[node][prevLogIndex].term = prevLogTerm)

AdvanceCommitIndex(node, leaderCommit) == 
    LET newCommitIndex == IF leaderCommit > commitIndex[node] THEN Min(leaderCommit, LastLogIndex(node)) ELSE commitIndex[node]
    IN commitIndex[node] < newCommitIndex

ApplyLogEntry(node, index) == 
    IF index > lastApplied[node] /\ index <= commitIndex[node] /\ index <= Len(log[node])
    THEN LET entry == log[node][index] 
         IN IF Type(entry.op) = "Put" 
            THEN sm[node]' = [sm[node] EXCEPT ![Key(entry.op)] = Value(entry.op)]
            ELSE UNCHANGED sm[node]
    ELSE UNCHANGED sm[node]

Send(src, dest, type, term, candidate, lastLogIndex, lastLogTerm, leader, prevLogIndex, prevLogTerm, entries, leaderCommit, success, matchIndex, conflictIndex, conflictTerm, op) == 
    LET msg == [ from |-> src, 
                to |-> dest, 
                type |-> type, 
                term |-> term, 
                candidate |-> candidate, 
                lastLogIndex |-> lastLogIndex, 
                lastLogTerm |-> lastLogTerm, 
                leader |-> leader, 
                prevLogIndex |-> prevLogIndex, 
                prevLogTerm |-> prevLogTerm, 
                entries |-> entries, 
                leaderCommit |-> leaderCommit, 
                success |-> success, 
                matchIndex |-> matchIndex, 
                conflictIndex |-> conflictIndex, 
                conflictTerm |-> conflictTerm, 
                op |-> op ]
    IN IF dest \in NodeFaults THEN msgs' = msgs ELSE msgs' = msgs \union {msg}

RequestVote(node) == 
    /\ state[node] \in {"Follower", "Candidate"}
    /\ electionDeadline[node] <= now
    /\ state' = [state EXCEPT ![node] = "Candidate"]
    /\ currentTerm' = [currentTerm EXCEPT ![node] = currentTerm[node] + 1]
    /\ votedFor' = [votedFor EXCEPT ![node] = node]
    /\ votesReceived' = [votesReceived EXCEPT ![node] = {node}]
    /\ electionDeadline' = [electionDeadline EXCEPT ![node] = now + ElectionTimeout]
    /\ \A dest \in Nodes \ {node}: 
        Send(node, dest, "RequestVote", currentTerm[node] + 1, node, LastLogIndex(node), LastLogTerm(node), Nil, 0, 0, <<>>, 0, FALSE, 0, 0, 0, [type |-> "Nop"])
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, leader, heartbeatDeadline, sm, clientRequests, clientResponses>>

ReceiveRequestVote(node, msg) == 
    /\ msg \in msgs
    /\ msg.type = "RequestVote"
    /\ GrantVote(node, msg.candidate, msg.term, msg.lastLogIndex, msg.lastLogTerm)
    /\ votedFor' = [votedFor EXCEPT ![node] = msg.candidate]
    /\ currentTerm' = [currentTerm EXCEPT ![node] = msg.term]
    /\ electionDeadline' = [electionDeadline EXCEPT ![node] = now + ElectionTimeout]
    /\ state' = [state EXCEPT ![node] = "Follower"]
    /\ leader' = [leader EXCEPT ![node] = Nil]
    /\ Send(node, msg.from, "RequestVoteResponse", currentTerm[node], msg.candidate, 0, 0, Nil, 0, 0, <<>>, 0, TRUE, 0, 0, 0, [type |-> "Nop"])
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, votesReceived, heartbeatDeadline, sm, clientRequests, clientResponses>>

ReceiveRequestVoteResponse(node, msg) == 
    /\ msg \in msgs
    /\ msg.type = "RequestVoteResponse"
    /\ state[node] = "Candidate"
    /\ currentTerm[node] = msg.term
    /\ votesReceived' = [votesReceived EXCEPT ![node] = @ \union {msg.from}]
    /\ IF Cardinality(votesReceived'[node]) >= Majority(Nodes)
       THEN /\ state' = [state EXCEPT ![node] = "Leader"]
            /\ leader' = [leader EXCEPT ![node] = node]
            /\ nextIndex' = [nextIndex EXCEPT ![node] = [m \in Nodes |-> LastLogIndex(node) + 1]]
            /\ matchIndex' = [matchIndex EXCEPT ![node] = [m \in Nodes |-> 0]]
            /\ heartbeatDeadline' = [heartbeatDeadline EXCEPT ![node] = now + HeartbeatTimeout]
            /\ \A dest \in Nodes \ {node}: 
                   Send(node, dest, "AppendEntries", currentTerm[node], Nil, 0, 0, node, LastLogIndex(node), LastLogTerm(node), <<>>, commitIndex[node], FALSE, 0, 0, 0, [type |-> "Nop"])
       ELSE UNCHANGED state
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied, electionDeadline, sm, clientRequests, clientResponses>>

LeaderHeartbeat(node) == 
    /\ IsLeader(node)
    /\ heartbeatDeadline[node] <= now
    /\ heartbeatDeadline' = [heartbeatDeadline EXCEPT ![node] = now + HeartbeatTimeout]
    /\ \A dest \in Nodes \ {node}: 
           Send(node, dest, "AppendEntries", currentTerm[node], Nil, 0, 0, node, LastLogIndex(node), LastLogTerm(node), <<>>, commitIndex[node], FALSE, 0, 0, 0, [type |-> "Nop"])
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, leader, votesReceived, electionDeadline, sm, clientRequests, clientResponses>>

LeaderAppend(node, op) == 
    /\ IsLeader(node)
    /\ \E clientReq \in clientRequests: 
        /\ clientReq \notin DOMAIN clientResponses
        /\ op = clientReq
    /\ log' = [log EXCEPT ![node] = @ \o <<[term |-> currentTerm[node], op |-> op]>>]
    /\ nextIndex' = [nextIndex EXCEPT ![node][node] = @ + 1]
    /\ matchIndex' = [matchIndex EXCEPT ![node][node] = @ + 1]
    /\ \A dest \in Nodes \ {node}: 
           LET prevLogIndex == nextIndex[node][dest] - 1
           IN Send(node, dest, "AppendEntries", currentTerm[node], Nil, 0, 0, node, prevLogIndex, LogTerm(node, prevLogIndex), <<[term |-> currentTerm[node], op |-> op]>>, commitIndex[node], FALSE, 0, 0, 0, op)
    /\ clientRequests' = clientRequests
    /\ clientResponses' = clientResponses
    /\ UNCHANGED <<now, state, currentTerm, votedFor, commitIndex, lastApplied, leader, votesReceived, electionDeadline, heartbeatDeadline, sm>>

ReceiveAppendEntries(node, msg) == 
    /\ msg \in msgs
    /\ msg.type = "AppendEntries"
    /\ AppendEntriesPrecondition(node, msg.term, msg.leader, msg.prevLogIndex, msg.prevLogTerm)
    /\ currentTerm' = [currentTerm EXCEPT ![node] = msg.term]
    /\ state' = [state EXCEPT ![node] = "Follower"]
    /\ leader' = [leader EXCEPT ![node] = msg.leader]
    /\ electionDeadline' = [electionDeadline EXCEPT ![node] = now + ElectionTimeout]
    /\ IF msg.prevLogIndex > 0 /\ (msg.prevLogIndex > Len(log[node]) \/ LogTerm(node, msg.prevLogIndex) # msg.prevLogTerm)
       THEN /\ LET conflictIndex == IF msg.prevLogIndex > Len(log[node]) THEN Len(log[node]) + 1 ELSE msg.prevLogIndex
                   conflictTerm == IF msg.prevLogIndex > 0 /\ msg.prevLogIndex <= Len(log[node]) THEN log[node][msg.prevLogIndex].term ELSE 0
                IN Send(node, msg.from, "AppendEntriesResponse", currentTerm[node], Nil, 0, 0, Nil, 0, 0, <<>>, 0, FALSE, 0, conflictIndex, conflictTerm, [type |-> "Nop"])
            /\ UNCHANGED log
    ELSE 
        /\ LET newLog == IF msg.entries = <<>> THEN log[node]
                         ELSE SubSeq(log[node], 1, msg.prevLogIndex) \o msg.entries
             newLastLogIndex == Len(newLog)
             newCommitIndex == Min(msg.leaderCommit, newLastLogIndex)
          IN
           /\ log' = [log EXCEPT ![node] = newLog]
           /\ IF newCommitIndex > commitIndex[node] 
              THEN commitIndex' = [commitIndex EXCEPT ![node] = newCommitIndex]
              ELSE UNCHANGED commitIndex
           /\ Send(node, msg.from, "AppendEntriesResponse", currentTerm[node], Nil, 0, 0, Nil, 0, 0, <<>>, 0, TRUE, newLastLogIndex, 0, 0, [type |-> "Nop"])
    /\ UNCHANGED <<votedFor, lastApplied, nextIndex, matchIndex, votesReceived, heartbeatDeadline, sm, clientRequests, clientResponses>>

ReceiveAppendEntriesResponse(node, msg) == 
    /\ msg \in msgs
    /\ msg.type = "AppendEntriesResponse"
    /\ IsLeader(node)
    /\ msg.term = currentTerm[node]
    /\ IF msg.success
       THEN /\ nextIndex' = [nextIndex EXCEPT ![node][msg.from] = msg.matchIndex + 1]
            /\ matchIndex' = [matchIndex EXCEPT ![node][msg.from] = msg.matchIndex]
            /\ LET N == CHOOSE m \in { k \in Nat : Cardinality({n \in Nodes : matchIndex[node][n] >= k}) >= Majority(Nodes) } : TRUE
               IN IF N > commitIndex[node] /\ LogTerm(node, N) = currentTerm[node]
                  THEN commitIndex' = [commitIndex EXCEPT ![node] = N]
                  ELSE UNCHANGED commitIndex
       ELSE /\ nextIndex' = [nextIndex EXCEPT ![node][msg.from] = msg.conflictIndex]
            /\ UNCHANGED matchIndex
    /\ UNCHANGED <<state, currentTerm, votedFor, log, lastApplied, leader, votesReceived, electionDeadline, heartbeatDeadline, sm, clientRequests, clientResponses>>

ApplyLog(node) == 
    /\ lastApplied[node] < commitIndex[node]
    /\ lastApplied' = [lastApplied EXCEPT ![node] = lastApplied[node] + 1]
    /\ ApplyLogEntry(node, lastApplied[node] + 1)
    /\ UNCHANGED <<now, state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, leader, votesReceived, electionDeadline, heartbeatDeadline, msgs, clientRequests, clientResponses>>

ClientRequest(node, op) == 
    /\ IsLeader(node)
    /\ clientRequests' = clientRequests \union {op}
    /\ clientResponses' = clientResponses
    /\ UNCHANGED <<now, state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, leader, votesReceived, electionDeadline, heartbeatDeadline, msgs, sm>>

ClientResponse(node, op) == 
    /\ op \in clientRequests
    /\ op \notin DOMAIN clientResponses
    /\ \E idx \in 1..Len(log[node]):
        /\ log[node][idx].op = op
        /\ idx <= lastApplied[node]
    /\ clientResponses' = [clientResponses EXCEPT ![op] = sm[node][Key(op)]]
    /\ UNCHANGED <<now, state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, leader, votesReceived, electionDeadline, heartbeatDeadline, msgs, sm, clientRequests>>

AdvanceTime == 
    /\ now' \in { t \in Nat : t > now }
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, leader, votesReceived, msgs, sm, clientRequests, clientResponses>>

Next == 
    \/ \E node \in Nodes: RequestVote(node)
    \/ \E node \in Nodes: \E msg \in msgs: 
        \/ (msg.type = "RequestVote" /\ ReceiveRequestVote(node, msg))
        \/ (msg.type = "RequestVoteResponse" /\ ReceiveRequestVoteResponse(node, msg))
        \/ (msg.type = "AppendEntries" /\ ReceiveAppendEntries(node, msg))
        \/ (msg.type = "AppendEntriesResponse" /\ ReceiveAppendEntriesResponse(node, msg))
    \/ \E node \in Nodes: 
        \/ LeaderHeartbeat(node)
        \/ ApplyLog(node)
    \/ \E node \in Nodes: \E op \in [type: {"Put","Get"}, key: Keys, value: Values]:
        \/ ClientRequest(node, op)
        \/ ClientResponse(node, op)
    \/ \E node \in Nodes: LeaderAppend(node, [type |-> "Nop"])
    \/ AdvanceTime

TypeInvariant == 
    /\ state \in [Nodes -> NodeState]
    /\ currentTerm \in [Nodes -> Nat]
    /\ votedFor \in [Nodes -> Nodes \union {Nil}]
    /\ log \in [Nodes -> Seq([term: Nat, op: [type: {"Put","Get","Nop"}, key: Keys, value: Values]])]
    /\ commitIndex \in [Nodes -> Nat]
    /\ lastApplied \in [Nodes -> Nat]
    /\ nextIndex \in [Nodes -> [Nodes -> Nat]]
    /\ matchIndex \in [Nodes -> [Nodes -> Nat]]
    /\ leader \in [Nodes -> Nodes \union {Nil}]
    /\ votesReceived \in [Nodes -> SUBSET Nodes]
    /\ electionDeadline \in [Nodes -> Nat]
    /\ heartbeatDeadline \in [Nodes -> Nat]
    /\ msgs \subseteq [from: Nodes, to: Nodes, type: MessageType, term: Nat, candidate: Nodes \union {Nil}, lastLogIndex: Nat, lastLogTerm: Nat, leader: Nodes \union {Nil}, prevLogIndex: Nat, prevLogTerm: Nat, entries: Seq([term: Nat, op: [type: {"Put","Get","Nop"}, key: Keys, value: Values]]), leaderCommit: Nat, success: BOOLEAN, matchIndex: Nat, conflictIndex: Nat, conflictTerm: Nat, op: [type: {"Put","Get","Nop"}, key: Keys, value: Values]]]
    /\ sm \in [Nodes -> [Keys -> Values]]
    /\ clientRequests \subseteq [type: {"Put","Get"}, key: Keys, value: Values]
    /\ clientResponses \in [clientRequests -> Values]

Safety == 
    \A n1, n2 \in Nodes: 
        /\ commitIndex[n1] <= LastLogIndex(n1)
        /\ lastApplied[n1] <= commitIndex[n1]
        /\ (state[n1] = "Leader" /\ state[n2] = "Leader" => currentTerm[n1] # currentTerm[n2])
        /\ \A idx \in 1..Min(commitIndex[n1], commitIndex[n2]):
            IF idx <= Len(log[n1]) /\ idx <= Len(log[n2])
            THEN log[n1][idx] = log[n2][idx]

Termination == 
    WF_vars(Next)

Spec == Init /\ [][Next]_vars /\ Termination

====