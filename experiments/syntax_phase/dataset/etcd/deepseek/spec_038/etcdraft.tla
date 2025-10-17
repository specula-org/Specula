---- MODULE etcdraft ----
EXTENDS Naturals, Sequences, FiniteSets, TLC
CONSTANTS Nodes, Keys, Values, Clients, ReqIds
Null == CHOOSE n : n \notin (Nodes \union Clients \union ReqIds \union Nat)
VARIABLES state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, messages, sm, pendingRequests, votesGranted
vars == <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, messages, sm, pendingRequests, votesGranted>>
RequestVote == [type: {"RequestVote"}, term: Nat, candidateId: Nodes, lastLogIndex: Nat, lastLogTerm: Nat]
RequestVoteResponse == [type: {"RequestVoteResponse"}, term: Nat, voteGranted: BOOLEAN, from: Nodes]
LogEntry == [term: Nat, op: [type: {"Put","Get","Delete"}, key: Keys, value: Values], client: Clients, reqId: ReqIds]
AppendEntries == [type: {"AppendEntries"}, term: Nat, leaderId: Nodes, prevLogIndex: Nat, prevLogTerm: Nat, entries: Seq(LogEntry), leaderCommit: Nat]
AppendEntriesResponse == [type: {"AppendEntriesResponse"}, term: Nat, success: BOOLEAN, from: Nodes, matchIndex: Nat]
ClientRequest == [type: {"ClientRequest"}, client: Clients, reqId: ReqIds, op: [type: {"Put","Get","Delete"}, key: Keys, value: Values]]
ClientResponse == [type: {"ClientResponse"}, client: Clients, reqId: ReqIds, result: Values \union {"ok"}]
Init == 
    state = [n \in Nodes |-> "Follower"] /\
    currentTerm = [n \in Nodes |-> 0] /\
    votedFor = [n \in Nodes |-> Null] /\
    log = [n \in Nodes |-> <<>>] /\
    commitIndex = [n \in Nodes |-> 0] /\
    lastApplied = [n \in Nodes |-> 0] /\
    nextIndex = [n \in Nodes |-> [m \in Nodes |-> 1]] /\
    matchIndex = [n \in Nodes |-> [m \in Nodes |-> 0]] /\
    leaderId = [n \in Nodes |-> Null] /\
    messages = {} /\
    sm = [n \in Nodes |-> [k \in Keys |-> Null]] /\
    pendingRequests = {} /\
    votesGranted = [n \in Nodes |-> 0]
ElectionTimeout(n) ==
    /\ state[n] \in {"Follower", "Candidate"}
    /\ state' = [state EXCEPT ![n] = "Candidate"]
    /\ currentTerm' = [currentTerm EXCEPT ![n] = currentTerm[n] + 1]
    /\ votedFor' = [votedFor EXCEPT ![n] = n]
    /\ votesGranted' = [votesGranted EXCEPT ![n] = 1]
    /\ \E lastLogIndex \in Nat: lastLogIndex = Len(log[n])
    /\ \E lastLogTerm \in Nat: lastLogTerm = IF lastLogIndex = 0 THEN 0 ELSE log[n][lastLogIndex].term
    /\ messages' = messages \cup {[type |-> "RequestVote", term |-> currentTerm[n] + 1, candidateId |-> n, lastLogIndex |-> lastLogIndex, lastLogTerm |-> lastLogTerm]}
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, sm, pendingRequests>>
ReceiveRequestVote(n, m) ==
    /\ m \in messages
    /\ m.type = "RequestVote"
    /\ IF m.term < currentTerm[n]
        THEN
            /\ LET resp == [type |-> "RequestVoteResponse", term |-> currentTerm[n], voteGranted |-> FALSE, from |-> n]
               IN messages' = (messages \ {m}) \cup {resp}
            /\ UNCHANGED <<state, currentTerm, votedFor, votesGranted>>
        ELSE
            /\ ( \/ (m.term > currentTerm[n])
                    /\ currentTerm' = [currentTerm EXCEPT ![n] = m.term]
                    /\ state' = [state EXCEPT ![n] = "Follower"]
                    /\ votedFor' = [votedFor EXCEPT ![n] = Null]
                    /\ votesGranted' = [votesGranted EXCEPT ![n] = 0]
                \/ UNCHANGED <<currentTerm, state, votedFor, votesGranted>>
              )
            /\ ( \/ (votedFor[n] = Null \/ votedFor[n] = m.candidateId)
                    /\ \E lastLogIndex \in Nat: lastLogIndex = Len(log[n])
                    /\ \E lastLogTerm \in Nat: lastLogTerm = IF lastLogIndex = 0 THEN 0 ELSE log[n][lastLogIndex].term
                    /\ ( \/ (m.lastLogTerm > lastLogTerm) \/ (m.lastLogTerm = lastLogTerm /\ m.lastLogIndex >= lastLogIndex)
                           /\ votedFor' = [votedFor EXCEPT ![n] = m.candidateId]
                           /\ LET resp == [type |-> "RequestVoteResponse", term |-> currentTerm'[n], voteGranted |-> TRUE, from |-> n]
                              IN messages' = (messages \ {m}) \cup {resp}
                       \/ ~((m.lastLogTerm > lastLogTerm) \/ (m.lastLogTerm = lastLogTerm /\ m.lastLogIndex >= lastLogIndex))
                           /\ LET resp == [type |-> "RequestVoteResponse", term |-> currentTerm'[n], voteGranted |-> FALSE, from |-> n]
                              IN messages' = (messages \ {m}) \cup {resp}
                           /\ UNCHANGED votedFor
                 )
                \/ ~(votedFor[n] = Null \/ votedFor[n] = m.candidateId)
                    /\ LET resp == [type |-> "RequestVoteResponse", term |-> currentTerm'[n], voteGranted |-> FALSE, from |-> n]
                       IN messages' = (messages \ {m}) \cup {resp}
                    /\ UNCHANGED votedFor
              )
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, sm, pendingRequests, votesGranted>>
ReceiveRequestVoteResponse(n, m) ==
    /\ m \in messages
    /\ m.type = "RequestVoteResponse"
    /\ state[n] = "Candidate"
    /\ m.term = currentTerm[n]
    /\ IF m.voteGranted
        THEN
            /\ votesGranted' = [votesGranted EXCEPT ![n] = @ + 1]
            /\ IF votesGranted'[n] > Cardinality(Nodes) \div 2
                THEN
                    /\ state' = [state EXCEPT ![n] = "Leader"]
                    /\ leaderId' = [leaderId EXCEPT ![n] = n]
                    /\ nextIndex' = [nextIndex EXCEPT ![n] = [m2 \in Nodes |-> Len(log[n]) + 1]]
                    /\ matchIndex' = [matchIndex EXCEPT ![n] = [m2 \in Nodes |-> 0]]
                    /\ \A m2 \in Nodes \ {n}: 
                        LET ae == [type |-> "AppendEntries", term |-> currentTerm[n], leaderId |-> n, prevLogIndex |-> Len(log[n]), prevLogTerm |-> IF Len(log[n]) > 0 THEN log[n][Len(log[n])].term ELSE 0, entries |-> <<>>, leaderCommit |-> commitIndex[n]]
                        IN messages' = messages \cup {ae}
                ELSE
                    /\ UNCHANGED <<state, leaderId, nextIndex, matchIndex>>
        ELSE
            /\ UNCHANGED votesGranted
            /\ IF m.term > currentTerm[n]
                THEN
                    /\ state' = [state EXCEPT ![n] = "Follower"]
                    /\ currentTerm' = [currentTerm EXCEPT ![n] = m.term]
                    /\ votedFor' = [votedFor EXCEPT ![n] = Null]
                    /\ votesGranted' = [votesGranted EXCEPT ![n] = 0]
                ELSE
                    /\ UNCHANGED <<state, currentTerm, votedFor>>
    /\ messages' = messages \ {m}
    /\ UNCHANGED <<log, commitIndex, lastApplied, sm, pendingRequests>>
ClientSubmitRequest(c, rid, op) ==
    /\ pendingRequests' = pendingRequests \cup {[client |-> c, reqId |-> rid, op |-> op]}
    /\ LET m == [type |-> "ClientRequest", client |-> c, reqId |-> rid, op |-> op]
       IN messages' = messages \cup {m}
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, sm, votesGranted>>
ReceiveClientRequest(n, m) ==
    /\ m \in messages
    /\ m.type = "ClientRequest"
    /\ state[n] = "Leader"
    /\ LET newLog == log[n] \o [term |-> currentTerm[n], op |-> m.op, client |-> m.client, reqId |-> m.reqId]
       IN log' = [log EXCEPT ![n] = newLog]
    /\ \A n2 \in Nodes \ {n}: 
        LET ae == [type |-> "AppendEntries", term |-> currentTerm[n], leaderId |-> n, prevLogIndex |-> Len(log[n]), prevLogTerm |-> IF Len(log[n]) > 0 THEN log[n][Len(log[n])].term ELSE 0, entries |-> <<[term |-> currentTerm[n], op |-> m.op, client |-> m.client, reqId |-> m.reqId]>>, leaderCommit |-> commitIndex[n]]
        IN messages' = messages \cup {ae}
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, sm, pendingRequests, votesGranted>>
ReceiveAppendEntries(n, m) ==
    /\ m \in messages
    /\ m.type = "AppendEntries"
    /\ IF m.term < currentTerm[n]
        THEN
            /\ LET resp == [type |-> "AppendEntriesResponse", term |-> currentTerm[n], success |-> FALSE, from |-> n, matchIndex |-> 0]
               IN messages' = (messages \ {m}) \cup {resp}
            /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, sm, pendingRequests, votesGranted>>
        ELSE
            /\ currentTerm' = [currentTerm EXCEPT ![n] = m.term]
            /\ state' = [state EXCEPT ![n] = "Follower"]
            /\ leaderId' = [leaderId EXCEPT ![n] = m.leaderId]
            /\ votedFor' = [votedFor EXCEPT ![n] = Null]
            /\ votesGranted' = [votesGranted EXCEPT ![n] = 0]
            /\ ( \/ ( \/ m.prevLogIndex > Len(log[n])
                      \/ (m.prevLogIndex > 0 /\ (m.prevLogIndex > Len(log[n]) \/ log[n][m.prevLogIndex].term # m.prevLogTerm))
                    /\ LET resp == [type |-> "AppendEntriesResponse", term |-> m.term, success |-> FALSE, from |-> n, matchIndex |-> 0]
                       IN messages' = (messages \ {m}) \cup {resp}
                    /\ UNCHANGED <<log, commitIndex, lastApplied>>
                \/ ( \/ m.prevLogIndex = 0
                      \/ (m.prevLogIndex <= Len(log[n]) /\ log[n][m.prevLogIndex].term = m.prevLogTerm)
                    /\ LET newLog == IF m.entries # <<>> THEN SubSeq(log[n], 1, m.prevLogIndex) \o m.entries ELSE log[n]
                       IN /\ log' = [log EXCEPT ![n] = newLog]
                          /\ commitIndex' = [commitIndex EXCEPT ![n] = IF m.leaderCommit > commitIndex[n] THEN Min({m.leaderCommit, Len(newLog)}) ELSE commitIndex[n]]
                          /\ LET resp == [type |-> "AppendEntriesResponse", term |-> m.term, success |-> TRUE, from |-> n, matchIndex |-> m.prevLogIndex + Len(m.entries)]
                             IN messages' = (messages \ {m}) \cup {resp}
                    /\ UNCHANGED lastApplied
                )
              )
            /\ UNCHANGED <<nextIndex, matchIndex, sm, pendingRequests>>
ReceiveAppendEntriesResponse(n, m) ==
    /\ m \in messages
    /\ m.type = "AppendEntriesResponse"
    /\ state[n] = "Leader"
    /\ IF m.term > currentTerm[n]
        THEN
            /\ state' = [state EXCEPT ![n] = "Follower"]
            /\ currentTerm' = [currentTerm EXCEPT ![n] = m.term]
            /\ votedFor' = [votedFor EXCEPT ![n] = Null]
            /\ votesGranted' = [votesGranted EXCEPT ![n] = 0]
        ELSE
            /\ IF m.success
                THEN
                    /\ nextIndex' = [nextIndex EXCEPT ![n][m.from] = m.matchIndex + 1]
                    /\ matchIndex' = [matchIndex EXCEPT ![n][m.from] = m.matchIndex]
                    /\ LET N == Min({k \in {Len(log[n])} : k > commitIndex[n] /\ \A i \in Nodes: matchIndex[n][i] >= k})
                       IN IF Cardinality({i \in Nodes : matchIndex[n][i] >= N}) > Cardinality(Nodes) \div 2
                          THEN commitIndex' = [commitIndex EXCEPT ![n] = N]
                          ELSE UNCHANGED commitIndex
                ELSE
                    /\ nextIndex' = [nextIndex EXCEPT ![n][m.from] = nextIndex[n][m.from] - 1]
                    /\ UNCHANGED matchIndex
            /\ UNCHANGED <<state, currentTerm, votedFor, votesGranted>>
    /\ messages' = messages \ {m}
    /\ UNCHANGED <<log, lastApplied, leaderId, sm, pendingRequests>>
ApplyLogEntry(n) ==
    /\ lastApplied[n] < commitIndex[n]
    /\ LET idx == lastApplied[n] + 1
           entry == log[n][idx]
           newSM == IF entry.op.type = "Put" THEN [sm[n] EXCEPT ![entry.op.key] = entry.op.value]
                    ELSE IF entry.op.type = "Delete" THEN [sm[n] EXCEPT ![entry.op.key] = Null]
                    ELSE sm[n]
       IN sm' = [sm EXCEPT ![n] = newSM]
    /\ lastApplied' = [lastApplied EXCEPT ![n] = lastApplied[n] + 1]
    /\ IF state[n] = "Leader" /\ entry.op.type = "Get"
        THEN
            /\ LET resp == [type |-> "ClientResponse", client |-> entry.client, reqId |-> entry.reqId, result |-> newSM[entry.op.key]]
               IN messages' = messages \cup {resp}
            /\ pendingRequests' = pendingRequests \ {[client |-> entry.client, reqId |-> entry.reqId, op |-> entry.op]}
        ELSE
            /\ UNCHANGED <<messages, pendingRequests>>
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, leaderId, votesGranted>>
Next == 
    \/ \E n \in Nodes: ElectionTimeout(n)
    \/ \E n \in Nodes: \E m \in messages: 
           \/ ReceiveRequestVote(n, m)
           \/ ReceiveRequestVoteResponse(n, m)
           \/ ReceiveAppendEntries(n, m)
           \/ ReceiveAppendEntriesResponse(n, m)
           \/ ReceiveClientRequest(n, m)
    \/ \E c \in Clients: \E rid \in ReqIds: \E op \in [type: {"Put","Get","Delete"}, key: Keys, value: Values]: 
        [client |-> c, reqId |-> rid, op |-> op] \notin pendingRequests /\ ClientSubmitRequest(c, rid, op)
    \/ \E n \in Nodes: ApplyLogEntry(n)
Spec == Init /\ [][Next]_vars
====