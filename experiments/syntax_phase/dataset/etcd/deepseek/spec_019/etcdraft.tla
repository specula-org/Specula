---- MODULE etcdraft ----
EXTENDS Naturals, Sequences, FiniteSets
CONSTANTS Nodes,  
          None   

VARIABLES state,        
          currentTerm,  
          votedFor,     
          log,          
          commitIndex,  
          lastApplied,  
          nextIndex,    
          matchIndex,   
          leaderId,     
          msgs,         
          smState,      
          pendingOps    

vars == <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, msgs, smState, pendingOps>>

Term == Nat
Key == CHOOSE K : TRUE
Value == CHOOSE V : TRUE
OpType == {{"Put", "Delete"}}
ClientOp == [type : OpType, key : Key, value : Value]
Entry == [term : Term, op : ClientOp]
MessageType == {{"AppendEntries", "AppendEntriesResponse", "RequestVote", "RequestVoteResponse", "TimeoutNow"}}
Message == [type : MessageType, from : Nodes, to : Nodes, term : Term, success : BOOLEAN, prevLogIndex : Nat, prevLogTerm : Term, entries : Seq(Entry), leaderCommit : Nat, matchIndex : Nat, voteGranted : BOOLEAN]

QuorumSize == Cardinality(Nodes) \div 2 + 1

Init == 
    /\ state = [n \in Nodes |-> "Follower"]
    /\ currentTerm = [n \in Nodes |-> 0]
    /\ votedFor = [n \in Nodes |-> None]
    /\ log = [n \in Nodes |-> <<>>]
    /\ commitIndex = [n \in Nodes |-> 0]
    /\ lastApplied = [n \in Nodes |-> 0]
    /\ nextIndex = [n \in Nodes |-> [m \in Nodes |-> 1]]
    /\ matchIndex = [n \in Nodes |-> [m \in Nodes |-> 0]]
    /\ leaderId = [n \in Nodes |-> None]
    /\ msgs = {{}}
    /\ smState = [n \in Nodes |-> [k \in {{}} |-> CHOOSE v : TRUE]]
    /\ pendingOps = {{}}

BecomeCandidate(n) ==
    /\ state[n] \in {{"Follower", "Candidate"}}
    /\ state' = [state EXCEPT ![n] = "Candidate"]
    /\ currentTerm' = [currentTerm EXCEPT ![n] = currentTerm[n] + 1]
    /\ votedFor' = [votedFor EXCEPT ![n] = n]
    /\ msgs' = msgs \cup { [m \in Nodes \ {n} :-> [type |-> "RequestVote", from |-> n, to |-> m, term |-> currentTerm[n] + 1, 
                  prevLogIndex |-> Len(log[n]), prevLogTerm |-> IF Len(log[n]) > 0 THEN log[n][Len(log[n])].term ELSE 0,
                  voteGranted |-> FALSE, success |-> FALSE, entries |-> <<>>, leaderCommit |-> 0, matchIndex |-> 0] }
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, smState, pendingOps>>

SendAppendEntries(n, f) ==
    /\ state[n] = "Leader"
    /\ prevIndex = nextIndex[n][f] - 1
    /\ prevTerm = IF prevIndex > 0 THEN log[n][prevIndex].term ELSE 0
    /\ entries = SubSeq(log[n], nextIndex[n][f], Len(log[n]))
    /\ msgs' = msgs \cup { [type |-> "AppendEntries", from |-> n, to |-> f, term |-> currentTerm[n], 
                  prevLogIndex |-> prevIndex, prevLogTerm |-> prevTerm, entries |-> entries, 
                  leaderCommit |-> commitIndex[n], success |-> FALSE, voteGranted |-> FALSE, matchIndex |-> 0] }
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, smState, pendingOps>>

ReceiveAppendEntries(n, m) ==
    LET msg == CHOOSE msg \in msgs : msg.from = m /\ msg.to = n /\ msg.type = "AppendEntries"
    IN
    IF msg.term < currentTerm[n] THEN
        /\ msgs' = msgs \cup { [type |-> "AppendEntriesResponse", from |-> n, to |-> m, term |-> currentTerm[n], success |-> FALSE, 
                      matchIndex |-> 0, prevLogIndex |-> 0, prevLogTerm |-> 0, entries |-> <<>>, leaderCommit |-> 0, voteGranted |-> FALSE] }
        /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, smState, pendingOps>>
    ELSE
        LET resetState == 
            IF msg.term > currentTerm[n] THEN
                /\ state' = [state EXCEPT ![n] = "Follower"]
                /\ currentTerm' = [currentTerm EXCEPT ![n] = msg.term]
                /\ votedFor' = [votedFor EXCEPT ![n] = None]
            ELSE 
                /\ state' = [state EXCEPT ![n] = "Follower"]
                /\ UNCHANGED <<currentTerm, votedFor>>
        IN
        LET logOk == 
            /\ msg.prevLogIndex = 0 
            \/ (msg.prevLogIndex <= Len(log[n]) /\ log[n][msg.prevLogIndex].term = msg.prevLogTerm)
        IN
        IF logOk THEN
            LET indices == 1..Min(Len(log[n]) - msg.prevLogIndex, Len(msg.entries))
            LET conflictIndex == 
                 IF \E i \in indices : log[n][msg.prevLogIndex + i].term # msg.entries[i].term
                 THEN CHOOSE i \in indices : log[n][msg.prevLogIndex + i].term # msg.entries[i].term
                 ELSE 0
            IN
            LET newLog == 
                IF conflictIndex = 0 THEN
                    IF msg.prevLogIndex + Len(msg.entries) > Len(log[n]) THEN
                        log[n] \o SubSeq(msg.entries, Len(log[n]) - msg.prevLogIndex + 1, Len(msg.entries))
                    ELSE
                        log[n]
                ELSE
                    SubSeq(log[n], 1, msg.prevLogIndex + conflictIndex - 1) \o 
                    SubSeq(msg.entries, conflictIndex, Len(msg.entries))
            IN
            LET newCommit == Min(msg.leaderCommit, Len(newLog))
            IN
            /\ resetState
            /\ log' = [log EXCEPT ![n] = newLog]
            /\ commitIndex' = [commitIndex EXCEPT ![n] = newCommit]
            /\ msgs' = msgs \cup { [type |-> "AppendEntriesResponse", from |-> n, to |-> m, term |-> currentTerm'[n], success |-> TRUE, 
                          matchIndex |-> Len(newLog), prevLogIndex |-> 0, prevLogTerm |-> 0, entries |-> <<>>, leaderCommit |-> 0, voteGranted |-> FALSE] }
            /\ leaderId' = [leaderId EXCEPT ![n] = m]
            /\ UNCHANGED <<nextIndex, matchIndex, smState, pendingOps>>
        ELSE
            /\ resetState
            /\ msgs' = msgs \cup { [type |-> "AppendEntriesResponse", from |-> n, to |-> m, term |-> currentTerm'[n], success |-> FALSE, 
                          matchIndex |-> 0, prevLogIndex |-> 0, prevLogTerm |-> 0, entries |-> <<>>, leaderCommit |-> 0, voteGranted |-> FALSE] }
            /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, leaderId, smState, pendingOps>>

ReceiveAppendEntriesResponse(n, m) ==
    LET msg == CHOOSE msg \in msgs : msg.from = m /\ msg.to = n /\ msg.type = "AppendEntriesResponse"
    IN
    IF msg.term > currentTerm[n] THEN
        /\ state' = [state EXCEPT ![n] = "Follower"]
        /\ currentTerm' = [currentTerm EXCEPT ![n] = msg.term]
        /\ votedFor' = [votedFor EXCEPT ![n] = None]
        /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, smState, pendingOps>>
    ELSE
        IF state[n] = "Leader" /\ msg.term = currentTerm[n] THEN
            IF msg.success THEN
                /\ nextIndex' = [nextIndex EXCEPT ![n][m] = msg.matchIndex + 1]
                /\ matchIndex' = [matchIndex EXCEPT ![n][m] = msg.matchIndex]
                /\ LET S == { j \in 1..Len(log[n]) : 
                                log[n][j].term = currentTerm[n] /\
                                Cardinality({k \in Nodes : matchIndex'[n][k] >= j}) >= QuorumSize }
                   IN
                   LET maxCommit == 
                         IF S = {} 
                         THEN commitIndex[n]
                         ELSE CHOOSE j \in S : \A k \in S : j >= k
                   IN
                   commitIndex' = [commitIndex EXCEPT ![n] = IF maxCommit > commitIndex[n] THEN maxCommit ELSE commitIndex[n]]
                /\ UNCHANGED <<state, currentTerm, votedFor, log, lastApplied, leaderId, smState, pendingOps>>
            ELSE
                /\ nextIndex' = [nextIndex EXCEPT ![n][m] = nextIndex[n][m] - 1]
                /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, matchIndex, leaderId, smState, pendingOps>>
        ELSE
            UNCHANGED vars
        ENDIF
    ENDIF

ReceiveRequestVote(n, m) ==
    LET msg == CHOOSE msg \in msgs : msg.from = m /\ msg.to = n /\ msg.type = "RequestVote"
    IN
    IF msg.term < currentTerm[n] THEN
        /\ msgs' = msgs \cup { [type |-> "RequestVoteResponse", from |-> n, to |-> m, term |-> currentTerm[n], voteGranted |-> FALSE,
                      success |-> FALSE, prevLogIndex |-> 0, prevLogTerm |-> 0, entries |-> <<>>, leaderCommit |-> 0, matchIndex |-> 0] }
        /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, smState, pendingOps>>
    ELSE
        LET resetState == 
            IF msg.term > currentTerm[n] THEN
                /\ state' = [state EXCEPT ![n] = "Follower"]
                /\ currentTerm' = [currentTerm EXCEPT ![n] = msg.term]
                /\ votedFor' = [votedFor EXCEPT ![n] = None]
            ELSE 
                /\ UNCHANGED <<state, currentTerm, votedFor>>
        IN
        LET lastLogIndex == Len(log[n])
        LET lastLogTerm == IF lastLogIndex > 0 THEN log[n][lastLogIndex].term ELSE 0
        LET logOk == (msg.prevLogTerm > lastLogTerm) \/ (msg.prevLogTerm = lastLogTerm /\ msg.prevLogIndex >= lastLogIndex)
        IN
        IF (votedFor[n] = None \/ votedFor[n] = m) /\ logOk THEN
            /\ resetState
            /\ votedFor' = [votedFor EXCEPT ![n] = m]
            /\ msgs' = msgs \cup { [type |-> "RequestVoteResponse", from |-> n, to |-> m, term |-> currentTerm'[n], voteGranted |-> TRUE,
                          success |-> FALSE, prevLogIndex |-> 0, prevLogTerm |-> 0, entries |-> <<>>, leaderCommit |-> 0, matchIndex |-> 0] }
            /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, smState, pendingOps>>
        ELSE
            /\ resetState
            /\ msgs' = msgs \cup { [type |-> "RequestVoteResponse", from |-> n, to |-> m, term |-> currentTerm'[n], voteGranted |-> FALSE,
                          success |-> FALSE, prevLogIndex |-> 0, prevLogTerm |-> 0, entries |-> <<>>, leaderCommit |-> 0, matchIndex |-> 0] }
            /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, smState, pendingOps>>
        ENDIF
    ENDIF

ReceiveRequestVoteResponse(n, m) ==
    LET msg == CHOOSE msg \in msgs : msg.from = m /\ msg.to = n /\ msg.type = "RequestVoteResponse"
    IN
    IF msg.term > currentTerm[n] THEN
        /\ state' = [state EXCEPT ![n] = "Follower"]
        /\ currentTerm' = [currentTerm EXCEPT ![n] = msg.term]
        /\ votedFor' = [votedFor EXCEPT ![n] = None]
        /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, smState, pendingOps>>
    ELSE
        IF state[n] = "Candidate" /\ msg.term = currentTerm[n] /\ msg.voteGranted THEN
            LET votes == {k \in Nodes : \E resp \in msgs : resp.type = "RequestVoteResponse" /\ resp.from = k /\ resp.to = n /\ resp.term = currentTerm[n] /\ resp.voteGranted}
            IN
            IF Cardinality(votes) >= QuorumSize THEN
                /\ state' = [state EXCEPT ![n] = "Leader"]
                /\ nextIndex' = [nextIndex EXCEPT ![n] = [m \in Nodes |-> Len(log[n]) + 1]]
                /\ matchIndex' = [matchIndex EXCEPT ![n] = [m \in Nodes |-> 0]]
                /\ leaderId' = [leaderId EXCEPT ![n] = n]
                /\ msgs' = msgs \cup { [f \in Nodes \ {n} :-> [type |-> "AppendEntries", from |-> n, to |-> f, term |-> currentTerm[n],
                              prevLogIndex |-> Len(log[n]), prevLogTerm |-> IF Len(log[n]) > 0 THEN log[n][Len(log[n])].term ELSE 0,
                              entries |-> <<>>, leaderCommit |-> commitIndex[n], success |-> FALSE, voteGranted |-> FALSE, matchIndex |-> 0] }
                /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied, smState, pendingOps>>
            ELSE
                UNCHANGED vars
            ENDIF
        ELSE
            UNCHANGED vars
        ENDIF
    ENDIF

LeaderPropose(n, op) ==
    /\ state[n] = "Leader"
    /\ op \in pendingOps
    /\ log' = [log EXCEPT ![n] = log[n] \o [ [term |-> currentTerm[n], op |-> op] ]]
    /\ nextIndex' = [nextIndex EXCEPT ![n][n] = Len(log[n]) + 1]
    /\ matchIndex' = [matchIndex EXCEPT ![n][n] = Len(log[n]) + 1]
    /\ pendingOps' = pendingOps \ {op}
    /\ msgs' = msgs \cup { [f \in Nodes \ {n} :-> [type |-> "AppendEntries", from |-> n, to |-> f, term |-> currentTerm[n],
                      prevLogIndex |-> Len(log[n]), prevLogTerm |-> IF Len(log[n]) > 0 THEN log[n][Len(log[n])].term ELSE 0,
                      entries |-> <<[term |-> currentTerm[n], op |-> op]>>, leaderCommit |-> commitIndex[n], 
                      success |-> FALSE, voteGranted |-> FALSE, matchIndex |-> 0] }
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, leaderId, smState>>

ApplyLog(n) ==
    /\ lastApplied[n] < commitIndex[n]
    /\ LET idx == lastApplied[n] + 1
       entry == log[n][idx]
       newState == 
            IF entry.op.type = "Put" THEN
                [smState[n] EXCEPT ![entry.op.key] = entry.op.value]
            ELSE
                [k \in DOMAIN smState[n] \ {entry.op.key} |-> smState[n][k]]
        IN
        /\ lastApplied' = [lastApplied EXCEPT ![n] = idx]
        /\ smState' = [smState EXCEPT ![n] = newState]
        /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, leaderId, msgs, pendingOps>>

Timeout(n) ==
    /\ state[n] # "Leader"
    /\ BecomeCandidate(n)

NewClientOp(op) ==
    /\ pendingOps' = pendingOps \cup {op}
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, msgs, smState>>

LoseMessage(msg) ==
    /\ msg \in msgs
    /\ msgs' = msgs \ {msg}
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, smState, pendingOps>>

Next ==
    \/ \E n \in Nodes : BecomeCandidate(n)
    \/ \E n, f \in Nodes : n # f /\ SendAppendEntries(n, f)
    \/ \E n, m \in Nodes : n # m /\ ReceiveAppendEntries(n, m)
    \/ \E n, m \in Nodes : n # m /\ ReceiveAppendEntriesResponse(n, m)
    \/ \E n, m \in Nodes : n # m /\ ReceiveRequestVote(n, m)
    \/ \E n, m \in Nodes : n # m /\ ReceiveRequestVoteResponse(n, m)
    \/ \E n \in Nodes, op \in ClientOp : LeaderPropose(n, op)
    \/ \E n \in Nodes : ApplyLog(n)
    \/ \E n \in Nodes : Timeout(n)
    \/ \E op \in ClientOp : NewClientOp(op)
    \/ \E msg \in msgs : LoseMessage(msg)

Spec == Init /\ [][Next]_vars

Termination ==
    <>(\A n \in Nodes : state[n] = "Leader" \/ state[n] = "Follower")

\* Invariants
TypeInvariant ==
    /\ state \in [Nodes -> {{"Follower", "Candidate", "Leader"}}]
    /\ currentTerm \in [Nodes -> Nat]
    /\ votedFor \in [Nodes -> Nodes \cup {{None}}]
    /\ log \in [Nodes -> Seq([term : Nat, op : [type : {{"Put","Delete"}}, key : Key, value : Value]])]
    /\ commitIndex \in [Nodes -> Nat]
    /\ lastApplied \in [Nodes -> Nat]
    /\ nextIndex \in [Nodes -> [Nodes -> Nat]]
    /\ matchIndex \in [Nodes -> [Nodes -> Nat]]
    /\ leaderId \in [Nodes -> Nodes \cup {{None}}]
    /\ msgs \subseteq [type : MessageType, from : Nodes, to : Nodes, term : Nat, success : BOOLEAN, 
                      prevLogIndex : Nat, prevLogTerm : Nat, entries : Seq([term : Nat, op : [type : {{"Put","Delete"}}, key : Key, value : Value]]), 
                      leaderCommit : Nat, matchIndex : Nat, voteGranted : BOOLEAN]
    /\ smState \in [Nodes -> [Key -> Value]]
    /\ pendingOps \subseteq [type : {{"Put","Delete"}}, key : Key, value : Value]

LeaderCompleteness ==
    \A n1, n2 \in Nodes, i \in 1..Len(log[n1]) : 
        (state[n1] = "Leader" /\ log[n1][i].term = currentTerm[n1] /\ commitIndex[n1] >= i) 
        => \E j \in 1..Len(log[n2]) : 
              j <= Len(log[n2]) /\ log[n2][j] = log[n1][i]

StateMachineSafety ==
    \A n1, n2 \in Nodes, i \in 1..Min(lastApplied[n1], lastApplied[n2]), k \in Key :
        (log[n1][i].op.key = k /\ log[n2][i].op.key = k) 
        => smState[n1][k] = smState[n2][k]

====