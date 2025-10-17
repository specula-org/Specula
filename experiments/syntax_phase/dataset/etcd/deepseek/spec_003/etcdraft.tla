---- MODULE etcdraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Nodes, None
ASSUME IsFiniteSet(Nodes)
ASSUME None \notin Nodes

VARIABLES 
    state,        \* Function: [Node -> {Follower, Candidate, PreCandidate, Leader}]
    currentTerm,  \* Function: [Node -> Nat]
    votedFor,     \* Function: [Node -> Node ∪ {None}]
    log,          \* Function: [Node -> Seq([term: Nat, index: Nat])]
    commitIndex,  \* Function: [Node -> Nat]
    nextIndex,    \* Function: [Node -> (Nodes -> Nat)]
    matchIndex,   \* Function: [Node -> (Nodes -> Nat)]
    messages,     \* Bag of messages in flight
    leader,       \* Function: [Node -> Node ∪ {None}]
    electionTimeout, \* Function: [Node -> Nat]
    votesReceived, \* Function: [Node -> SUBSET Nodes]
    prevoteResponses  \* Function: [Node -> SUBSET Nodes]

vars == <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, messages, leader, electionTimeout, votesReceived, prevoteResponses>>

Term == Nat
LogIndex == Nat

MessageType == {"MsgHup", "MsgVote", "MsgVoteResp", "MsgApp", "MsgAppResp", "MsgHeartbeat", "MsgHeartbeatResp", "MsgPreVote", "MsgPreVoteResp"}

Message == [type : MessageType, term : Term, from : Node ∪ {None}, to : Node ∪ {None}, logTerm : Term, index : LogIndex, reject : BOOLEAN, entries : Seq([term: Nat, index: Nat])]

StateType == {"Follower", "Candidate", "PreCandidate", "Leader"}

Init == 
    /\ state = [n \in Nodes |-> "Follower"]
    /\ currentTerm = [n \in Nodes |-> 0]
    /\ votedFor = [n \in Nodes |-> None]
    /\ log = [n \in Nodes |-> <<>>]
    /\ commitIndex = [n \in Nodes |-> 0]
    /\ nextIndex = [n \in Nodes |-> [m \in Nodes |-> 1]]
    /\ matchIndex = [n \in Nodes |-> [m \in Nodes |-> 0]]
    /\ messages = EmptyBag
    /\ leader = [n \in Nodes |-> None]
    /\ electionTimeout = [n \in Nodes |-> 0]
    /\ votesReceived = [n \in Nodes |-> {}]
    /\ prevoteResponses = [n \in Nodes |-> {}]

CanVote(n, m) == 
    \/ votedFor[n] = m.from
    \/ votedFor[n] = None /\ leader[n] = None
    \/ m.type = "MsgPreVote" /\ m.term > currentTerm[n]

IsUpToDate(n, m) == 
    LET lastLog == IF Len(log[n]) > 0 THEN log[n][Len(log[n])] ELSE [term |-> 0, index |-> 0] IN
    \/ m.logTerm > lastLog.term
    \/ m.logTerm = lastLog.term /\ m.index >= lastLog.index

HandleMsgHup(n) == 
    /\ state[n] \in {"Follower", "Candidate"}
    /\ electionTimeout[n] >= 3
    /\ \/ state[n] = "Follower" /\ leader[n] = None
       \/ state[n] = "Candidate"
    /\ state' = [state EXCEPT ![n] = "PreCandidate"]
    /\ votesReceived' = [votesReceived EXCEPT ![n] = {}]
    /\ prevoteResponses' = [prevoteResponses EXCEPT ![n] = {}]
    /\ electionTimeout' = [electionTimeout EXCEPT ![n] = 0]
    /\ \E m \in Nodes \ {n}:
        messages' = messages (+) 
            [type |-> "MsgPreVote", term |-> currentTerm[n] + 1, from |-> n, to |-> m, 
             logTerm |-> IF Len(log[n]) > 0 THEN log[n][Len(log[n])].term ELSE 0,
             index |-> IF Len(log[n]) > 0 THEN log[n][Len(log[n])].index ELSE 0,
             reject |-> FALSE, entries |-> <<>>]

HandlePreVote(n, m) == 
    /\ m.type = "MsgPreVote"
    /\ \/ m.term > currentTerm[n]
       \/ m.term = currentTerm[n] /\ CanVote(n, m) /\ IsUpToDate(n, m)
    /\ messages' = messages (+) 
        [type |-> "MsgPreVoteResp", term |-> m.term, from |-> n, to |-> m.from,
         logTerm |-> 0, index |-> 0, reject |-> ~(CanVote(n, m) /\ IsUpToDate(n, m)), entries |-> <<>>]

HandlePreVoteResp(n, m) == 
    /\ m.type = "MsgPreVoteResp"
    /\ state[n] = "PreCandidate"
    /\ m.term = currentTerm[n] + 1
    /\ prevoteResponses' = [prevoteResponses EXCEPT ![n] = @ \union {m.from}]
    /\ LET responses == prevoteResponses'[n] IN
        IF Cardinality(responses) >= QuorumSize()
        THEN /\ state' = [state EXCEPT ![n] = "Candidate"]
             /\ currentTerm' = [currentTerm EXCEPT ![n] = currentTerm[n] + 1]
             /\ votedFor' = [votedFor EXCEPT ![n] = n]
             /\ votesReceived' = [votesReceived EXCEPT ![n] = {n}]
             /\ electionTimeout' = [electionTimeout EXCEPT ![n] = 0]
             /\ \E other \in Nodes \ {n}:
                 messages' = messages (+) 
                    [type |-> "MsgVote", term |-> currentTerm[n] + 1, from |-> n, to |-> other,
                     logTerm |-> IF Len(log[n]) > 0 THEN log[n][Len(log[n])].term ELSE 0,
                     index |-> IF Len(log[n]) > 0 THEN log[n][Len(log[n])].index ELSE 0,
                     reject |-> FALSE, entries |-> <<>>]
        ELSE UNCHANGED <<state, currentTerm, votedFor, votesReceived, electionTimeout, messages>>

HandleVote(n, m) == 
    /\ m.type = "MsgVote"
    /\ \/ m.term > currentTerm[n]
       \/ m.term = currentTerm[n] /\ CanVote(n, m) /\ IsUpToDate(n, m)
    /\ currentTerm' = [currentTerm EXCEPT ![n] = MAX({currentTerm[n], m.term})]
    /\ \/ m.term > currentTerm[n] /\ votedFor' = [votedFor EXCEPT ![n] = None]
       \/ UNCHANGED votedFor
    /\ messages' = messages (+) 
        [type |-> "MsgVoteResp", term |-> currentTerm'[n], from |-> n, to |-> m.from,
         logTerm |-> 0, index |-> 0, reject |-> ~(CanVote(n, m) /\ IsUpToDate(n, m)), entries |-> <<>>]

HandleVoteResp(n, m) == 
    /\ m.type = "MsgVoteResp"
    /\ state[n] = "Candidate"
    /\ m.term = currentTerm[n]
    /\ ~m.reject
    /\ votesReceived' = [votesReceived EXCEPT ![n] = @ \union {m.from}]
    /\ IF Cardinality(votesReceived'[n]) >= QuorumSize()
       THEN /\ state' = [state EXCEPT ![n] = "Leader"]
            /\ leader' = [leader EXCEPT ![n] = n]
            /\ nextIndex' = [nextIndex EXCEPT ![n] = [m \in Nodes |-> Len(log[n]) + 1]]
            /\ matchIndex' = [matchIndex EXCEPT ![n] = [m \in Nodes |-> 0]]
            /\ electionTimeout' = [electionTimeout EXCEPT ![n] = 0]
            /\ \E other \in Nodes \ {n}:
                messages' = messages (+) 
                    [type |-> "MsgApp", term |-> currentTerm[n], from |-> n, to |-> other,
                     logTerm |-> IF Len(log[n]) > 0 THEN log[n][Len(log[n])].term ELSE 0,
                     index |-> IF Len(log[n]) > 0 THEN log[n][Len(log[n])].index ELSE 0,
                     reject |-> FALSE, entries |-> <<>>]
       ELSE UNCHANGED <<state, leader, nextIndex, matchIndex, electionTimeout, messages>>

HandleAppendEntries(n, m) == 
    /\ m.type = "MsgApp"
    /\ \/ m.term > currentTerm[n]
       \/ m.term = currentTerm[n] \/ state[n] = "Follower"
    /\ currentTerm' = [currentTerm EXCEPT ![n] = MAX({currentTerm[n], m.term})]
    /\ leader' = [leader EXCEPT ![n] = m.from]
    /\ electionTimeout' = [electionTimeout EXCEPT ![n] = 0]
    /\ \* Log consistency check and update logic would go here
    /\ messages' = messages (+) 
        [type |-> "MsgAppResp", term |-> currentTerm'[n], from |-> n, to |-> m.from,
         logTerm |-> 0, index |-> 0, reject |-> FALSE, entries |-> <<>>]

HandleHeartbeat(n, m) == 
    /\ m.type = "MsgHeartbeat"
    /\ electionTimeout' = [electionTimeout EXCEPT ![n] = 0]
    /\ messages' = messages (+) 
        [type |-> "MsgHeartbeatResp", term |-> currentTerm[n], from |-> n, to |-> m.from,
         logTerm |-> 0, index |-> 0, reject |-> FALSE, entries |-> <<>>]

Next == 
    \/ \E n \in Nodes: HandleMsgHup(n)
    \/ \E m \in BagToSet(messages): \E n \in Nodes: 
        \/ HandlePreVote(n, m)
        \/ HandlePreVoteResp(n, m)
        \/ HandleVote(n, m)
        \/ HandleVoteResp(n, m)
        \/ HandleAppendEntries(n, m)
        \/ HandleHeartbeat(n, m)
    \/ \E n \in Nodes: 
        /\ state[n] = "Leader"
        /\ electionTimeout' = [electionTimeout EXCEPT ![n] = @ + 1]
        /\ electionTimeout[n] >= 2
        /\ \E other \in Nodes \ {n}:
            messages' = messages (+) 
                [type |-> "MsgHeartbeat", term |-> currentTerm[n], from |-> n, to |-> other,
                 logTerm |-> 0, index |-> 0, reject |-> FALSE, entries |-> <<>>]
    \/ \E n \in Nodes:
        /\ state[n] \in {"Follower", "Candidate", "PreCandidate"}
        /\ electionTimeout' = [electionTimeout EXCEPT ![n] = @ + 1]

QuorumSize() == Cardinality(Nodes) \div 2 + 1

Spec == Init /\ [][Next]_vars

====