---- MODULE etcdraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Node, None, ElectionTimeoutRange

VARIABLES state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votes, messages

VARIABLE leader

vars == <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votes, messages, leader>>

StateType == {"StateFollower", "StateCandidate", "StatePreCandidate", "StateLeader"}

MessageType == {"MsgHup", "MsgVote", "MsgVoteResp", "MsgPreVote", "MsgPreVoteResp", "MsgApp", "MsgAppResp", "MsgHeartbeat", "MsgHeartbeatResp", "MsgProp"}

(* Message structure *)
Message == [type : MessageType, from : Node \union {None}, to : Node \union {None}, term : Nat, logTerm : Nat, index : Nat, entries : Seq(LogEntry), commit : Nat, reject : BOOLEAN]

LogEntry == [term : Nat, index : Nat, data : Nat]

Init ==
    /\ state = [n \in Node |-> "StateFollower"]
    /\ currentTerm = [n \in Node |-> 0]
    /\ votedFor = [n \in Node |-> None]
    /\ log = [n \in Node |-> <<>>]
    /\ commitIndex = [n \in Node |-> 0]
    /\ nextIndex = [n \in Node |-> [m \in Node |-> 1]]
    /\ matchIndex = [n \in Node |-> [m \in Node |-> 0]]
    /\ votes = [n \in Node |-> {}]
    /\ messages = {}
    /\ leader = None

TypeOK ==
    /\ state \in [Node -> StateType]
    /\ currentTerm \in [Node -> Nat]
    /\ votedFor \in [Node -> Node \union {None}]
    /\ log \in [Node -> Seq(LogEntry)]
    /\ commitIndex \in [Node -> Nat]
    /\ nextIndex \in [Node -> [Node -> Nat]]
    /\ matchIndex \in [Node -> [Node -> Nat]]
    /\ votes \in [Node -> SUBSET Node]
    /\ messages \subseteq Message
    /\ leader \in Node \union {None}

Nodes == Node \union {None}

ElectionTimeout(n) ==
    /\ state[n] \in {"StateFollower", "StateCandidate"}
    /\ \E t \in ElectionTimeoutRange : TRUE
    /\ \/ state' = [state EXCEPT ![n] = "StatePreCandidate"]
       \/ state' = [state EXCEPT ![n] = "StateCandidate"]
    /\ currentTerm' = IF state'[n] = "StateCandidate" THEN [currentTerm EXCEPT ![n] = currentTerm[n] + 1] ELSE currentTerm
    /\ votedFor' = [votedFor EXCEPT ![n] = IF state'[n] = "StateCandidate" THEN n ELSE None]
    /\ votes' = [votes EXCEPT ![n] = IF state'[n] = "StateCandidate" THEN {n} ELSE {}]
    /\ messages' = messages \cup {[type |-> IF state'[n] = "StatePreCandidate" THEN "MsgPreVote" ELSE "MsgVote", 
                                          from |-> n, to |-> m, term |-> currentTerm[n] + IF state'[n] = "StatePreCandidate" THEN 0 ELSE 1, 
                                          logTerm |-> LastTerm(log[n]), index |-> Len(log[n]), 
                                          entries |-> <<>>, commit |-> 0, reject |-> FALSE] : m \in Node \ {n}}
    /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, leader>>

HandleMsgVote(n, m) ==
    /\ m \in messages
    /\ m.type = "MsgVote"
    /\ m.to = n
    /\ LET lastIndex == Len(log[n])
           lastTerm == IF lastIndex > 0 THEN log[n][lastIndex].term ELSE 0
        IN
        /\ IF /\ m.term > currentTerm[n]
              \/ (m.term = currentTerm[n] /\ votedFor[n] \in {None, m.from})
              \/ (m.term = currentTerm[n] /\ votedFor[n] = None)
              /\ (m.logTerm > lastTerm \/ (m.logTerm = lastTerm /\ m.index >= lastIndex))
           THEN
               /\ votedFor' = [votedFor EXCEPT ![n] = m.from]
               /\ currentTerm' = [currentTerm EXCEPT ![n] = m.term]
               /\ state' = [state EXCEPT ![n] = "StateFollower"]
               /\ messages' = messages \cup {[type |-> "MsgVoteResp", from |-> n, to |-> m.from, 
                                              term |-> currentTerm'[n], logTerm |-> 0, index |-> 0, 
                                              entries |-> <<>>, commit |-> 0, reject |-> FALSE]}
           ELSE
               /\ messages' = messages \cup {[type |-> "MsgVoteResp", from |-> n, to |-> m.from, 
                                              term |-> currentTerm[n], logTerm |-> 0, index |-> 0, 
                                              entries |-> <<>>, commit |-> 0, reject |-> TRUE]}
        /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votes, leader>>

HandleMsgPreVote(n, m) ==
    /\ m \in messages
    /\ m.type = "MsgPreVote"
    /\ m.to = n
    /\ LET lastIndex == Len(log[n])
           lastTerm == IF lastIndex > 0 THEN log[n][lastIndex].term ELSE 0
        IN
        IF /\ m.term > currentTerm[n]
           /\ (m.logTerm > lastTerm \/ (m.logTerm = lastTerm /\ m.index >= lastIndex))
        THEN
            messages' = messages \cup {[type |-> "MsgPreVoteResp", from |-> n, to |-> m.from, 
                                         term |-> m.term, logTerm |-> 0, index |-> 0, 
                                         entries |-> <<>>, commit |-> 0, reject |-> FALSE]}
        ELSE
            messages' = messages \cup {[type |-> "MsgPreVoteResp", from |-> n, to |-> m.from, 
                                         term |-> currentTerm[n], logTerm |-> 0, index |-> 0, 
                                         entries |-> <<>>, commit |-> 0, reject |-> TRUE]}
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votes, leader>>

HandleVoteResp(n, m) ==
    /\ m \in messages
    /\ m.type \in {"MsgVoteResp", "MsgPreVoteResp"}
    /\ m.to = n
    /\ state[n] \in {"StateCandidate", "StatePreCandidate"}
    /\ IF ~m.reject THEN
           votes' = [votes EXCEPT ![n] = votes[n] \cup {m.from}]
       ELSE
           votes' = votes
    /\ LET quorum == Cardinality(Node) \div 2 + 1
        IN
        IF Cardinality(votes'[n]) >= quorum THEN
            IF state[n] = "StatePreCandidate" THEN
                /\ state' = [state EXCEPT ![n] = "StateCandidate"]
                /\ currentTerm' = [currentTerm EXCEPT ![n] = currentTerm[n] + 1]
                /\ votedFor' = [votedFor EXCEPT ![n] = n]
                /\ votes' = [votes EXCEPT ![n] = {n}]
                /\ messages' = messages \cup {[type |-> "MsgVote", from |-> n, to |-> m, 
                                               term |-> currentTerm'[n], logTerm |-> LastTerm(log[n]), 
                                               index |-> Len(log[n]), entries |-> <<>>, 
                                               commit |-> 0, reject |-> FALSE] : m \in Node \ {n}}
            ELSE
                /\ state' = [state EXCEPT ![n] = "StateLeader"]
                /\ leader' = n
                /\ nextIndex' = [nextIndex EXCEPT ![n] = [m \in Node |-> Len(log[n]) + 1]]
                /\ matchIndex' = [matchIndex EXCEPT ![n] = [m \in Node |-> 0]]
                /\ messages' = messages \cup {[type |-> "MsgApp", from |-> n, to |-> m, 
                                               term |-> currentTerm[n], logTerm |-> LastTerm(log[n]), 
                                               index |-> Len(log[n]), entries |-> <<>>, 
                                               commit |-> commitIndex[n], reject |-> FALSE] : m \in Node \ {n}}
        ELSE
            UNCHANGED <<state, currentTerm, votedFor, leader, nextIndex, matchIndex, messages>>
    /\ UNCHANGED <<log, commitIndex>>

HandleMsgApp(n, m) ==
    /\ m \in messages
    /\ m.type = "MsgApp"
    /\ m.to = n
    /\ IF m.term < currentTerm[n] THEN
           messages' = messages \cup {[type |-> "MsgAppResp", from |-> n, to |-> m.from, 
                                          term |-> currentTerm[n], logTerm |-> 0, index |-> 0, 
                                          entries |-> <<>>, commit |-> 0, reject |-> TRUE]}
       ELSE
           /\ state' = [state EXCEPT ![n] = "StateFollower"]
           /\ currentTerm' = [currentTerm EXCEPT ![n] = m.term]
           /\ leader' = m.from
           /\ LET prevLogIndex == m.index
                  prevLogTerm == m.logTerm
                  newEntries == m.entries
              IN
              IF \/ prevLogIndex > Len(log[n])
                 \/ (prevLogIndex > 0 /\ prevLogIndex <= Len(log[n]) /\ log[n][prevLogIndex].term # prevLogTerm)
              THEN
                  messages' = messages \cup {[type |-> "MsgAppResp", from |-> n, to |-> m.from, 
                                             term |-> currentTerm'[n], logTerm |-> 0, index |-> prevLogIndex, 
                                             entries |-> <<>>, commit |-> 0, reject |-> TRUE]}
              ELSE
                  /\ log' = [log EXCEPT ![n] = SubSeq(log[n], 1, prevLogIndex) \o newEntries]
                  /\ commitIndex' = [commitIndex EXCEPT ![n] = MAX(commitIndex[n], m.commit)]
                  /\ messages' = messages \cup {[type |-> "MsgAppResp", from |-> n, to |-> m.from, 
                                                 term |-> currentTerm'[n], logTerm |-> 0, 
                                                 index |-> Len(log'[n]), entries |-> <<>>, 
                                                 commit |-> 0, reject |-> FALSE]}
    /\ UNCHANGED <<votedFor, nextIndex, matchIndex, votes>>

HandleMsgAppResp(n, m) ==
    /\ m \in messages
    /\ m.type = "MsgAppResp"
    /\ m.to = n
    /\ state[n] = "StateLeader"
    /\ IF m.reject THEN
           nextIndex' = [nextIndex EXCEPT ![n][m.from] = m.index]
           /\ messages' = messages \cup {[type |-> "MsgApp", from |-> n, to |-> m.from, 
                                          term |-> currentTerm[n], logTerm |-> IF m.index > 0 THEN log[n][m.index].term ELSE 0, 
                                          index |-> m.index, entries |-> SubSeq(log[n], m.index+1, Len(log[n])), 
                                          commit |-> commitIndex[n], reject |-> FALSE]}
       ELSE
           /\ matchIndex' = [matchIndex EXCEPT ![n][m.from] = m.index]
           /\ nextIndex' = [nextIndex EXCEPT ![n][m.from] = m.index + 1]
           /\ LET N == CHOOSE i \in {k \in 1..Len(log[n]) : log[n][k].term = currentTerm[n]} : 
                         Cardinality({m \in Node : matchIndex[n][m] >= i}) >= Cardinality(Node) \div 2 + 1
              IN
              IF N > commitIndex[n] THEN
                 commitIndex' = [commitIndex EXCEPT ![n] = N]
              ELSE
                 UNCHANGED commitIndex
           /\ UNCHANGED messages
    /\ UNCHANGED <<state, currentTerm, votedFor, log, votes, leader>>

HandleMsgHeartbeat(n, m) ==
    /\ m \in messages
    /\ m.type = "MsgHeartbeat"
    /\ m.to = n
    /\ IF m.term < currentTerm[n] THEN
           messages' = messages \cup {[type |-> "MsgHeartbeatResp", from |-> n, to |-> m.from, 
                                          term |-> currentTerm[n], logTerm |-> 0, index |-> 0, 
                                          entries |-> <<>>, commit |-> 0, reject |-> TRUE]}
       ELSE
           /\ state' = [state EXCEPT ![n] = "StateFollower"]
           /\ currentTerm' = [currentTerm EXCEPT ![n] = m.term]
           /\ leader' = m.from
           /\ commitIndex' = [commitIndex EXCEPT ![n] = MAX(commitIndex[n], m.commit)]
           /\ messages' = messages \cup {[type |-> "MsgHeartbeatResp", from |-> n, to |-> m.from, 
                                          term |-> currentTerm'[n], logTerm |-> 0, index |-> 0, 
                                          entries |-> <<>>, commit |-> 0, reject |-> FALSE]}
    /\ UNCHANGED <<votedFor, log, nextIndex, matchIndex, votes>>

HandleMsgProp(n, m) ==
    /\ m \in messages
    /\ m.type = "MsgProp"
    /\ m.to = n
    /\ state[n] = "StateLeader"
    /\ LET newEntry == [term |-> currentTerm[n], index |-> Len(log[n]) + 1, data |-> CHOOSE d \in Nat : TRUE]
        IN
        /\ log' = [log EXCEPT ![n] = log[n] \o <<newEntry>>]
        /\ nextIndex' = [nextIndex EXCEPT ![n][n] = Len(log'[n]) + 1]
        /\ matchIndex' = [matchIndex EXCEPT ![n][n] = Len(log'[n])]
        /\ messages' = messages \cup {[type |-> "MsgApp", from |-> n, to |-> m, 
                                       term |-> currentTerm[n], logTerm |-> LastTerm(log[n]), 
                                       index |-> Len(log[n]), entries |-> <<newEntry>>, 
                                       commit |-> commitIndex[n], reject |-> FALSE] : m \in Node \ {n}}
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, votes, leader>>

Next ==
    \/ \E n \in Node : ElectionTimeout(n)
    \/ \E n \in Node : \E m \in messages : HandleMsgVote(n, m)
    \/ \E n \in Node : \E m \in messages : HandleMsgPreVote(n, m)
    \/ \E n \in Node : \E m \in messages : HandleVoteResp(n, m)
    \/ \E n \in Node : \E m \in messages : HandleMsgApp(n, m)
    \/ \E n \in Node : \E m \in messages : HandleMsgAppResp(n, m)
    \/ \E n \in Node : \E m \in messages : HandleMsgHeartbeat(n, m)
    \/ \E n \in Node : \E m \in messages : HandleMsgProp(n, m)

Spec == Init /\ [][Next]_vars

Termination ==
    \E n \in Node : state[n] = "StateLeader"

====