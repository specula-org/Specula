---- MODULE raftkvs ----
EXTENDS TLC, Sequences, Naturals, FiniteSets
CONSTANTS NumServers, NumClients, Key, Value, LeaderTimeout
Server == 1..NumServers
Client == NumServers+1..NumServers+NumClients
Node == Server \cup Client
Nil == 0
VARIABLES state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votesGranted, sm, smDomain, msgs, leader
vars == <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votesGranted, sm, smDomain, msgs, leader>>
Max(a, b) == IF a > b THEN a ELSE b
LastTerm(logSeq) == IF Len(logSeq) = 0 THEN 0 ELSE logSeq[Len(logSeq)].term
IsQuorum(s) == Cardinality(s) > NumServers \div 2
Init == 
 state = [s \in Server |-> "Follower"] /\
 currentTerm = [s \in Server |-> 0] /\
 votedFor = [s \in Server |-> Nil] /\
 log = [s \in Server |-> <<>>] /\
 commitIndex = [s \in Server |-> 0] /\
 nextIndex = [s \in Server |-> [t \in Server |-> 1]] /\
 matchIndex = [s \in Server |-> [t \in Server |-> 0]] /\
 votesGranted = [s \in Server |-> {}] /\
 sm = [s \in Server |-> [k \in Key |-> Nil]] /\
 smDomain = [s \in Server |-> {}] /\
 msgs = {} /\
 leader = [s \in Server |-> Nil]
Timeout(s) == 
 state[s] = "Follower" /\
 state' = [state EXCEPT ![s] = "Candidate"] /\
 currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1] /\
 votedFor' = [votedFor EXCEPT ![s] = s] /\
 votesGranted' = [votesGranted EXCEPT ![s] = {s}] /\
 leader' = [leader EXCEPT ![s] = Nil] /\
 msgs' = msgs \cup { [ type |-> "RVRequest", term |-> currentTerm[s] + 1, lastLogTerm |-> LastTerm(log[s]), lastLogIndex |-> Len(log[s]), source |-> s, dest |-> t ] : t \in Server \ {s} } /\
 UNCHANGED <<log, commitIndex, nextIndex, matchIndex, sm, smDomain>>
Receive(m) == 
 m \in msgs /\
 \/ m.type = "RVRequest" /\ 
   IF m.term > currentTerm[m.dest] THEN
     currentTerm' = [currentTerm EXCEPT ![m.dest] = m.term] /\
     state' = [state EXCEPT ![m.dest] = "Follower"] /\
     votedFor' = [votedFor EXCEPT ![m.dest] = Nil] /\
     leader' = [leader EXCEPT ![m.dest] = Nil] /\
     LET i == m.dest IN
     LET j == m.source IN
     LET logOK == (m.lastLogTerm > LastTerm(log[i])) \/ (m.lastLogTerm = LastTerm(log[i]) /\ m.lastLogIndex >= Len(log[i])) IN
     LET grant == (m.term = currentTerm'[i]) /\ logOK /\ (votedFor'[i] \in {Nil, j}) IN
     IF grant THEN
       votedFor' = [votedFor' EXCEPT ![i] = j] /\
       msgs' = (msgs \ {m}) \cup { [ type |-> "RVResponse", term |-> currentTerm'[i], voteGranted |-> TRUE, source |-> i, dest |-> j ] }
     ELSE
       msgs' = (msgs \ {m}) \cup { [ type |-> "RVResponse", term |-> currentTerm'[i], voteGranted |-> FALSE, source |-> i, dest |-> j ] }
     /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, votesGranted, sm, smDomain>>
   ELSE
     IF m.term < currentTerm[m.dest] THEN
       msgs' = (msgs \ {m}) \cup { [ type |-> "RVResponse", term |-> currentTerm[m.dest], voteGranted |-> FALSE, source |-> m.dest, dest |-> m.source ] } /\
       UNCHANGED <<state, currentTerm, votedFor, leader, log, commitIndex, nextIndex, matchIndex, votesGranted, sm, smDomain>>
     ELSE
       LET i == m.dest IN
       LET j == m.source IN
       LET logOK == (m.lastLogTerm > LastTerm(log[i])) \/ (m.lastLogTerm = LastTerm(log[i]) /\ m.lastLogIndex >= Len(log[i])) IN
       LET grant == logOK /\ (votedFor[i] \in {Nil, j}) IN
       IF grant THEN
         votedFor' = [votedFor EXCEPT ![i] = j] /\
         msgs' = (msgs \ {m}) \cup { [ type |-> "RVResponse", term |-> currentTerm[i], voteGranted |-> TRUE, source |-> i, dest |-> j ] }
       ELSE
         msgs' = (msgs \ {m}) \cup { [ type |-> "RVResponse", term |-> currentTerm[i], voteGranted |-> FALSE, source |-> i, dest |-> j ] }
       /\ UNCHANGED <<state, currentTerm, leader, log, commitIndex, nextIndex, matchIndex, votesGranted, sm, smDomain>>
 \/ m.type = "RVResponse" /\ 
   IF m.term > currentTerm[m.dest] THEN
     currentTerm' = [currentTerm EXCEPT ![m.dest] = m.term] /\
     state' = [state EXCEPT ![m.dest] = "Follower"] /\
     votedFor' = [votedFor EXCEPT ![m.dest] = Nil] /\
     leader' = [leader EXCEPT ![m.dest] = Nil] /\
     msgs' = msgs \ {m} /\
     UNCHANGED <<log, commitIndex, nextIndex, matchIndex, votesGranted, sm, smDomain>>
   ELSE
     IF m.term < currentTerm[m.dest] THEN
       msgs' = msgs \ {m} /\
       UNCHANGED <<state, currentTerm, votedFor, leader, log, commitIndex, nextIndex, matchIndex, votesGranted, sm, smDomain>>
     ELSE
       IF state[m.dest] = "Candidate" /\ m.voteGranted THEN
         votesGranted' = [votesGranted EXCEPT ![m.dest] = votesGranted[m.dest] \cup {m.source}] /\
         IF IsQuorum(votesGranted'[m.dest]) THEN
           state' = [state EXCEPT ![m.dest] = "Leader"] /\
           nextIndex' = [nextIndex EXCEPT ![m.dest] = [t \in Server |-> Len(log[m.dest]) + 1]] /\
           matchIndex' = [matchIndex EXCEPT ![m.dest] = [t \in Server |-> 0]] /\
           leader' = [leader EXCEPT ![m.dest] = m.dest] /\
           msgs' = (msgs \ {m}) \cup { [ type |-> "AERequest", term |-> currentTerm[m.dest], prevLogIndex |-> Len(log[m.dest]), prevLogTerm |-> LastTerm(log[m.dest]), entries |-> <<>>, commitIndex |-> commitIndex[m.dest], source |-> m.dest, dest |-> t ] : t \in Server \ {m.dest} }
         ELSE
           msgs' = msgs \ {m} /\
           UNCHANGED <<state, nextIndex, matchIndex, leader>>
         /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, sm, smDomain>>
       ELSE
         msgs' = msgs \ {m} /\
         UNCHANGED <<state, currentTerm, votedFor, leader, log, commitIndex, nextIndex, matchIndex, votesGranted, sm, smDomain>>
 \/ m.type = "AERequest" /\ 
   IF m.term > currentTerm[m.dest] THEN
     currentTerm' = [currentTerm EXCEPT ![m.dest] = m.term] /\
     state' = [state EXCEPT ![m.dest] = "Follower"] /\
     votedFor' = [votedFor EXCEPT ![m.dest] = Nil] /\
     leader' = [leader EXCEPT ![m.dest] = Nil] /\
     msgs' = (msgs \ {m}) \cup { [ type |-> "AEResponse", term |-> currentTerm'[m.dest], success |-> FALSE, matchIndex |-> 0, source |-> m.dest, dest |-> m.source ] } /\
     UNCHANGED <<log, commitIndex, nextIndex, matchIndex, votesGranted, sm, smDomain>>
   ELSE
     IF m.term < currentTerm[m.dest] THEN
       msgs' = (msgs \ {m}) \cup { [ type |-> "AEResponse", term |-> currentTerm[m.dest], success |-> FALSE, matchIndex |-> 0, source |-> m.dest, dest |-> m.source ] } /\
       UNCHANGED <<state, currentTerm, votedFor, leader, log, commitIndex, nextIndex, matchIndex, votesGranted, sm, smDomain>>
     ELSE
       LET i == m.dest IN
       LET j == m.source IN
       LET logOK == (m.prevLogIndex = 0) \/ (m.prevLogIndex > 0 /\ m.prevLogIndex <= Len(log[i]) /\ m.prevLogTerm = log[i][m.prevLogIndex].term) IN
       IF logOK THEN
         leader' = [leader EXCEPT ![i] = j] /\
         LET newLog == IF m.entries # <<>> THEN SubSeq(log[i], 1, m.prevLogIndex) \o m.entries ELSE log[i] IN
         log' = [log EXCEPT ![i] = newLog] /\
         commitIndex' = [commitIndex EXCEPT ![i] = Max(commitIndex[i], m.commitIndex)] /\
         msgs' = (msgs \ {m}) \cup { [ type |-> "AEResponse", term |-> currentTerm[i], success |-> TRUE, matchIndex |-> m.prevLogIndex + Len(m.entries), source |-> i, dest |-> j ] } /\
         UNCHANGED <<state, currentTerm, votedFor, nextIndex, matchIndex, votesGranted, sm, smDomain>>
       ELSE
         msgs' = (msgs \ {m}) \cup { [ type |-> "AEResponse", term |-> currentTerm[i], success |-> FALSE, matchIndex |-> 0, source |-> i, dest |-> j ] } /\
         UNCHANGED <<state, currentTerm, votedFor, leader, log, commitIndex, nextIndex, matchIndex, votesGranted, sm, smDomain>>
 \/ m.type = "AEResponse" /\ 
   IF m.term > currentTerm[m.dest] THEN
     currentTerm' = [currentTerm EXCEPT ![m.dest] = m.term] /\
     state' = [state EXCEPT ![m.dest] = "Follower"] /\
     votedFor' = [votedFor EXCEPT ![m.dest] = Nil] /\
     leader' = [leader EXCEPT ![m.dest] = Nil] /\
     msgs' = msgs \ {m} /\
     UNCHANGED <<log, commitIndex, nextIndex, matchIndex, votesGranted, sm, smDomain>>
   ELSE
     IF m.term < currentTerm[m.dest] THEN
       msgs' = msgs \ {m} /\
       UNCHANGED <<state, currentTerm, votedFor, leader, log, commitIndex, nextIndex, matchIndex, votesGranted, sm, smDomain>>
     ELSE
       IF state[m.dest] = "Leader" THEN
         nextIndex' = [nextIndex EXCEPT ![m.dest][m.source] = IF m.success THEN m.matchIndex + 1 ELSE Max(nextIndex[m.dest][m.source] - 1, 1)] /\
         matchIndex' = [matchIndex EXCEPT ![m.dest][m.source] = IF m.success THEN m.matchIndex ELSE matchIndex[m.dest][m.source]] /\
         msgs' = msgs \ {m} /\
         UNCHANGED <<state, currentTerm, votedFor, leader, log, commitIndex, votesGranted, sm, smDomain>>
       ELSE
         msgs' = msgs \ {m} /\
         UNCHANGED <<state, currentTerm, votedFor, leader, log, commitIndex, nextIndex, matchIndex, votesGranted, sm, smDomain>>
 \/ (m.type = "CPRequest" \/ m.type = "CGRequest") /\ 
   IF state[m.dest] = "Leader" THEN
     LET newEntry == [ term |-> currentTerm[m.dest], cmdType |-> IF m.type = "CPRequest" THEN "Put" ELSE "Get", key |-> m.key, value |-> IF m.type = "CPRequest" THEN m.value ELSE Nil, client |-> m.source ] IN
     log' = [log EXCEPT ![m.dest] = Append(log[m.dest], newEntry)] /\
     msgs' = msgs \ {m} /\
     UNCHANGED <<state, currentTerm, votedFor, commitIndex, nextIndex, matchIndex, votesGranted, sm, smDomain, leader>>
   ELSE
     msgs' = (msgs \ {m}) \cup { [ type |-> IF m.type = "CPRequest" THEN "CPResponse" ELSE "CGResponse", success |-> FALSE, response |-> [ idx |-> m.idx, key |-> m.key, value |-> Nil, ok |-> FALSE ], leaderHint |-> leader[m.dest], source |-> m.dest, dest |-> m.source ] } /\
     UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votesGranted, sm, smDomain, leader>>
 \/ (m.type = "CPResponse" \/ m.type = "CGResponse") /\ 
   msgs' = msgs \ {m} /\
   UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votesGranted, sm, smDomain, leader>>
LeaderSendAppendEntries(s) == 
 state[s] = "Leader" /\
 LET entriesForT(server) == SubSeq(log[s], nextIndex[s][server], Len(log[s])) IN
 msgs' = msgs \cup { [ type |-> "AERequest", term |-> currentTerm[s], prevLogIndex |-> nextIndex[s][t] - 1, prevLogTerm |-> IF nextIndex[s][t] > 1 THEN log[s][nextIndex[s][t] - 1].term ELSE 0, entries |-> entriesForT(t), commitIndex |-> commitIndex[s], source |-> s, dest |-> t ] : t \in Server \ {s} } /\
 UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votesGranted, sm, smDomain, leader>>
AdvanceCommitIndex(s) == 
 state[s] = "Leader" /\
 LET N == CHOOSE n \in 1..Len(log[s]) : \A t \in Server : matchIndex[s][t] >= n /\ Cardinality({t \in Server : matchIndex[s][t] >= n}) > NumServers \div 2 /\ log[s][n].term = currentTerm[s] IN
 commitIndex' = [commitIndex EXCEPT ![s] = N] /\
 UNCHANGED <<state, currentTerm, votedFor, log, nextIndex, matchIndex, votesGranted, sm, smDomain, msgs, leader>>
ClientSendRequest(c) == 
 LET dest == CHOOSE d \in Server : TRUE IN
 LET idx == CHOOSE i \in Nat : TRUE IN
 LET key == CHOOSE k \in Key : TRUE IN
 LET value == CHOOSE v \in Value : TRUE IN
 LET type == CHOOSE t \in {"Put", "Get"} : TRUE IN
 msgs' = msgs \cup { [ type |-> IF type = "Put" THEN "CPRequest" ELSE "CGRequest", idx |-> idx, key |-> key, value |-> value, source |-> c, dest |-> dest ] } /\
 UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votesGranted, sm, smDomain, leader>>
MessageLoss(m) == 
 msgs' = msgs \ {m} /\
 UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votesGranted, sm, smDomain, leader>>
Next == 
 \/ \E s \in Server : Timeout(s)
 \/ \E m \in msgs : Receive(m)
 \/ \E s \in Server : LeaderSendAppendEntries(s)
 \/ \E s \in Server : AdvanceCommitIndex(s)
 \/ \E c \in Client : ClientSendRequest(c)
 \/ \E m \in msgs : MessageLoss(m)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
====