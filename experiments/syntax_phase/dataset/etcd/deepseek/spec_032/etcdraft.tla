---- MODULE etcdraft ----
EXTENDS Naturals, Sequences, FiniteSets, TLC
CONSTANTS Node, Key, Value, Client, None, MaxElectionTimeout, HeartbeatInterval

VARIABLES
  state,        
  currentTerm,  
  votedFor,     
  log,          
  commitIndex,  
  lastApplied,  
  nextIndex,    
  matchIndex,   
  leaderId,     
  electionTimer,
  kvStore,      
  pendingReads, 
  messages,     
  uncommittedSize 

vars == <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, electionTimer, kvStore, pendingReads, messages, uncommittedSize>>

MsgType == {"AppendEntries", "AppendEntriesResponse", "RequestVote", "RequestVoteResponse", "ClientRequest", "ClientResponse", "TimeoutNow", "Heartbeat"}

StateType == {"Follower", "Candidate", "Leader"}

LogEntry == [term: Nat, cmd: [type: {"put","del","get"}, key: Key, value: Value \cup {None}, client: Client, opId: Nat]]

IsLeader(node) == state[node] = "Leader"

TermAt(node, index) == IF index > 0 /\ index <= Len(log[node]) THEN log[node][index].term ELSE 0
LastLogTerm(node) == IF Len(log[node]) > 0 THEN log[node][Len(log[node])].term ELSE 0
LastLogIndex(node) == Len(log[node])
Majority == Cardinality(Node) \div 2 + 1
Min(a, b) == IF a <= b THEN a ELSE b

Init ==
  /\ state = [n \in Node |-> "Follower"]
  /\ currentTerm = [n \in Node |-> 0]
  /\ votedFor = [n \in Node |-> None]
  /\ log = [n \in Node |-> <<>>]
  /\ commitIndex = [n \in Node |-> 0]
  /\ lastApplied = [n \in Node |-> 0]
  /\ nextIndex = [n \in Node |-> [m \in Node |-> 1]]
  /\ matchIndex = [n \in Node |-> [m \in Node |-> 0]]
  /\ leaderId = [n \in Node |-> None]
  /\ electionTimer = [n \in Node |-> 0]
  /\ kvStore = [n \in Node |-> [k \in Key |-> "DELETED"]]
  /\ pendingReads = [n \in Node |-> {}]
  /\ messages = {}
  /\ uncommittedSize = [n \in Node |-> 0]

TypeOK ==
  /\ state \in [Node -> StateType]
  /\ currentTerm \in [Node -> Nat]
  /\ votedFor \in [Node -> Node \cup {None}]
  /\ log \in [Node -> Seq(LogEntry)]
  /\ commitIndex \in [Node -> Nat]
  /\ lastApplied \in [Node -> Nat]
  /\ \A n \in Node : lastApplied[n] <= commitIndex[n] /\ commitIndex[n] <= Len(log[n])
  /\ nextIndex \in [Node -> [Node -> Nat]]
  /\ matchIndex \in [Node -> [Node -> Nat]]
  /\ leaderId \in [Node -> Node \cup {None}]
  /\ electionTimer \in [Node -> 0..MaxElectionTimeout]
  /\ kvStore \in [Node -> [Key -> Value \cup {"DELETED"}]]
  /\ pendingReads \in [Node -> SUBSET [client: Client, key: Key, opId: Nat, readIndex: Nat]]
  /\ \A msg \in messages: 
        \/ /\ msg.type = "RequestVote"
           /\ msg.from \in Node
           /\ msg.to \in Node
           /\ msg.term \in Nat
           /\ msg.prevLogIndex \in Nat
           /\ msg.prevLogTerm \in Nat
        \/ /\ msg.type = "RequestVoteResponse"
           /\ msg.from \in Node
           /\ msg.to \in Node
           /\ msg.term \in Nat
           /\ msg.success \in BOOLEAN
        \/ /\ msg.type = "AppendEntries"
           /\ msg.from \in Node
           /\ msg.to \in Node
           /\ msg.term \in Nat
           /\ msg.prevLogIndex \in Nat
           /\ msg.prevLogTerm \in Nat
           /\ msg.entries \in Seq(LogEntry)
           /\ msg.leaderCommit \in Nat
        \/ /\ msg.type = "AppendEntriesResponse"
           /\ msg.from \in Node
           /\ msg.to \in Node
           /\ msg.term \in Nat
           /\ msg.success \in BOOLEAN
           /\ msg.matchIndex \in Nat
        \/ /\ msg.type = "ClientRequest"
           /\ msg.from \in Client
           /\ msg.to \in Node
           /\ msg.clientReq \in [type: {"put","del","get"}, key: Key, value: Value \cup {None}, client: Client, opId: Nat]
        \/ /\ msg.type = "ClientResponse"
           /\ msg.to \in Client
           /\ msg.value \in Value \cup {"DELETED"}
        \/ /\ msg.type \in {"Heartbeat", "TimeoutNow"}
           /\ msg.from \in Node
           /\ msg.to \in Node
           /\ msg.term \in Nat
  /\ uncommittedSize \in [Node -> Nat]

ElectionTimeout(n) ==
  /\ state[n] \in {"Follower", "Candidate"}
  /\ electionTimer[n] >= MaxElectionTimeout
  /\ state' = [state EXCEPT ![n] = "Candidate"]
  /\ currentTerm' = [currentTerm EXCEPT ![n] = currentTerm[n] + 1]
  /\ votedFor' = [votedFor EXCEPT ![n] = n]
  /\ electionTimer' = [electionTimer EXCEPT ![n] = 0]
  /\ messages' = messages \cup 
        {[type |-> "RequestVote", from |-> n, to |-> m, term |-> currentTerm[n] + 1,
          prevLogIndex |-> LastLogIndex(n), prevLogTerm |-> LastLogTerm(n)] : m \in Node \ {n}}
  /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, kvStore, pendingReads, uncommittedSize>>

RequestVote(n, m) ==
  LET req == CHOOSE r \in messages: r.type = "RequestVote" /\ r.from = m /\ r.to = n IN
  LET term == req.term IN
  LET pli == req.prevLogIndex IN
  LET plt == req.prevLogTerm IN
  /\ req \in messages
  /\ IF term < currentTerm[n] 
        THEN 
          /\ messages' = messages \cup {[type |-> "RequestVoteResponse", from |-> n, to |-> m, term |-> currentTerm[n], success |-> FALSE]}
          /\ UNCHANGED <<state, currentTerm, votedFor>>
        ELSE 
          /\ \/ term > currentTerm[n] 
                /\ state' = [state EXCEPT ![n] = "Follower"]
                /\ currentTerm' = [currentTerm EXCEPT ![n] = term]
                /\ votedFor' = [votedFor EXCEPT ![n] = None]
             \/ UNCHANGED <<state, currentTerm, votedFor>>
          /\ IF (votedFor[n] = None \/ votedFor[n] = m) 
                /\ (plt > LastLogTerm(n) \/ (plt = LastLogTerm(n) /\ pli >= LastLogIndex(n)))
             THEN 
                /\ votedFor' = [votedFor EXCEPT ![n] = m]
                /\ messages' = messages \cup {[type |-> "RequestVoteResponse", from |-> n, to |-> m, term |-> term, success |-> TRUE]}
             ELSE 
                /\ messages' = messages \cup {[type |-> "RequestVoteResponse", from |-> n, to |-> m, term |-> term, success |-> FALSE]}
  /\ electionTimer' = [electionTimer EXCEPT ![n] = 0]
  /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, kvStore, pendingReads, uncommittedSize>>

RequestVoteResponse(n) ==
  LET resp == CHOOSE r \in messages: r.type = "RequestVoteResponse" /\ r.to = n IN
  LET sender == resp.from IN
  LET term == resp.term IN
  LET vote == resp.success IN
  /\ resp \in messages
  /\ state[n] = "Candidate"
  /\ term = currentTerm[n]
  /\ LET votes == { node \in Node : \E r \in messages: r.from = node /\ r.type = "RequestVoteResponse" /\ r.term = term /\ r.success = TRUE } IN
     Cardinality(votes) >= Majority
  /\ state' = [state EXCEPT ![n] = "Leader"]
  /\ leaderId' = [leaderId EXCEPT ![n] = n]
  /\ nextIndex' = [nextIndex EXCEPT ![n] = [o \in Node |-> LastLogIndex(n) + 1]]
  /\ matchIndex' = [matchIndex EXCEPT ![n] = [o \in Node |-> 0]]
  /\ messages' = messages \cup {[type |-> "Heartbeat", from |-> n, to |-> o, term |-> term] : o \in Node \ {n}}
  /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied, electionTimer, kvStore, pendingReads, uncommittedSize>>

SendAppendEntries(n) ==
  /\ IsLeader(n)
  /\ \E o \in Node \ {n}:
      LET ni == nextIndex[n][o] IN
      LET prevLogIndex == ni - 1 IN
      LET prevLogTerm == TermAt(n, prevLogIndex) IN
      LET entries == IF ni <= Len(log[n]) THEN SubSeq(log[n], ni, Len(log[n])) ELSE <<>> IN
      messages' = messages \cup {[type |-> "AppendEntries", from |-> n, to |-> o, term |-> currentTerm[n],
                                 prevLogIndex |-> prevLogIndex, prevLogTerm |-> prevLogTerm,
                                 entries |-> entries, leaderCommit |-> commitIndex[n]]}
  /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, electionTimer, kvStore, pendingReads, uncommittedSize>>

HandleAppendEntries(n) ==
  LET req == CHOOSE r \in messages: r.type = "AppendEntries" /\ r.to = n IN
  LET m == req.from IN
  LET term == req.term IN
  LET pli == req.prevLogIndex IN
  LET plt == req.prevLogTerm IN
  LET ents == req.entries IN
  LET lc == req.leaderCommit IN
  /\ req \in messages
  /\ IF term < currentTerm[n] 
        THEN 
          /\ messages' = messages \cup {[type |-> "AppendEntriesResponse", from |-> n, to |-> m, term |-> currentTerm[n], success |-> FALSE, matchIndex |-> 0]}
          /\ UNCHANGED <<log, commitIndex, state, currentTerm, leaderId>>
        ELSE 
          /\ IF term > currentTerm[n] 
                THEN 
                  /\ state' = [state EXCEPT ![n] = "Follower"]
                  /\ currentTerm' = [currentTerm EXCEPT ![n] = term]
                  /\ leaderId' = [leaderId EXCEPT ![n] = m]
                ELSE UNCHANGED <<state, currentTerm, leaderId>>
          /\ IF (pli = 0) \/ (pli <= Len(log[n]) /\ log[n][pli].term = plt)
                THEN 
                  /\ LET newLog == 
                         IF ents = <<>> THEN log[n]
                         ELSE IF Len(log[n]) >= pli + 1 
                              THEN SubSeq(log[n], 1, pli) \o ents
                              ELSE log[n] \o SubSeq(ents, Len(log[n]) - pli + 1, Len(ents)) IN
                     log' = [log EXCEPT ![n] = newLog]
                  /\ commitIndex' = [commitIndex EXCEPT ![n] = 
                         IF lc > commitIndex[n] THEN Min(lc, LastLogIndex(n)) ELSE commitIndex[n]]
                  /\ messages' = messages \cup {[type |-> "AppendEntriesResponse", from |-> n, to |-> m, term |-> term, success |-> TRUE, matchIndex |-> LastLogIndex(n)]}
                ELSE 
                  /\ messages' = messages \cup {[type |-> "AppendEntriesResponse", from |-> n, to |-> m, term |-> currentTerm[n], success |-> FALSE, matchIndex |-> 0]}
                  /\ UNCHANGED <<log, commitIndex>>
  /\ electionTimer' = [electionTimer EXCEPT ![n] = 0]
  /\ UNCHANGED <<votedFor, lastApplied, nextIndex, matchIndex, kvStore, pendingReads, uncommittedSize>>

ClientWriteRequest(n) ==
  LET req == CHOOSE r \in messages: r.type = "ClientRequest" /\ r.to = n /\ r.clientReq.type = "put" IN
  LET client == req.clientReq.client IN
  LET opId == req.clientReq.opId IN
  LET key == req.clientReq.key IN
  LET value == req.clientReq.value IN
  /\ IsLeader(n)
  /\ LET newEntry == [term |-> currentTerm[n], cmd |-> [type |-> "put", key |-> key, value |-> value, client |-> client, opId |-> opId]] IN
     /\ log' = [log EXCEPT ![n] = Append(log[n], newEntry)]
     /\ uncommittedSize' = [uncommittedSize EXCEPT ![n] = uncommittedSize[n] + 1]
     /\ messages' = messages \ {req}
  /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, electionTimer, kvStore, pendingReads>>

ClientReadRequest(n) ==
  LET req == CHOOSE r \in messages: r.type = "ClientRequest" /\ r.to = n /\ r.clientReq.type = "get" IN
  LET client == req.clientReq.client IN
  LET opId == req.clientReq.opId IN
  LET key == req.clientReq.key IN
  /\ IsLeader(n)
  /\ LET newEntry == [term |-> currentTerm[n], cmd |-> [type |-> "get", key |-> key, value |-> None, client |-> client, opId |-> opId]] IN
     /\ log' = [log EXCEPT ![n] = Append(log[n], newEntry)]
     /\ uncommittedSize' = [uncommittedSize EXCEPT ![n] = uncommittedSize[n] + 1]
     /\ pendingReads' = [pendingReads EXCEPT ![n] = pendingReads[n] \cup {[client |-> client, key |-> key, opId |-> opId, readIndex |-> commitIndex[n]]}]
     /\ messages' = messages \ {req}
  /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, electionTimer, kvStore>>

ApplyCommitted(n) ==
  /\ commitIndex[n] > lastApplied[n]
  /\ LET idx == lastApplied[n] + 1 IN
     /\ lastApplied' = [lastApplied EXCEPT ![n] = idx]
     /\ LET cmd == log[n][idx].cmd IN
        /\ IF cmd.type = "put" THEN
             kvStore' = [kvStore EXCEPT ![n][cmd.key] = cmd.value]
           ELSE IF cmd.type = "del" THEN
             kvStore' = [kvStore EXCEPT ![n][cmd.key] = "DELETED"]
           ELSE UNCHANGED kvStore
        /\ IF cmd.type \in {"put", "del"} THEN
             uncommittedSize' = [uncommittedSize EXCEPT ![n] = uncommittedSize[n] - 1]
           ELSE UNCHANGED uncommittedSize
        /\ IF cmd.type = "get" THEN
             \E readReq \in pendingReads[n]: 
                 readReq.client = cmd.client /\ readReq.opId = cmd.opId /\ readReq.key = cmd.key /\ idx >= readReq.readIndex
             /\ messages' = messages \cup {[type |-> "ClientResponse", to |-> cmd.client, value |-> kvStore[n][cmd.key]]}
             /\ pendingReads' = [pendingReads EXCEPT ![n] = pendingReads[n] \ {readReq}]
           ELSE UNCHANGED <<messages, pendingReads>>
  /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, leaderId, electionTimer>>

AdvanceCommitIndex(n) ==
  /\ IsLeader(n)
  /\ LET indices == { k \in 1..Len(log[n]) : k > commitIndex[n] /\ log[n][k].term = currentTerm[n] } IN
     LET N == CHOOSE k \in indices : \A j \in indices : j <= k IN
     /\ Cardinality({o \in Node \ {n} : matchIndex[n][o] >= N}) >= Majority
  /\ commitIndex' = [commitIndex EXCEPT ![n] = N]
  /\ UNCHANGED <<state, currentTerm, votedFor, log, lastApplied, nextIndex, matchIndex, leaderId, electionTimer, kvStore, pendingReads, messages, uncommittedSize>>

Next ==
  \/ \E n \in Node: ElectionTimeout(n)
  \/ \E n, m \in Node: RequestVote(n, m)
  \/ \E n \in Node: RequestVoteResponse(n)
  \/ \E n \in Node: SendAppendEntries(n)
  \/ \E n \in Node: HandleAppendEntries(n)
  \/ \E n \in Node: ClientWriteRequest(n)
  \/ \E n \in Node: ClientReadRequest(n)
  \/ \E n \in Node: ApplyCommitted(n)
  \/ \E n \in Node: AdvanceCommitIndex(n)

ElectionSafety == \A n1, n2 \in Node:
  (state[n1] = "Leader" /\ state[n2] = "Leader") => currentTerm[n1] # currentTerm[n2]

LeaderCompleteness == \A n1 \in Node, n2 \in Node, i \in 1..Len(log[n1]):
  (state[n1] = "Leader" /\ log[n1][i].term = currentTerm[n1] /\ i <= commitIndex[n1])
  => (i <= Len(log[n2]) /\ log[n2][i] = log[n1][i])

StateMachineSafety == \A n1 \in Node, n2 \in Node, idx \in 1..Min(Len(log[n1]), Len(log[n2])):
  (lastApplied[n1] >= idx /\ lastApplied[n2] >= idx) => kvStore[n1][log[n1][idx].cmd.key] = kvStore[n2][log[n2][idx].cmd.key]

LinearizableReads == \A resp \in {m \in messages: m.type = "ClientResponse"}:
  \E req \in {m \in messages: m.type = "ClientRequest" /\ m.clientReq.type = "get"}:
      req.clientReq.key = resp.key
      /\ \A n \in Node: 
          (state[n] = "Leader" \/ lastApplied[n] >= req.clientReq.readIndex) 
          => kvStore[n][resp.key] = resp.value

Spec == Init /\ [][Next]_vars
====