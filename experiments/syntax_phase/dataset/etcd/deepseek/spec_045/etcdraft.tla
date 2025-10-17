
---- MODULE etcdraft ----
EXTENDS Naturals, Sequences, FiniteSets
CONSTANTS Servers, Keys, Values

None == CHOOSE n: n \notin Servers
NotFound == CHOOSE nf: nf \notin Values
OPERATION == [type: {"PUT"}, key: Keys, value: Values] \cup [type: {"GET"}, key: Keys]
LogEntry == [term: Nat, op: OPERATION]

VARIABLES
  state,
  currentTerm,
  votedFor,
  log,
  commitIndex,
  lastApplied,
  nextIndex,
  matchIndex,
  kvStore,
  leader,
  votesReceived

vars == <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, kvStore, leader, votesReceived>>

Server == Servers
Quorum == Cardinality(Servers) \div 2 + 1

ApplyOp(op, store) == 
  IF op.type = "PUT" THEN [k \in Keys |-> IF k = op.key THEN op.value ELSE store[k]]
  ELSE store

ApplyLog(server) == 
  LET start == lastApplied[server] + 1
      end == commitIndex[server]
      f[i \in start..end] == 
        IF i = start 
        THEN ApplyOp(log[server][start].op, kvStore[server])
        ELSE ApplyOp(log[server][i].op, f[i-1])
  IN
    /\ lastApplied[server] < end
    /\ lastApplied' = [lastApplied EXCEPT ![server] = end]
    /\ kvStore' = [kvStore EXCEPT ![server] = f[end]]

TypeOK == 
  /\ state \in [Server -> {"Follower", "Candidate", "Leader"}]
  /\ currentTerm \in [Server -> Nat]
  /\ votedFor \in [Server -> Server \cup {None}]
  /\ log \in [Server -> Seq(LogEntry)]
  /\ commitIndex \in [Server -> Nat]
  /\ lastApplied \in [Server -> Nat]
  /\ nextIndex \in [Server -> [Server -> Nat]]
  /\ matchIndex \in [Server -> [Server -> Nat]]
  /\ kvStore \in [Server -> [Keys -> Values \cup {NotFound}]]
  /\ leader \in Server
  /\ votesReceived \in SUBSET Server

Init == 
  /\ state = [s \in Server |-> "Follower"]
  /\ currentTerm = [s \in Server |-> 0]
  /\ votedFor = [s \in Server |-> None]
  /\ log = [s \in Server |-> <<>>]
  /\ commitIndex = [s \in Server |-> 0]
  /\ lastApplied = [s \in Server |-> 0]
  /\ nextIndex = [s \in Server |-> [f \in Server |-> 1]]
  /\ matchIndex = [s \in Server |-> [f \in Server |-> 0]]
  /\ kvStore = [s \in Server |-> [k \in Keys |-> NotFound]]
  /\ leader \in Server
  /\ votesReceived = {}

BecomeCandidate(server) == 
  /\ state[server] \in {"Follower", "Candidate"}
  /\ currentTerm' = [currentTerm EXCEPT ![server] = currentTerm[server] + 1]
  /\ state' = [state EXCEPT ![server] = "Candidate"]
  /\ votedFor' = [votedFor EXCEPT ![server] = server]
  /\ votesReceived' = {server}

RequestVote(server, follower) == 
  /\ state[server] = "Candidate"
  /\ LET prevLogIndex == Len(log[server])
        prevLogTerm == IF prevLogIndex > 0 THEN log[server][prevLogIndex].term ELSE 0
        granted == /\ currentTerm[follower] <= currentTerm[server]
                   /\ \/ votedFor[follower] = None
                      \/ votedFor[follower] = server
                   /\ \/ Len(log[follower]) <= prevLogIndex
                      \/ (Len(log[follower]) > prevLogIndex /\ log[follower][prevLogIndex].term = prevLogTerm)
  IN
    IF granted 
    THEN /\ votedFor' = [votedFor EXCEPT ![follower] = server]
         /\ votesReceived' = votesReceived \cup {follower}
    ELSE UNCHANGED <<votedFor, votesReceived>>

BecomeLeader(server) == 
  /\ state[server] = "Candidate"
  /\ Cardinality(votesReceived) >= Quorum
  /\ state' = [state EXCEPT ![server] = "Leader"]
  /\ nextIndex' = [nextIndex EXCEPT ![server] = [s \in Server |-> Len(log[server]) + 1]]
  /\ matchIndex' = [matchIndex EXCEPT ![server] = [s \in Server |-> 0]]
  /\ leader' = server
  /\ votesReceived' = {}

AppendEntries(leader, follower) == 
  /\ state[leader] = "Leader"
  /\ nextIndex[leader][follower] <= Len(log[leader])
  /\ LET prevLogIndex == nextIndex[leader][follower] - 1
        prevLogTerm == IF prevLogIndex > 0 THEN log[leader][prevLogIndex].term ELSE 0
        entries == SubSeq(log[leader], nextIndex[leader][follower], Len(log[leader]))
        success == prevLogIndex = 0 \/ 
                  (prevLogIndex <= Len(log[follower]) /\ 
                   log[follower][prevLogIndex].term = prevLogTerm)
  IN
    IF success
    THEN /\ log' = [log EXCEPT ![follower] = 
                     IF prevLogIndex > 0 
                     THEN SubSeq(log[follower], 1, prevLogIndex) \o entries
                     ELSE entries]
         /\ nextIndex' = [nextIndex EXCEPT ![leader][follower] = Len(log[leader]) + 1]
         /\ matchIndex' = [matchIndex EXCEPT ![leader][follower] = Len(log[leader])]
    ELSE /\ nextIndex' = [nextIndex EXCEPT ![leader][follower] = nextIndex[leader][follower] - 1]
         /\ UNCHANGED <<log, matchIndex>>

Commit(leader) == 
  /\ state[leader] = "Leader"
  /\ LET N == Len(log[leader])
        commitSet == { i \in (commitIndex[leader]+1)..N : 
                      Cardinality({s \in Server: matchIndex[leader][s] >= i}) >= Quorum }
  IN 
    IF commitSet # {}
    THEN LET newCommit == CHOOSE i \in commitSet: TRUE
         IN commitIndex' = [commitIndex EXCEPT ![s \in Server] = IF s = leader THEN newCommit ELSE MIN(newCommit, commitIndex[s])]
    ELSE UNCHANGED commitIndex

ClientRequest(server, op) == 
  /\ state[server] = "Leader"
  /\ log' = [log EXCEPT ![server] = Append(@, [term |-> currentTerm[server], op |-> op])]
  /\ nextIndex' = [nextIndex EXCEPT ![server] = [s \in Server |-> Len(log[server]) + 1]]
  /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, matchIndex, kvStore, leader, votesReceived>>

Next == 
  \/ \E server \in Server: BecomeCandidate(server)
  \/ \E server, follower \in Server: RequestVote(server, follower)
  \/ \E server \in Server: BecomeLeader(server)
  \/ \E leader, follower \in Server: AppendEntries(leader, follower)
  \/ \E leader \in Server: Commit(leader)
  \/ \E server \in Server: ApplyLog(server)
  \/ \E server \in Server, op \in OPERATION: ClientRequest(server, op)

Spec == Init /\ [][Next]_vars

Termination == <>(\A s \in Server: lastApplied[s] = commitIndex[s])

====