
---- MODULE etcdraft ----
EXTENDS Naturals, Sequences, FiniteSets, TLC
CONSTANTS Nodes, ClientRequest
VARIABLES 
    state, 
    currentTerm, 
    votedFor, 
    log, 
    commitIndex, 
    nextIndex, 
    matchIndex

\* Type definitions and helper functions
NotLeader == {"Follower", "Candidate"}
LastLogTerm(node) == IF log[node] = <<>> THEN 0 ELSE log[node][Len(log[node])].term
LastLogIndex(node) == Len(log[node])
LogUpToDate(candidate, voter) ==
    \/ LastLogTerm(candidate) > LastLogTerm(voter)
    \/ /\ LastLogTerm(candidate) = LastLogTerm(voter)
       /\ LastLogIndex(candidate) >= LastLogIndex(voter)
Majority == Cardinality(Nodes) \div 2 + 1

\* State initialization
Init == 
    /\ state = [n \in Nodes |-> "Follower"]
    /\ currentTerm = [n \in Nodes |-> 0]
    /\ votedFor = [n \in Nodes |-> nil]
    /\ log = [n \in Nodes |-> <<>>]
    /\ commitIndex = [n \in Nodes |-> 0]
    /\ nextIndex = [n \in Nodes |-> [m \in Nodes |-> 1]]
    /\ matchIndex = [n \in Nodes |-> [m \in Nodes |-> 0]]

\* Election timeout
BecomeCandidate(node) ==
    /\ state[node] \in NotLeader
    /\ state' = [state EXCEPT ![node] = "Candidate"]
    /\ currentTerm' = [currentTerm EXCEPT ![node] = currentTerm[node] + 1]
    /\ votedFor' = [votedFor EXCEPT ![node] = node]
    /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex>>

\* Vote granting
GrantVote(voter, candidate) ==
    /\ candidate \in Nodes \ {voter}
    /\ state[candidate] = "Candidate"
    /\ currentTerm[candidate] >= currentTerm[voter]
    /\ \/ currentTerm[candidate] > currentTerm[voter]
       \/ votedFor[voter] \in {nil, candidate}
    /\ LogUpToDate(candidate, voter)
    /\ votedFor' = [votedFor EXCEPT ![voter] = candidate]
    /\ \/ currentTerm[candidate] > currentTerm[voter]
           /\ currentTerm' = [currentTerm EXCEPT ![voter] = currentTerm[candidate]]
           /\ state' = [state EXCEPT ![voter] = "Follower"]
       \/ currentTerm' = currentTerm
          /\ state' = state
    /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex>>

\* Leader election
BecomeLeader(node) ==
    /\ state[node] = "Candidate"
    /\ Cardinality({v \in Nodes: votedFor[v] = node}) >= Majority
    /\ state' = [state EXCEPT ![node] = "Leader"]
    /\ nextIndex' = [nextIndex EXCEPT ![node] = [n \in Nodes |-> Len(log[node]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![node] = [n \in Nodes |-> 0]]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex>>

\* Log replication
AppendEntries(leader, follower) ==
    LET prevIndex == nextIndex[leader][follower] - 1
        prevTerm == IF prevIndex = 0 THEN 0 ELSE log[leader][prevIndex].term
        entries == SubSeq(log[leader], nextIndex[leader][follower], Len(log[leader]))
        leaderCommit == commitIndex[leader]
    IN
    /\ state[leader] = "Leader"
    /\ prevIndex >= 0
    /\ \/ currentTerm[leader] < currentTerm[follower]
           /\ state' = [state EXCEPT ![leader] = "Follower"]
           /\ currentTerm' = [currentTerm EXCEPT ![leader] = currentTerm[follower]]
           /\ votedFor' = [votedFor EXCEPT ![leader] = nil]
           /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex>>
       \/ /\ currentTerm[leader] >= currentTerm[follower]
          /\ \/ currentTerm[leader] > currentTerm[follower]
                 /\ currentTerm' = [currentTerm EXCEPT ![follower] = currentTerm[leader]]
                 /\ state' = [state EXCEPT ![follower] = "Follower"]
                 /\ votedFor' = [votedFor EXCEPT ![follower] = nil]
             \/ UNCHANGED <<currentTerm, state, votedFor>>
          /\ \/ /\ prevIndex = 0
                 \/ /\ prevIndex <= Len(log[follower])
                    /\ log[follower][prevIndex].term = prevTerm
                 /\ log' = [log EXCEPT ![follower] = 
                            SubSeq(log[follower], 1, prevIndex) \o entries]
                 /\ nextIndex' = [nextIndex EXCEPT ![leader][follower] = prevIndex + Len(entries) + 1]
                 /\ matchIndex' = [matchIndex EXCEPT ![leader][follower] = prevIndex + Len(entries)]
                 /\ commitIndex' = [commitIndex EXCEPT ![follower] = 
                     IF leaderCommit > commitIndex[follower] 
                     THEN Min(leaderCommit, prevIndex + Len(entries)) 
                     ELSE commitIndex[follower]]
             \/ /\ nextIndex' = [nextIndex EXCEPT ![leader][follower] = prevIndex]
                /\ UNCHANGED <<log, commitIndex, matchIndex>>
          /\ UNCHANGED <<votedFor>>

\* Client request handling
AppendNewEntry(leader) ==
    /\ state[leader] = "Leader"
    /\ LET newEntry == [term |-> currentTerm[leader], cmd |-> CHOOSE c \in ClientRequest: TRUE]
       newLog == log[leader] \o <<newEntry>>
    IN
    /\ log' = [log EXCEPT ![leader] = newLog]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, nextIndex, matchIndex>>

\* Commit propagation
UpdateCommitIndex(leader) ==
    /\ state[leader] = "Leader"
    /\ LET indices == {i \in 1..Len(log[leader]): 
                       log[leader][i].term = currentTerm[leader] /\
                       Cardinality({n \in Nodes: matchIndex[leader][n] >= i}) >= Majority}
       newCommit == IF indices = {} THEN commitIndex[leader] ELSE Max(indices)
    IN
    /\ commitIndex' = [commitIndex EXCEPT ![leader] = newCommit]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, nextIndex, matchIndex>>

\* Next-state relation
Next == 
    \/ \E n \in Nodes: BecomeCandidate(n)
    \/ \E v, c \in Nodes: c # v /\ GrantVote(v, c)
    \/ \E n \in Nodes: BecomeLeader(n)
    \/ \E l, f \in Nodes: l # f /\ AppendEntries(l, f)
    \/ \E l \in Nodes: AppendNewEntry(l)
    \/ \E l \in Nodes: UpdateCommitIndex(l)

\* Safety properties
TypeOK == 
    /\ state \in [Nodes -> {"Follower", "Candidate", "Leader"}]
    /\ currentTerm \in [Nodes -> Nat]
    /\ votedFor \in [Nodes -> (Nodes \cup {nil})]
    /\ log \in [Nodes -> Seq([term: Nat, cmd: ClientRequest])]
    /\ commitIndex \in [Nodes -> Nat]
    /\ nextIndex \in [Nodes -> [Nodes -> Nat]]
    /\ matchIndex \in [Nodes -> [Nodes -> Nat]]

OneLeader == 
    \A n1, n2 \in Nodes: 
        state[n1] = "Leader" /\ state[n2] = "Leader" => n1 = n2

LogMatching ==
    \A n1, n2 \in Nodes, i \in 1..Min(Len(log[n1]), Len(log[n2])):
        log[n1][i].term = log[n2][i].term => log[n1][i].cmd = log[n2][i].cmd

LeaderCompleteness ==
    \A leader, n \in Nodes, i \in 1..commitIndex[leader]:
        state[leader] = "Leader" /\ i <= Len(log[n]) => log[leader][i] = log[n][i]

\* Specification
Spec == Init /\ [][Next]_<<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex>>
====