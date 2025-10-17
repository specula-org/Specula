
---- MODULE etcdraft ----
EXTENDS Naturals, Sequences, FiniteSets
CONSTANTS Servers, \* Set of servers
          QuorumSize \* Size of quorum needed for consensus

VARIABLES state, \* Server state: "Follower" | "Candidate" | "Leader"
         currentTerm, \* Latest term server has seen
         votedFor, \* Server voted for in current term (or Nil)
         log, \* Log entries: sequence of [term, command]
         commitIndex, \* Highest log index known committed
         nextIndex, \* Leader: next log index to send to each server
         matchIndex, \* Leader: highest log index replicated on server
         votesReceived \* Set of servers granting vote in current term

vars == <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votesReceived>>

Nil == CHOOSE n : n \notin Servers

\* Type definitions
IsFollower(server) == state[server] = "Follower"
IsCandidate(server) == state[server] = "Candidate"
IsLeader(server) == state[server] = "Leader"
LogTerm(server, i) == log[server][i][1]  \* Term of log entry at index i

\* Initial state
Init == 
    /\ state = [s \in Servers |-> "Follower"]
    /\ currentTerm = [s \in Servers |-> 0]
    /\ votedFor = [s \in Servers |-> Nil]
    /\ log = [s \in Servers |-> << >>]
    /\ commitIndex = [s \in Servers |-> 0]
    /\ nextIndex = [s \in Servers |-> [t \in Servers |-> 1]]
    /\ matchIndex = [s \in Servers |-> [t \in Servers |-> 0]]
    /\ votesReceived = [s \in Servers |-> {}]

\* Election timeout: Follower -> Candidate
BecomeCandidate(server) == 
    /\ IsFollower(server)
    /\ state' = [state EXCEPT ![server] = "Candidate"]
    /\ currentTerm' = [currentTerm EXCEPT ![server] = currentTerm[server] + 1]
    /\ votedFor' = [votedFor EXCEPT ![server] = server]
    /\ votesReceived' = [votesReceived EXCEPT ![server] = {server}]
    /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex>>

\* RequestVote RPC
SendVoteRequest(server, candidate) == 
    /\ candidate /= server
    /\ IsCandidate(candidate)
    /\ \/ IsFollower(server) \/ IsCandidate(server)
    /\ LET lastLogIndex == Len(log[server])
           lastLogTerm == IF lastLogIndex > 0 THEN LogTerm(server, lastLogIndex) ELSE 0
           candidateLastLogIndex == Len(log[candidate])
           candidateLastLogTerm == IF candidateLastLogIndex > 0 THEN LogTerm(candidate, candidateLastLogIndex) ELSE 0
    IN /\ ( (currentTerm[server] < currentTerm[candidate])
           \/ (currentTerm[server] = currentTerm[candidate] /\ (votedFor[server] = Nil \/ votedFor[server] = candidate)) )
       /\ ( (lastLogTerm < candidateLastLogTerm)
           \/ (lastLogTerm = candidateLastLogTerm /\ lastLogIndex <= candidateLastLogIndex) )
    /\ votedFor' = [votedFor EXCEPT ![server] = candidate]
    /\ votesReceived' = [votesReceived EXCEPT ![candidate] = votesReceived[candidate] \cup {server}]
    /\ UNCHANGED <<state, currentTerm, log, commitIndex, nextIndex, matchIndex>>

\* Win election: Candidate -> Leader
BecomeLeader(server) == 
    /\ IsCandidate(server)
    /\ Cardinality(votesReceived[server]) >= QuorumSize
    /\ state' = [state EXCEPT ![server] = "Leader"]
    /\ nextIndex' = [nextIndex EXCEPT ![server] = [s \in Servers |-> Len(log[server]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![server] = [s \in Servers |-> 0]]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, votesReceived>>

\* AppendEntries RPC (heartbeat)
SendAppendEntries(leader, follower) == 
    /\ IsLeader(leader)
    /\ \/ IsFollower(follower) \/ IsCandidate(follower)
    /\ currentTerm[follower] <= currentTerm[leader]
    /\ LET prevIndex == nextIndex[leader][follower] - 1
           prevTerm == IF prevIndex > 0 THEN LogTerm(leader, prevIndex) ELSE 0
           newEntries == IF nextIndex[leader][follower] <= Len(log[leader])
                         THEN [i \in nextIndex[leader][follower]..Len(log[leader]) |-> log[leader][i]]
                         ELSE << >>
    IN /\ (prevIndex = 0) \/ (prevIndex <= Len(log[follower]) /\ LogTerm(follower, prevIndex) = prevTerm)
       /\ \/ newEntries = << >>  \* Heartbeat - no log change
          \/ log' = [log EXCEPT ![follower] = SubSeq(log[follower], 1, prevIndex) \o newEntries]
       /\ currentTerm' = [currentTerm EXCEPT ![follower] = currentTerm[leader]]
       /\ state' = [state EXCEPT ![follower] = "Follower"]
       /\ votedFor' = [votedFor EXCEPT ![follower] = Nil]
       /\ nextIndex' = [nextIndex EXCEPT ![leader][follower] = prevIndex + 1 + Len(newEntries)]
       /\ matchIndex' = [matchIndex EXCEPT ![leader][follower] = prevIndex + Len(newEntries)]
       /\ UNCHANGED <<commitIndex, votesReceived>>

\* Leader commits log entries
CommitEntry(leader) == 
    /\ IsLeader(leader)
    /\ LET indices == { i \in 1..Len(log[leader]) : 
                    /\ i > commitIndex[leader]
                    /\ Cardinality({ s \in Servers : matchIndex[leader][s] >= i }) >= QuorumSize
                    /\ LogTerm(leader, i) = currentTerm[leader] }
           N == IF indices = {} THEN commitIndex[leader] ELSE Max(indices)
    IN commitIndex' = [commitIndex EXCEPT ![leader] = N]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, nextIndex, matchIndex, votesReceived>>

\* Apply committed entries to state machine (abstracted)
ApplyLog(server) == 
    /\ commitIndex[server] > 0
    /\ UNCHANGED vars

\* Next state relation
Next == 
    \/ \E server \in Servers : BecomeCandidate(server)
    \/ \E server, candidate \in Servers : SendVoteRequest(server, candidate)
    \/ \E server \in Servers : BecomeLeader(server)
    \/ \E leader, follower \in Servers : SendAppendEntries(leader, follower)
    \/ \E leader \in Servers : CommitEntry(leader)
    \/ \E server \in Servers : ApplyLog(server)

\* Type invariant
TypeInv == 
    /\ state \in [Servers -> {"Follower", "Candidate", "Leader"}]
    /\ currentTerm \in [Servers -> Nat]
    /\ votedFor \in [Servers -> Servers \cup {Nil}]
    /\ log \in [Servers -> Seq(Nat \times {})]  \* Sequence of [term, command]
    /\ commitIndex \in [Servers -> Nat]
    /\ nextIndex \in [Servers -> [Servers -> Nat]]
    /\ matchIndex \in [Servers -> [Servers -> Nat]]
    /\ votesReceived \in [Servers -> SUBSET Servers]

\* At most one leader per term
OneLeaderPerTerm == 
    \A t \in Nat : 
        Cardinality({ s \in Servers : currentTerm[s] = t /\ IsLeader(s) }) =< 1

\* Log matching property
LogMatching == 
    \A s1, s2 \in Servers : 
        \A i \in 1..Min(Len(log[s1]), Len(log[s2])) : 
            LogTerm(s1, i) = LogTerm(s2, i) => log[s1][i] = log[s2][i]

\* Safety property: committed entries remain
Consistency == 
    \A s1, s2 \in Servers : 
        \A i \in 1..Min(commitIndex[s1], commitIndex[s2]) : 
            log[s1][i] = log[s2][i]

\* Liveness: eventually a leader is elected
Liveness == 
    <>(\E s \in Servers : IsLeader(s))

\* Main specification
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

THEOREM Spec => []TypeInv

====