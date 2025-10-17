---- MODULE redisraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Nodes, NoLeader

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
    electionTimeout,
    votesResponded,
    votesGranted

vars == <<state, currentTerm, votedFor, log, commitIndex, lastApplied, 
          nextIndex, matchIndex, leaderId, electionTimeout, 
          votesResponded, votesGranted>>

NodeState == {"Follower", "Candidate", "Leader", "PreCandidate"}

MessageType == {"AppendEntries", "AppendEntriesResponse", 
                "RequestVote", "RequestVoteResponse"}

Message == [type : MessageType, term : Nat, src : Nodes, dst : Nodes, 
            success : BOOLEAN, voteGranted : BOOLEAN, 
            prevLogIndex : Nat, prevLogTerm : Nat, 
            entries : Seq({}), leaderCommit : Nat]

Init ==
    /\ state = [n \in Nodes |-> "Follower"]
    /\ currentTerm = [n \in Nodes |-> 0]
    /\ votedFor = [n \in Nodes |-> NoLeader]
    /\ log = [n \in Nodes |-> <<>>]
    /\ commitIndex = [n \in Nodes |-> 0]
    /\ lastApplied = [n \in Nodes |-> 0]
    /\ nextIndex = [n \in Nodes |-> [m \in Nodes |-> 1]]
    /\ matchIndex = [n \in Nodes |-> [m \in Nodes |-> 0]]
    /\ leaderId = [n \in Nodes |-> NoLeader]
    /\ electionTimeout = [n \in Nodes |-> {}]
    /\ votesResponded = [n \in Nodes |-> {}]
    /\ votesGranted = [n \in Nodes |-> {}]

TypeOK ==
    /\ state \in [Nodes -> NodeState]
    /\ currentTerm \in [Nodes -> Nat]
    /\ votedFor \in [Nodes -> Nodes \cup {NoLeader}]
    /\ log \in [Nodes -> Seq([])]
    /\ commitIndex \in [Nodes -> Nat]
    /\ lastApplied \in [Nodes -> Nat]
    /\ nextIndex \in [Nodes -> [Nodes -> Nat]]
    /\ matchIndex \in [Nodes -> [Nodes -> Nat]]
    /\ leaderId \in [Nodes -> Nodes \cup {NoLeader}]
    /\ electionTimeout \in [Nodes -> SUBSET(Nodes)]
    /\ votesResponded \in [Nodes -> SUBSET(Nodes)]
    /\ votesGranted \in [Nodes -> SUBSET(Nodes)]

ElectionTimeout(n) ==
    /\ state[n] \in {"Follower", "Candidate"}
    /\ \/ electionTimeout[n] = {}
       \/ \E m \in electionTimeout[n] : TRUE
    /\ state' = [state EXCEPT ![n] = "Candidate"]
    /\ currentTerm' = [currentTerm EXCEPT ![n] = currentTerm[n] + 1]
    /\ votedFor' = [votedFor EXCEPT ![n] = n]
    /\ votesResponded' = [votesResponded EXCEPT ![n] = {}]
    /\ votesGranted' = [votesGranted EXCEPT ![n] = {n}]
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, electionTimeout>>

BecomeLeader(n) ==
    /\ state[n] = "Candidate"
    /\ Cardinality(votesGranted[n]) > Cardinality(Nodes) \div 2
    /\ state' = [state EXCEPT ![n] = "Leader"]
    /\ leaderId' = [leaderId EXCEPT ![n] = n]
    /\ nextIndex' = [nextIndex EXCEPT ![n] = [m \in Nodes |-> Len(log[n]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![n] = [m \in Nodes |-> 0]]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied, electionTimeout, votesResponded, votesGranted>>

SendAppendEntries(n, m) ==
    /\ state[n] = "Leader"
    /\ nextIndex[n][m] <= Len(log[n])
    /\ nextIndex' = [nextIndex EXCEPT ![n][m] = nextIndex[n][m] + 1]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, matchIndex, leaderId, electionTimeout, votesResponded, votesGranted>>

ReceiveAppendEntries(n, m, msg) ==
    /\ msg.term >= currentTerm[n]
    /\ \/ msg.term > currentTerm[n]
          /\ currentTerm' = [currentTerm EXCEPT ![n] = msg.term]
          /\ state' = [state EXCEPT ![n] = "Follower"]
          /\ votedFor' = [votedFor EXCEPT ![n] = NoLeader]
       \/ UNCHANGED <<currentTerm, state, votedFor>>
    /\ leaderId' = [leaderId EXCEPT ![n] = msg.src]
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, electionTimeout, votesResponded, votesGranted>>

Next ==
    \/ \E n \in Nodes : ElectionTimeout(n)
    \/ \E n \in Nodes : BecomeLeader(n)
    \/ \E n, m \in Nodes : SendAppendEntries(n, m)
    \/ \E n \in Nodes, msg \in Message : ReceiveAppendEntries(n, m, msg)

Spec == Init /\ [][Next]_vars

====