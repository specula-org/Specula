---- MODULE Raft ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS 
    Nodes,
    MaxTerm,
    MaxLogIndex

VARIABLES
    \* Core Raft state
    currentTerm,
    votedFor,
    log,
    commitIndex,
    state,
    leaderId,
    
    \* Leader state
    nextIndex,
    matchIndex,
    leadTransferee,
    
    \* Election state
    electionElapsed,
    heartbeatElapsed,
    randomizedElectionTimeout,
    votes,
    
    \* Message queues
    msgs,
    msgsAfterAppend,
    
    \* Configuration
    isLearner,
    pendingConfIndex,
    uncommittedSize

vars == <<currentTerm, votedFor, log, commitIndex, state, leaderId, 
          nextIndex, matchIndex, leadTransferee, electionElapsed, 
          heartbeatElapsed, randomizedElectionTimeout, votes, msgs, 
          msgsAfterAppend, isLearner, pendingConfIndex, uncommittedSize>>

TypeInvariant ==
    /\ currentTerm \in [Nodes -> Nat]
    /\ votedFor \in [Nodes -> Nodes \cup {0}]
    /\ log \in [Nodes -> Seq(Nat)]
    /\ commitIndex \in [Nodes -> Nat]
    /\ state \in [Nodes -> {"follower", "candidate", "leader", "precandidate"}]
    /\ leaderId \in [Nodes -> Nodes \cup {0}]
    /\ nextIndex \in [Nodes -> [Nodes -> Nat]]
    /\ matchIndex \in [Nodes -> [Nodes -> Nat]]
    /\ leadTransferee \in [Nodes -> Nodes \cup {0}]
    /\ electionElapsed \in [Nodes -> Nat]
    /\ heartbeatElapsed \in [Nodes -> Nat]
    /\ randomizedElectionTimeout \in [Nodes -> Nat]
    /\ votes \in [Nodes -> [Nodes -> BOOLEAN]]
    /\ msgs \in SUBSET [from: Nodes, to: Nodes, type: STRING, term: Nat]
    /\ msgsAfterAppend \in SUBSET [from: Nodes, to: Nodes, type: STRING, term: Nat]
    /\ isLearner \in [Nodes -> BOOLEAN]
    /\ pendingConfIndex \in [Nodes -> Nat]
    /\ uncommittedSize \in [Nodes -> Nat]

Init ==
    /\ currentTerm = [n \in Nodes |-> 0]
    /\ votedFor = [n \in Nodes |-> 0]
    /\ log = [n \in Nodes |-> <<>>]
    /\ commitIndex = [n \in Nodes |-> 0]
    /\ state = [n \in Nodes |-> "follower"]
    /\ leaderId = [n \in Nodes |-> 0]
    /\ nextIndex = [n \in Nodes |-> [m \in Nodes |-> 1]]
    /\ matchIndex = [n \in Nodes |-> [m \in Nodes |-> 0]]
    /\ leadTransferee = [n \in Nodes |-> 0]
    /\ electionElapsed = [n \in Nodes |-> 0]
    /\ heartbeatElapsed = [n \in Nodes |-> 0]
    /\ randomizedElectionTimeout = [n \in Nodes |-> 10]
    /\ votes = [n \in Nodes |-> [m \in Nodes |-> FALSE]]
    /\ msgs = {}
    /\ msgsAfterAppend = {}
    /\ isLearner = [n \in Nodes |-> FALSE]
    /\ pendingConfIndex = [n \in Nodes |-> 0]
    /\ uncommittedSize = [n \in Nodes |-> 0]

becomeFollower(n, term, lead) ==
    /\ state' = [state EXCEPT ![n] = "follower"]
    /\ currentTerm' = [currentTerm EXCEPT ![n] = term]
    /\ leaderId' = [leaderId EXCEPT ![n] = lead]
    /\ electionElapsed' = [electionElapsed EXCEPT ![n] = 0]
    /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![n] = 0]
    /\ UNCHANGED <<votedFor, log, commitIndex, nextIndex, matchIndex, 
                   leadTransferee, randomizedElectionTimeout, votes, msgs, 
                   msgsAfterAppend, isLearner, pendingConfIndex, uncommittedSize>>

becomeCandidate(n) ==
    /\ state[n] # "leader"
    /\ state' = [state EXCEPT ![n] = "candidate"]
    /\ currentTerm' = [currentTerm EXCEPT ![n] = currentTerm[n] + 1]
    /\ votedFor' = [votedFor EXCEPT ![n] = n]
    /\ electionElapsed' = [electionElapsed EXCEPT ![n] = 0]
    /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![n] = 0]
    /\ votes' = [votes EXCEPT ![n] = [m \in Nodes |-> FALSE]]
    /\ UNCHANGED <<log, commitIndex, leaderId, nextIndex, matchIndex, 
                   leadTransferee, randomizedElectionTimeout, msgs, 
                   msgsAfterAppend, isLearner, pendingConfIndex, uncommittedSize>>

becomePreCandidate(n) ==
    /\ state[n] # "leader"
    /\ state' = [state EXCEPT ![n] = "precandidate"]
    /\ leaderId' = [leaderId EXCEPT ![n] = 0]
    /\ votes' = [votes EXCEPT ![n] = [m \in Nodes |-> FALSE]]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, 
                   leadTransferee, electionElapsed, heartbeatElapsed, 
                   randomizedElectionTimeout, msgs, msgsAfterAppend, isLearner, 
                   pendingConfIndex, uncommittedSize>>

becomeLeader(n) ==
    /\ state[n] # "follower"
    /\ state' = [state EXCEPT ![n] = "leader"]
    /\ leaderId' = [leaderId EXCEPT ![n] = n]
    /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![n] = 0]
    /\ nextIndex' = [nextIndex EXCEPT ![n] = [m \in Nodes |-> Len(log[n]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![n] = [m \in Nodes |-> 0]]
    /\ pendingConfIndex' = [pendingConfIndex EXCEPT ![n] = Len(log[n])]
    /\ log' = [log EXCEPT ![n] = Append(log[n], currentTerm[n])]
    /\ UNCHANGED <<currentTerm, votedFor, commitIndex, leadTransferee, 
                   electionElapsed, randomizedElectionTimeout, votes, msgs, 
                   msgsAfterAppend, isLearner, uncommittedSize>>

hup(n, campaignType) ==
    /\ state[n] # "leader"
    /\ \/ /\ campaignType = "preelection"
          /\ becomePreCandidate(n)
       \/ /\ campaignType = "election"
          /\ becomeCandidate(n)

campaign(n, campaignType) ==
    /\ \/ /\ campaignType = "preelection"
          /\ becomePreCandidate(n)
       \/ /\ campaignType = "election"
          /\ becomeCandidate(n)
    /\ msgs' = msgs \cup {[from |-> n, to |-> m, type |-> "vote", term |-> currentTerm'[n]] : m \in Nodes \ {n}}
    /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, leadTransferee, 
                   electionElapsed, heartbeatElapsed, randomizedElectionTimeout, 
                   msgsAfterAppend, isLearner, pendingConfIndex, uncommittedSize>>

poll(n, from, msgType, granted) ==
    /\ votes' = [votes EXCEPT ![n][from] = granted]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, state, leaderId, 
                   nextIndex, matchIndex, leadTransferee, electionElapsed, 
                   heartbeatElapsed, randomizedElectionTimeout, msgs, 
                   msgsAfterAppend, isLearner, pendingConfIndex, uncommittedSize>>

Step(n, m) ==
    /\ \/ /\ m.type = "hup"
          /\ hup(n, "election")
       \/ /\ m.type = "vote"
          /\ \/ /\ Len(log[n]) >= Len(log[m.from])
                /\ votedFor' = [votedFor EXCEPT ![n] = m.from]
                /\ msgs' = msgs \cup {[from |-> n, to |-> m.from, type |-> "voteResp", term |-> m.term]}
             \/ /\ Len(log[n]) < Len(log[m.from])
                /\ msgs' = msgs \cup {[from |-> n, to |-> m.from, type |-> "voteResp", term |-> currentTerm[n]]}
                /\ UNCHANGED votedFor
       \/ /\ m.type = "voteResp"
          /\ poll(n, m.from, m.type, TRUE)
       \/ /\ m.type = "app"
          /\ handleAppendEntries(n, m)
       \/ /\ m.type = "heartbeat"
          /\ handleHeartbeat(n, m)
    /\ UNCHANGED <<log, commitIndex, state, leaderId, nextIndex, matchIndex, 
                   leadTransferee, electionElapsed, heartbeatElapsed, 
                   randomizedElectionTimeout, msgsAfterAppend, isLearner, 
                   pendingConfIndex, uncommittedSize>>

stepLeader(n, m) ==
    /\ state[n] = "leader"
    /\ \/ /\ m.type = "beat"
          /\ bcastHeartbeat(n)
       \/ /\ m.type = "prop"
          /\ appendEntry(n, m.entries)
       \/ /\ m.type = "appResp"
          /\ handleAppendResponse(n, m)
    /\ UNCHANGED <<currentTerm, votedFor, commitIndex, state, leaderId, 
                   electionElapsed, heartbeatElapsed, randomizedElectionTimeout, 
                   votes, isLearner, pendingConfIndex, uncommittedSize>>

stepCandidate(n, m) ==
    /\ state[n] \in {"candidate", "precandidate"}
    /\ \/ /\ m.type = "voteResp"
          /\ poll(n, m.from, m.type, ~m.reject)
       \/ /\ m.type = "app"
          /\ becomeFollower(n, m.term, m.from)
    /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, leadTransferee, 
                   electionElapsed, heartbeatElapsed, randomizedElectionTimeout, 
                   msgs, msgsAfterAppend, isLearner, pendingConfIndex, uncommittedSize>>

stepFollower(n, m) ==
    /\ state[n] = "follower"
    /\ \/ /\ m.type = "prop"
          /\ leaderId[n] # 0
          /\ msgs' = msgs \cup {[from |-> n, to |-> leaderId[n], type |-> "prop", term |-> currentTerm[n]]}
       \/ /\ m.type = "app"
          /\ handleAppendEntries(n, m)
       \/ /\ m.type = "heartbeat"
          /\ handleHeartbeat(n, m)
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, state, leaderId, 
                   nextIndex, matchIndex, leadTransferee, electionElapsed, 
                   heartbeatElapsed, randomizedElectionTimeout, votes, 
                   msgsAfterAppend, isLearner, pendingConfIndex, uncommittedSize>>

handleAppendEntries(n, m) ==
    /\ electionElapsed' = [electionElapsed EXCEPT ![n] = 0]
    /\ leaderId' = [leaderId EXCEPT ![n] = m.from]
    /\ \/ /\ Len(log[n]) >= m.prevIndex
          /\ log' = [log EXCEPT ![n] = SubSeq(log[n], 1, m.prevIndex) \o m.entries]
          /\ msgs' = msgs \cup {[from |-> n, to |-> m.from, type |-> "appResp", term |-> currentTerm[n]]}
       \/ /\ Len(log[n]) < m.prevIndex
          /\ msgs' = msgs \cup {[from |-> n, to |-> m.from, type |-> "appResp", term |-> currentTerm[n]]}
          /\ UNCHANGED log
    /\ UNCHANGED <<currentTerm, votedFor, commitIndex, state, nextIndex, matchIndex, 
                   leadTransferee, heartbeatElapsed, randomizedElectionTimeout, 
                   votes, msgsAfterAppend, isLearner, pendingConfIndex, uncommittedSize>>

handleHeartbeat(n, m) ==
    /\ electionElapsed' = [electionElapsed EXCEPT ![n] = 0]
    /\ leaderId' = [leaderId EXCEPT ![n] = m.from]
    /\ commitIndex' = [commitIndex EXCEPT ![n] = m.commit]
    /\ msgs' = msgs \cup {[from |-> n, to |-> m.from, type |-> "heartbeatResp", term |-> currentTerm[n]]}
    /\ UNCHANGED <<currentTerm, votedFor, log, state, nextIndex, matchIndex, 
                   leadTransferee, heartbeatElapsed, randomizedElectionTimeout, 
                   votes, msgsAfterAppend, isLearner, pendingConfIndex, uncommittedSize>>

appendEntry(n, entries) ==
    /\ state[n] = "leader"
    /\ log' = [log EXCEPT ![n] = log[n] \o entries]
    /\ uncommittedSize' = [uncommittedSize EXCEPT ![n] = uncommittedSize[n] + Len(entries)]
    /\ bcastAppend(n)
    /\ UNCHANGED <<currentTerm, votedFor, commitIndex, state, leaderId, 
                   nextIndex, matchIndex, leadTransferee, electionElapsed, 
                   heartbeatElapsed, randomizedElectionTimeout, votes, 
                   msgsAfterAppend, isLearner, pendingConfIndex>>

bcastAppend(n) ==
    /\ state[n] = "leader"
    /\ msgs' = msgs \cup {[from |-> n, to |-> m, type |-> "app", term |-> currentTerm[n]] : m \in Nodes \ {n}}
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, state, leaderId, 
                   nextIndex, matchIndex, leadTransferee, electionElapsed, 
                   heartbeatElapsed, randomizedElectionTimeout, votes, 
                   msgsAfterAppend, isLearner, pendingConfIndex, uncommittedSize>>

bcastHeartbeat(n) ==
    /\ state[n] = "leader"
    /\ msgs' = msgs \cup {[from |-> n, to |-> m, type |-> "heartbeat", term |-> currentTerm[n]] : m \in Nodes \ {n}}
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, state, leaderId, 
                   nextIndex, matchIndex, leadTransferee, electionElapsed, 
                   heartbeatElapsed, randomizedElectionTimeout, votes, 
                   msgsAfterAppend, isLearner, pendingConfIndex, uncommittedSize>>

handleAppendResponse(n, m) ==
    /\ state[n] = "leader"
    /\ \/ /\ ~m.reject
          /\ matchIndex' = [matchIndex EXCEPT ![n][m.from] = m.index]
          /\ nextIndex' = [nextIndex EXCEPT ![n][m.from] = m.index + 1]
       \/ /\ m.reject
          /\ nextIndex' = [nextIndex EXCEPT ![n][m.from] = Max(1, nextIndex[n][m.from] - 1)]
          /\ UNCHANGED matchIndex
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, state, leaderId, 
                   leadTransferee, electionElapsed, heartbeatElapsed, 
                   randomizedElectionTimeout, votes, msgs, msgsAfterAppend, 
                   isLearner, pendingConfIndex, uncommittedSize>>

tickElection(n) ==
    /\ state[n] \in {"follower", "candidate", "precandidate"}
    /\ electionElapsed' = [electionElapsed EXCEPT ![n] = electionElapsed[n] + 1]
    /\ IF electionElapsed'[n] >= randomizedElectionTimeout[n]
       THEN /\ electionElapsed' = [electionElapsed' EXCEPT ![n] = 0]
            /\ hup(n, "election")
       ELSE UNCHANGED <<currentTerm, votedFor, log, commitIndex, state, leaderId, 
                        nextIndex, matchIndex, leadTransferee, heartbeatElapsed, 
                        randomizedElectionTimeout, votes, msgs, msgsAfterAppend, 
                        isLearner, pendingConfIndex, uncommittedSize>>

tickHeartbeat(n) ==
    /\ state[n] = "leader"
    /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![n] = heartbeatElapsed[n] + 1]
    /\ electionElapsed' = [electionElapsed EXCEPT ![n] = electionElapsed[n] + 1]
    /\ IF heartbeatElapsed'[n] >= 5
       THEN /\ heartbeatElapsed' = [heartbeatElapsed' EXCEPT ![n] = 0]
            /\ bcastHeartbeat(n)
       ELSE UNCHANGED <<currentTerm, votedFor, log, commitIndex, state, leaderId, 
                        nextIndex, matchIndex, leadTransferee, randomizedElectionTimeout, 
                        votes, msgs, msgsAfterAppend, isLearner, pendingConfIndex, 
                        uncommittedSize>>

maybeCommit(n) ==
    /\ state[n] = "leader"
    /\ \E newCommit \in Nat :
        /\ newCommit > commitIndex[n]
        /\ newCommit <= Len(log[n])
        /\ Cardinality({m \in Nodes : matchIndex[n][m] >= newCommit}) > Cardinality(Nodes) \div 2
        /\ commitIndex' = [commitIndex EXCEPT ![n] = newCommit]
    /\ UNCHANGED <<currentTerm, votedFor, log, state, leaderId, nextIndex, matchIndex, 
                   leadTransferee, electionElapsed, heartbeatElapsed, 
                   randomizedElectionTimeout, votes, msgs, msgsAfterAppend, 
                   isLearner, pendingConfIndex, uncommittedSize>>

Next ==
    \/ \E n \in Nodes : tickElection(n)
    \/ \E n \in Nodes : tickHeartbeat(n)
    \/ \E n \in Nodes : maybeCommit(n)
    \/ \E n \in Nodes, m \in msgs : Step(n, m)
    \/ \E n \in Nodes, entries \in Seq(Nat) : appendEntry(n, entries)

Spec == Init /\ [][Next]_vars

TypeOK == TypeInvariant

====