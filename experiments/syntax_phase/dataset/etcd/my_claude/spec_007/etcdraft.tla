---- MODULE etcdraft ----

EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Nodes, MaxTerm, MaxLogLen

VARIABLES 
    state,
    currentTerm,
    votedFor,
    log,
    commitIndex,
    nextIndex,
    matchIndex,
    votes,
    preVotes,
    electionTimeout,
    heartbeatTimeout,
    messages,
    leader

vars == <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votes, preVotes, electionTimeout, heartbeatTimeout, messages, leader>>

NodeStates == {"Follower", "PreCandidate", "Candidate", "Leader"}

MessageTypes == {"MsgHup", "MsgVote", "MsgVoteResp", "MsgPreVote", "MsgPreVoteResp", "MsgApp", "MsgAppResp", "MsgHeartbeat", "MsgHeartbeatResp", "MsgProp"}

Message == [type: MessageTypes, from: Nodes, to: Nodes, term: Nat, logTerm: Nat, index: Nat, entries: Seq(Nat), commit: Nat, reject: BOOLEAN]

LogEntry == [term: Nat, index: Nat, data: Nat]

TypeOK ==
    /\ state \in [Nodes -> NodeStates]
    /\ currentTerm \in [Nodes -> Nat]
    /\ votedFor \in [Nodes -> Nodes \cup {0}]
    /\ log \in [Nodes -> Seq(LogEntry)]
    /\ commitIndex \in [Nodes -> Nat]
    /\ nextIndex \in [Nodes -> [Nodes -> Nat]]
    /\ matchIndex \in [Nodes -> [Nodes -> Nat]]
    /\ votes \in [Nodes -> SUBSET Nodes]
    /\ preVotes \in [Nodes -> SUBSET Nodes]
    /\ electionTimeout \in [Nodes -> Nat]
    /\ heartbeatTimeout \in [Nodes -> Nat]
    /\ messages \in SUBSET Message
    /\ leader \in [Nodes -> Nodes \cup {0}]

Init ==
    /\ state = [n \in Nodes |-> "Follower"]
    /\ currentTerm = [n \in Nodes |-> 0]
    /\ votedFor = [n \in Nodes |-> 0]
    /\ log = [n \in Nodes |-> <<>>]
    /\ commitIndex = [n \in Nodes |-> 0]
    /\ nextIndex = [n \in Nodes |-> [m \in Nodes |-> 1]]
    /\ matchIndex = [n \in Nodes |-> [m \in Nodes |-> 0]]
    /\ votes = [n \in Nodes |-> {}]
    /\ preVotes = [n \in Nodes |-> {}]
    /\ electionTimeout = [n \in Nodes |-> 1]
    /\ heartbeatTimeout = [n \in Nodes |-> 1]
    /\ messages = {}
    /\ leader = [n \in Nodes |-> 0]

Send(m) == messages' = messages \cup {m}

Discard(m) == messages' = messages \ {m}

Reply(response, request) ==
    messages' = (messages \ {request}) \cup {response}

LastLogIndex(n) == Len(log[n])

LastLogTerm(n) == 
    IF Len(log[n]) = 0 THEN 0 ELSE log[n][Len(log[n])].term

IsUpToDate(n, lastLogTerm, lastLogIndex) ==
    \/ lastLogTerm > LastLogTerm(n)
    \/ /\ lastLogTerm = LastLogTerm(n)
       /\ lastLogIndex >= LastLogIndex(n)

CanVote(n, candidate, term, lastLogTerm, lastLogIndex) ==
    /\ term >= currentTerm[n]
    /\ \/ votedFor[n] = 0
       \/ votedFor[n] = candidate
    /\ IsUpToDate(n, lastLogTerm, lastLogIndex)

ElectionTimeout(n) ==
    /\ state[n] \in {"Follower", "PreCandidate", "Candidate"}
    /\ electionTimeout[n] = 0
    /\ state' = [state EXCEPT ![n] = "PreCandidate"]
    /\ preVotes' = [preVotes EXCEPT ![n] = {n}]
    /\ LET preVoteMsg == [type |-> "MsgPreVote", from |-> n, to |-> n, term |-> currentTerm[n] + 1, logTerm |-> LastLogTerm(n), index |-> LastLogIndex(n), entries |-> <<>>, commit |-> 0, reject |-> FALSE]
       IN messages' = messages \cup {[preVoteMsg EXCEPT !.to = m] : m \in Nodes \ {n}}
    /\ electionTimeout' = [electionTimeout EXCEPT ![n] = 1]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votes, heartbeatTimeout, leader>>

StartElection(n) ==
    /\ state[n] = "PreCandidate"
    /\ Cardinality(preVotes[n]) * 2 > Cardinality(Nodes)
    /\ state' = [state EXCEPT ![n] = "Candidate"]
    /\ currentTerm' = [currentTerm EXCEPT ![n] = currentTerm[n] + 1]
    /\ votedFor' = [votedFor EXCEPT ![n] = n]
    /\ votes' = [votes EXCEPT ![n] = {n}]
    /\ LET voteMsg == [type |-> "MsgVote", from |-> n, to |-> n, term |-> currentTerm[n] + 1, logTerm |-> LastLogTerm(n), index |-> LastLogIndex(n), entries |-> <<>>, commit |-> 0, reject |-> FALSE]
       IN messages' = messages \cup {[voteMsg EXCEPT !.to = m] : m \in Nodes \ {n}}
    /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, preVotes, electionTimeout, heartbeatTimeout, leader>>

BecomeLeader(n) ==
    /\ state[n] = "Candidate"
    /\ Cardinality(votes[n]) * 2 > Cardinality(Nodes)
    /\ state' = [state EXCEPT ![n] = "Leader"]
    /\ leader' = [leader EXCEPT ![n] = n]
    /\ nextIndex' = [nextIndex EXCEPT ![n] = [m \in Nodes |-> LastLogIndex(n) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![n] = [m \in Nodes |-> 0]]
    /\ heartbeatTimeout' = [heartbeatTimeout EXCEPT ![n] = 1]
    /\ LET heartbeatMsg == [type |-> "MsgHeartbeat", from |-> n, to |-> n, term |-> currentTerm[n], logTerm |-> 0, index |-> 0, entries |-> <<>>, commit |-> commitIndex[n], reject |-> FALSE]
       IN messages' = messages \cup {[heartbeatMsg EXCEPT !.to = m] : m \in Nodes \ {n}}
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, votes, preVotes, electionTimeout>>

HandlePreVote(m) ==
    /\ m.type = "MsgPreVote"
    /\ LET n == m.to
           canVote == CanVote(n, m.from, m.term, m.logTerm, m.index)
           response == [type |-> "MsgPreVoteResp", from |-> n, to |-> m.from, term |-> m.term, logTerm |-> 0, index |-> 0, entries |-> <<>>, commit |-> 0, reject |-> ~canVote]
       IN Reply(response, m)
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votes, preVotes, electionTimeout, heartbeatTimeout, leader>>

HandlePreVoteResp(m) ==
    /\ m.type = "MsgPreVoteResp"
    /\ m.term = currentTerm[m.to] + 1
    /\ state[m.to] = "PreCandidate"
    /\ preVotes' = [preVotes EXCEPT ![m.to] = IF m.reject THEN @ ELSE @ \cup {m.from}]
    /\ Discard(m)
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votes, electionTimeout, heartbeatTimeout, leader>>

HandleVote(m) ==
    /\ m.type = "MsgVote"
    /\ LET n == m.to
           canVote == CanVote(n, m.from, m.term, m.logTerm, m.index)
           newTerm == IF m.term > currentTerm[n] THEN m.term ELSE currentTerm[n]
           newVotedFor == IF canVote /\ m.term >= currentTerm[n] THEN m.from ELSE votedFor[n]
           newState == IF m.term > currentTerm[n] THEN "Follower" ELSE state[n]
           response == [type |-> "MsgVoteResp", from |-> n, to |-> m.from, term |-> m.term, logTerm |-> 0, index |-> 0, entries |-> <<>>, commit |-> 0, reject |-> ~canVote]
       IN /\ Reply(response, m)
          /\ currentTerm' = [currentTerm EXCEPT ![n] = newTerm]
          /\ votedFor' = [votedFor EXCEPT ![n] = newVotedFor]
          /\ state' = [state EXCEPT ![n] = newState]
          /\ leader' = [leader EXCEPT ![n] = IF newState = "Follower" THEN 0 ELSE leader[n]]
    /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, votes, preVotes, electionTimeout, heartbeatTimeout>>

HandleVoteResp(m) ==
    /\ m.type = "MsgVoteResp"
    /\ m.term = currentTerm[m.to]
    /\ state[m.to] = "Candidate"
    /\ votes' = [votes EXCEPT ![m.to] = IF m.reject THEN @ ELSE @ \cup {m.from}]
    /\ Discard(m)
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, preVotes, electionTimeout, heartbeatTimeout, leader>>

HandleHeartbeat(m) ==
    /\ m.type = "MsgHeartbeat"
    /\ LET n == m.to
           newTerm == IF m.term > currentTerm[n] THEN m.term ELSE currentTerm[n]
           newState == IF m.term >= currentTerm[n] THEN "Follower" ELSE state[n]
           newLeader == IF m.term >= currentTerm[n] THEN m.from ELSE leader[n]
           newCommitIndex == IF m.term >= currentTerm[n] /\ m.commit > commitIndex[n] THEN m.commit ELSE commitIndex[n]
           response == [type |-> "MsgHeartbeatResp", from |-> n, to |-> m.from, term |-> currentTerm[n], logTerm |-> 0, index |-> 0, entries |-> <<>>, commit |-> 0, reject |-> FALSE]
       IN /\ Reply(response, m)
          /\ currentTerm' = [currentTerm EXCEPT ![n] = newTerm]
          /\ state' = [state EXCEPT ![n] = newState]
          /\ leader' = [leader EXCEPT ![n] = newLeader]
          /\ commitIndex' = [commitIndex EXCEPT ![n] = newCommitIndex]
          /\ electionTimeout' = [electionTimeout EXCEPT ![n] = 1]
    /\ UNCHANGED <<votedFor, log, nextIndex, matchIndex, votes, preVotes, heartbeatTimeout>>

HandleHeartbeatResp(m) ==
    /\ m.type = "MsgHeartbeatResp"
    /\ state[m.to] = "Leader"
    /\ Discard(m)
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votes, preVotes, electionTimeout, heartbeatTimeout, leader>>

SendHeartbeat(n) ==
    /\ state[n] = "Leader"
    /\ heartbeatTimeout[n] = 0
    /\ LET heartbeatMsg == [type |-> "MsgHeartbeat", from |-> n, to |-> n, term |-> currentTerm[n], logTerm |-> 0, index |-> 0, entries |-> <<>>, commit |-> commitIndex[n], reject |-> FALSE]
       IN messages' = messages \cup {[heartbeatMsg EXCEPT !.to = m] : m \in Nodes \ {n}}
    /\ heartbeatTimeout' = [heartbeatTimeout EXCEPT ![n] = 1]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votes, preVotes, electionTimeout, leader>>

HandleAppendEntries(m) ==
    /\ m.type = "MsgApp"
    /\ LET n == m.to
           logOk == \/ m.index = 0
                    \/ /\ m.index <= Len(log[n])
                       /\ log[n][m.index].term = m.logTerm
           newTerm == IF m.term > currentTerm[n] THEN m.term ELSE currentTerm[n]
           newState == IF m.term >= currentTerm[n] THEN "Follower" ELSE state[n]
           newLeader == IF m.term >= currentTerm[n] THEN m.from ELSE leader[n]
           newLog == IF logOk /\ m.term >= currentTerm[n]
                     THEN SubSeq(log[n], 1, m.index) \o m.entries
                     ELSE log[n]
           newCommitIndex == IF logOk /\ m.term >= currentTerm[n] /\ m.commit > commitIndex[n]
                            THEN Min(m.commit, Len(newLog))
                            ELSE commitIndex[n]
           response == [type |-> "MsgAppResp", from |-> n, to |-> m.from, term |-> currentTerm[n], logTerm |-> 0, index |-> IF logOk THEN m.index + Len(m.entries) ELSE 0, entries |-> <<>>, commit |-> 0, reject |-> ~logOk]
       IN /\ Reply(response, m)
          /\ currentTerm' = [currentTerm EXCEPT ![n] = newTerm]
          /\ state' = [state EXCEPT ![n] = newState]
          /\ leader' = [leader EXCEPT ![n] = newLeader]
          /\ log' = [log EXCEPT ![n] = newLog]
          /\ commitIndex' = [commitIndex EXCEPT ![n] = newCommitIndex]
          /\ electionTimeout' = [electionTimeout EXCEPT ![n] = 1]
    /\ UNCHANGED <<votedFor, nextIndex, matchIndex, votes, preVotes, heartbeatTimeout>>

HandleAppendEntriesResp(m) ==
    /\ m.type = "MsgAppResp"
    /\ state[m.to] = "Leader"
    /\ m.term = currentTerm[m.to]
    /\ IF m.reject
       THEN /\ nextIndex' = [nextIndex EXCEPT ![m.to][m.from] = Max(1, nextIndex[m.to][m.from] - 1)]
            /\ UNCHANGED matchIndex
       ELSE /\ nextIndex' = [nextIndex EXCEPT ![m.to][m.from] = m.index + 1]
            /\ matchIndex' = [matchIndex EXCEPT ![m.to][m.from] = m.index]
    /\ Discard(m)
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, votes, preVotes, electionTimeout, heartbeatTimeout, leader>>

ClientRequest(n, data) ==
    /\ state[n] = "Leader"
    /\ Len(log[n]) < MaxLogLen
    /\ LET newEntry == [term |-> currentTerm[n], index |-> Len(log[n]) + 1, data |-> data]
       IN log' = [log EXCEPT ![n] = Append(@, newEntry)]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, nextIndex, matchIndex, votes, preVotes, electionTimeout, heartbeatTimeout, messages, leader>>

ReplicateLog(n) ==
    /\ state[n] = "Leader"
    /\ \E m \in Nodes \ {n} :
        /\ nextIndex[n][m] <= Len(log[n])
        /\ LET prevIndex == nextIndex[n][m] - 1
               prevTerm == IF prevIndex = 0 THEN 0 ELSE log[n][prevIndex].term
               entries == SubSeq(log[n], nextIndex[n][m], Len(log[n]))
               msg == [type |-> "MsgApp", from |-> n, to |-> m, term |-> currentTerm[n], logTerm |-> prevTerm, index |-> prevIndex, entries |-> entries, commit |-> commitIndex[n], reject |-> FALSE]
           IN Send(msg)
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votes, preVotes, electionTimeout, heartbeatTimeout, leader>>

AdvanceCommitIndex(n) ==
    /\ state[n] = "Leader"
    /\ \E index \in (commitIndex[n] + 1)..Len(log[n]) :
        /\ log[n][index].term = currentTerm[n]
        /\ Cardinality({m \in Nodes : matchIndex[n][m] >= index}) * 2 > Cardinality(Nodes)
        /\ commitIndex' = [commitIndex EXCEPT ![n] = index]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, nextIndex, matchIndex, votes, preVotes, electionTimeout, heartbeatTimeout, messages, leader>>

Tick ==
    \E n \in Nodes :
        \/ /\ electionTimeout[n] > 0
           /\ electionTimeout' = [electionTimeout EXCEPT ![n] = @ - 1]
           /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votes, preVotes, heartbeatTimeout, messages, leader>>
        \/ /\ heartbeatTimeout[n] > 0
           /\ heartbeatTimeout' = [heartbeatTimeout EXCEPT ![n] = @ - 1]
           /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votes, preVotes, electionTimeout, messages, leader>>

Next ==
    \/ Tick
    \/ \E n \in Nodes : ElectionTimeout(n)
    \/ \E n \in Nodes : StartElection(n)
    \/ \E n \in Nodes : BecomeLeader(n)
    \/ \E n \in Nodes : SendHeartbeat(n)
    \/ \E n \in Nodes, data \in 1..3 : ClientRequest(n, data)
    \/ \E n \in Nodes : ReplicateLog(n)
    \/ \E n \in Nodes : AdvanceCommitIndex(n)
    \/ \E m \in messages : HandlePreVote(m)
    \/ \E m \in messages : HandlePreVoteResp(m)
    \/ \E m \in messages : HandleVote(m)
    \/ \E m \in messages : HandleVoteResp(m)
    \/ \E m \in messages : HandleHeartbeat(m)
    \/ \E m \in messages : HandleHeartbeatResp(m)
    \/ \E m \in messages : HandleAppendEntries(m)
    \/ \E m \in messages : HandleAppendEntriesResp(m)

Spec == Init /\ [][Next]_vars

====