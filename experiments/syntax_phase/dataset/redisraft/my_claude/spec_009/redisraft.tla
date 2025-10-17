---- MODULE redisraft ----

EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Servers, MaxTerm, MaxLogLen

VARIABLES
    currentTerm,
    state,
    votedFor,
    log,
    commitIndex,
    nextIndex,
    matchIndex,
    votesReceived,
    leaderVars,
    messages,
    electionTimeout,
    heartbeatTimeout

serverVars == <<currentTerm, state, votedFor>>
logVars == <<log, commitIndex>>
candidateVars == <<votesReceived>>
leaderVars == <<nextIndex, matchIndex>>
timeoutVars == <<electionTimeout, heartbeatTimeout>>

vars == <<serverVars, logVars, candidateVars, leaderVars, messages, timeoutVars>>

States == {"Follower", "PreCandidate", "Candidate", "Leader"}

Message ==
    [type : {"RequestVote"}, term : Nat, candidateId : Servers, 
     lastLogIndex : Nat, lastLogTerm : Nat, preVote : BOOLEAN] \cup
    [type : {"RequestVoteResponse"}, term : Nat, voteGranted : BOOLEAN, 
     preVote : BOOLEAN, from : Servers] \cup
    [type : {"AppendEntries"}, term : Nat, leaderId : Servers,
     prevLogIndex : Nat, prevLogTerm : Nat, entries : Seq(Nat),
     leaderCommit : Nat] \cup
    [type : {"AppendEntriesResponse"}, term : Nat, success : BOOLEAN,
     matchIndex : Nat, from : Servers]

Init ==
    /\ currentTerm = [i \in Servers |-> 0]
    /\ state = [i \in Servers |-> "Follower"]
    /\ votedFor = [i \in Servers |-> Nil]
    /\ log = [i \in Servers |-> <<>>]
    /\ commitIndex = [i \in Servers |-> 0]
    /\ nextIndex = [i \in Servers |-> [j \in Servers |-> 1]]
    /\ matchIndex = [i \in Servers |-> [j \in Servers |-> 0]]
    /\ votesReceived = [i \in Servers |-> {}]
    /\ messages = {}
    /\ electionTimeout = [i \in Servers |-> TRUE]
    /\ heartbeatTimeout = [i \in Servers |-> FALSE]

LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)]

Send(m) == messages' = messages \cup {m}

Reply(response, request) == Send(response)

Discard(m) == messages' = messages \ {m}

UpdateTerm(i, term) ==
    /\ currentTerm' = [currentTerm EXCEPT ![i] = term]
    /\ state' = [state EXCEPT ![i] = "Follower"]
    /\ votedFor' = [votedFor EXCEPT ![i] = Nil]

BecomeFollower(i, term) ==
    /\ currentTerm' = [currentTerm EXCEPT ![i] = term]
    /\ state' = [state EXCEPT ![i] = "Follower"]
    /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
    /\ electionTimeout' = [electionTimeout EXCEPT ![i] = TRUE]

BecomePreCandidate(i) ==
    /\ state[i] = "Follower"
    /\ electionTimeout[i] = TRUE
    /\ state' = [state EXCEPT ![i] = "PreCandidate"]
    /\ votesReceived' = [votesReceived EXCEPT ![i] = {i}]
    /\ electionTimeout' = [electionTimeout EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<currentTerm, votedFor>>

BecomeCandidate(i) ==
    /\ state[i] \in {"Follower", "PreCandidate"}
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
    /\ state' = [state EXCEPT ![i] = "Candidate"]
    /\ votedFor' = [votedFor EXCEPT ![i] = i]
    /\ votesReceived' = [votesReceived EXCEPT ![i] = {i}]
    /\ electionTimeout' = [electionTimeout EXCEPT ![i] = FALSE]

BecomeLeader(i) ==
    /\ state[i] \in {"Candidate", "PreCandidate"}
    /\ Cardinality(votesReceived[i]) * 2 > Cardinality(Servers)
    /\ state' = [state EXCEPT ![i] = "Leader"]
    /\ nextIndex' = [nextIndex EXCEPT ![i] = [j \in Servers |-> Len(log[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in Servers |-> 0]]
    /\ heartbeatTimeout' = [heartbeatTimeout EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<currentTerm, votedFor, votesReceived>>

ElectionTimeout(i) ==
    /\ state[i] = "Follower"
    /\ electionTimeout[i] = TRUE
    /\ BecomePreCandidate(i)
    /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, messages>>

RequestVote(i, j) ==
    /\ state[i] \in {"PreCandidate", "Candidate"}
    /\ i # j
    /\ LET preVote == state[i] = "PreCandidate"
           term == IF preVote THEN currentTerm[i] + 1 ELSE currentTerm[i]
       IN Send([type |-> "RequestVote",
                term |-> term,
                candidateId |-> i,
                lastLogIndex |-> Len(log[i]),
                lastLogTerm |-> LastTerm(log[i]),
                preVote |-> preVote])
    /\ UNCHANGED <<serverVars, logVars, candidateVars, leaderVars, timeoutVars>>

HandleRequestVote(i, j, m) ==
    LET logOk == \/ m.lastLogTerm > LastTerm(log[i])
                 \/ /\ m.lastLogTerm = LastTerm(log[i])
                    /\ m.lastLogIndex >= Len(log[i])
        grant == /\ m.term >= currentTerm[i]
                 /\ logOk
                 /\ \/ votedFor[i] = Nil
                    \/ votedFor[i] = m.candidateId
                    \/ m.preVote
    IN /\ m.term <= currentTerm[i] + 1
       /\ \/ /\ m.term = currentTerm[i]
             /\ \/ /\ grant
                   /\ votedFor' = [votedFor EXCEPT ![i] = m.candidateId]
                \/ /\ ~grant
                   /\ UNCHANGED votedFor
             /\ UNCHANGED <<currentTerm, state>>
          \/ /\ m.term > currentTerm[i]
             /\ UpdateTerm(i, m.term)
             /\ votedFor' = [votedFor EXCEPT ![i] = IF grant THEN m.candidateId ELSE Nil]
       /\ Reply([type |-> "RequestVoteResponse",
                 term |-> currentTerm'[i],
                 voteGranted |-> grant,
                 preVote |-> m.preVote,
                 from |-> i], m)
       /\ UNCHANGED <<log, commitIndex, candidateVars, leaderVars, timeoutVars>>

HandleRequestVoteResponse(i, j, m) ==
    /\ m.term = currentTerm[i]
    /\ \/ /\ m.term > currentTerm[i]
          /\ UpdateTerm(i, m.term)
          /\ UNCHANGED <<votesReceived, log, commitIndex, leaderVars, timeoutVars>>
       \/ /\ m.term = currentTerm[i]
          /\ \/ /\ state[i] = "PreCandidate"
                /\ m.preVote
                /\ m.voteGranted
                /\ votesReceived' = [votesReceived EXCEPT ![i] = votesReceived[i] \cup {j}]
                /\ \/ /\ Cardinality(votesReceived'[i]) * 2 > Cardinality(Servers)
                      /\ BecomeCandidate(i)
                   \/ /\ Cardinality(votesReceived'[i]) * 2 <= Cardinality(Servers)
                      /\ UNCHANGED <<currentTerm, state, votedFor, timeoutVars>>
             \/ /\ state[i] = "Candidate"
                /\ ~m.preVote
                /\ m.voteGranted
                /\ votesReceived' = [votesReceived EXCEPT ![i] = votesReceived[i] \cup {j}]
                /\ \/ /\ Cardinality(votesReceived'[i]) * 2 > Cardinality(Servers)
                      /\ BecomeLeader(i)
                   \/ /\ Cardinality(votesReceived'[i]) * 2 <= Cardinality(Servers)
                      /\ UNCHANGED <<currentTerm, state, votedFor, nextIndex, matchIndex, timeoutVars>>
             \/ /\ ~(state[i] = "PreCandidate" /\ m.preVote /\ m.voteGranted)
                /\ ~(state[i] = "Candidate" /\ ~m.preVote /\ m.voteGranted)
                /\ UNCHANGED <<serverVars, votesReceived, leaderVars, timeoutVars>>
          /\ UNCHANGED <<log, commitIndex>>

AppendEntries(i, j) ==
    /\ state[i] = "Leader"
    /\ i # j
    /\ LET prevLogIndex == nextIndex[i][j] - 1
           prevLogTerm == IF prevLogIndex > 0 THEN log[i][prevLogIndex] ELSE 0
           entries == SubSeq(log[i], nextIndex[i][j], Len(log[i]))
       IN Send([type |-> "AppendEntries",
                term |-> currentTerm[i],
                leaderId |-> i,
                prevLogIndex |-> prevLogIndex,
                prevLogTerm |-> prevLogTerm,
                entries |-> entries,
                leaderCommit |-> commitIndex[i]])
    /\ UNCHANGED <<serverVars, logVars, candidateVars, leaderVars, timeoutVars>>

HandleAppendEntries(i, j, m) ==
    LET logOk == \/ m.prevLogIndex = 0
                 \/ /\ m.prevLogIndex > 0
                    /\ m.prevLogIndex <= Len(log[i])
                    /\ log[i][m.prevLogIndex] = m.prevLogTerm
    IN /\ \/ /\ m.term > currentTerm[i]
             /\ UpdateTerm(i, m.term)
          \/ /\ m.term <= currentTerm[i]
             /\ UNCHANGED <<currentTerm, state, votedFor>>
       /\ \/ /\ m.term < currentTerm[i]
             /\ Reply([type |-> "AppendEntriesResponse",
                       term |-> currentTerm[i],
                       success |-> FALSE,
                       matchIndex |-> 0,
                       from |-> i], m)
             /\ UNCHANGED <<log, commitIndex>>
          \/ /\ m.term >= currentTerm[i]
             /\ \/ /\ ~logOk
                   /\ Reply([type |-> "AppendEntriesResponse",
                             term |-> currentTerm[i],
                             success |-> FALSE,
                             matchIndex |-> 0,
                             from |-> i], m)
                   /\ UNCHANGED <<log, commitIndex>>
                \/ /\ logOk
                   /\ LET index == m.prevLogIndex + 1
                          newLog == SubSeq(log[i], 1, m.prevLogIndex) \o m.entries
                      IN /\ log' = [log EXCEPT ![i] = newLog]
                         /\ commitIndex' = [commitIndex EXCEPT ![i] = 
                                           IF m.leaderCommit > commitIndex[i]
                                           THEN Min({m.leaderCommit, Len(newLog)})
                                           ELSE commitIndex[i]]
                         /\ Reply([type |-> "AppendEntriesResponse",
                                   term |-> currentTerm[i],
                                   success |-> TRUE,
                                   matchIndex |-> Len(newLog),
                                   from |-> i], m)
       /\ electionTimeout' = [electionTimeout EXCEPT ![i] = FALSE]
       /\ UNCHANGED <<candidateVars, leaderVars, heartbeatTimeout>>

HandleAppendEntriesResponse(i, j, m) ==
    /\ state[i] = "Leader"
    /\ \/ /\ m.term > currentTerm[i]
          /\ UpdateTerm(i, m.term)
          /\ UNCHANGED <<log, commitIndex, candidateVars, leaderVars, timeoutVars>>
       \/ /\ m.term = currentTerm[i]
          /\ \/ /\ m.success
                /\ nextIndex' = [nextIndex EXCEPT ![i][j] = m.matchIndex + 1]
                /\ matchIndex' = [matchIndex EXCEPT ![i][j] = m.matchIndex]
             \/ /\ ~m.success
                /\ nextIndex' = [nextIndex EXCEPT ![i][j] = Max({nextIndex[i][j] - 1, 1})]
                /\ UNCHANGED matchIndex
          /\ UNCHANGED <<serverVars, log, commitIndex, candidateVars, timeoutVars>>

ClientRequest(i, v) ==
    /\ state[i] = "Leader"
    /\ Len(log[i]) < MaxLogLen
    /\ log' = [log EXCEPT ![i] = Append(log[i], currentTerm[i])]
    /\ UNCHANGED <<serverVars, commitIndex, candidateVars, leaderVars, messages, timeoutVars>>

AdvanceCommitIndex(i) ==
    /\ state[i] = "Leader"
    /\ LET agreementSet == {j \in Servers : matchIndex[i][j] >= commitIndex[i] + 1}
       IN /\ Cardinality(agreementSet) * 2 > Cardinality(Servers)
          /\ commitIndex[i] + 1 <= Len(log[i])
          /\ log[i][commitIndex[i] + 1] = currentTerm[i]
          /\ commitIndex' = [commitIndex EXCEPT ![i] = commitIndex[i] + 1]
    /\ UNCHANGED <<serverVars, log, candidateVars, leaderVars, messages, timeoutVars>>

Timeout(i) ==
    /\ \/ /\ state[i] = "Follower"
          /\ electionTimeout[i] = TRUE
          /\ BecomePreCandidate(i)
       \/ /\ state[i] = "Leader"
          /\ heartbeatTimeout[i] = TRUE
          /\ heartbeatTimeout' = [heartbeatTimeout EXCEPT ![i] = FALSE]
          /\ UNCHANGED <<serverVars, candidateVars, leaderVars>>
    /\ UNCHANGED <<log, commitIndex, messages>>

Receive(m) ==
    LET i == CHOOSE j \in Servers : TRUE
        j == CHOOSE j \in Servers : j # i
    IN \/ /\ m.type = "RequestVote"
          /\ HandleRequestVote(i, j, m)
       \/ /\ m.type = "RequestVoteResponse"
          /\ HandleRequestVoteResponse(i, j, m)
       \/ /\ m.type = "AppendEntries"
          /\ HandleAppendEntries(i, j, m)
       \/ /\ m.type = "AppendEntriesResponse"
          /\ HandleAppendEntriesResponse(i, j, m)

Next ==
    \/ \E i \in Servers : ElectionTimeout(i)
    \/ \E i, j \in Servers : RequestVote(i, j)
    \/ \E i, j \in Servers : AppendEntries(i, j)
    \/ \E i \in Servers, v \in Nat : ClientRequest(i, v)
    \/ \E i \in Servers : AdvanceCommitIndex(i)
    \/ \E i \in Servers : Timeout(i)
    \/ \E m \in messages : /\ Receive(m)
                           /\ Discard(m)

Spec == Init /\ [][Next]_vars

====