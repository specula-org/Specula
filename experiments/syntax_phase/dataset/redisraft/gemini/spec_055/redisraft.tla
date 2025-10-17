---- MODULE redisraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANT Nodes, DefaultValue

ASSUME IsFiniteSet(Nodes) /\ Cardinality(Nodes) >= 1

NodeStates == {"Follower", "PreCandidate", "Candidate", "Leader"}
MessageTypes == { "RequestVoteReq", "RequestVoteResp",
                  "AppendEntriesReq", "AppendEntriesResp",
                  "SnapshotReq", "SnapshotResp" }
EntryTypes == { "Normal", "AddNode", "RemoveNode", "NoOp" }
None == "None"

VARIABLES
    state,
    currentTerm,
    votedFor,
    log,
    commitIndex,
    lastApplied,
    leaderId,
    votesGranted,
    nextIndex,
    matchIndex,
    snapshotLastIndex,
    snapshotLastTerm,
    messages

vars == <<state, currentTerm, votedFor, log, commitIndex, lastApplied, leaderId, votesGranted, nextIndex, matchIndex, snapshotLastIndex, snapshotLastTerm, messages>>

Majority == (Cardinality(Nodes) \div 2) + 1

LastLogIndex(n) ==
    IF Len(log[n]) = 0 THEN snapshotLastIndex[n] ELSE snapshotLastIndex[n] + Len(log[n])

LastLogTerm(n) ==
    IF Len(log[n]) = 0 THEN snapshotLastTerm[n]
    ELSE log[n][Len(log[n])]["term"]

GetEntry(n, idx) ==
    IF idx > snapshotLastIndex[n] /\ idx <= LastLogIndex(n)
    THEN log[n][idx - snapshotLastIndex[n]]
    ELSE [term |-> 0, value |-> None, type |-> None]

GetTerm(n, idx) ==
    IF idx = 0 THEN 0
    ELSE IF idx = snapshotLastIndex[n] THEN snapshotLastTerm[n]
    ELSE GetEntry(n, idx)["term"]

Quorum(votes) == Cardinality(votes) >= Majority

BecomeFollower(n, term) ==
    /\ state' = [state EXCEPT ![n] = "Follower"]
    /\ currentTerm' = [currentTerm EXCEPT ![n] = term]
    /\ votedFor' = [votedFor EXCEPT ![n] = None]
    /\ leaderId' = [leaderId EXCEPT ![n] = None]
    /\ UNCHANGED <<log, commitIndex, lastApplied, votesGranted, nextIndex, matchIndex, snapshotLastIndex, snapshotLastTerm, messages>>

BecomePreCandidate(n) ==
    /\ state' = [state EXCEPT ![n] = "PreCandidate"]
    /\ votesGranted' = [votesGranted EXCEPT ![n] = {}]
    /\ messages' = messages \cup
        { [ type |-> "RequestVoteReq",
            src |-> n,
            dest |-> peer,
            term |-> currentTerm[n] + 1,
            lastLogIndex |-> LastLogIndex(n),
            lastLogTerm |-> LastLogTerm(n),
            prevote |-> TRUE
          ] : peer \in Nodes \ {n} }
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied, leaderId, nextIndex, matchIndex, snapshotLastIndex, snapshotLastTerm>>

BecomeCandidate(n) ==
    /\ state' = [state EXCEPT ![n] = "Candidate"]
    /\ currentTerm' = [currentTerm EXCEPT ![n] = currentTerm[n] + 1]
    /\ votedFor' = [votedFor EXCEPT ![n] = n]
    /\ votesGranted' = [votesGranted EXCEPT ![n] = {n}]
    /\ leaderId' = [leaderId EXCEPT ![n] = None]
    /\ messages' = messages \cup
        { [ type |-> "RequestVoteReq",
            src |-> n,
            dest |-> peer,
            term |-> currentTerm[n] + 1,
            lastLogIndex |-> LastLogIndex(n),
            lastLogTerm |-> LastLogTerm(n),
            prevote |-> FALSE
          ] : peer \in Nodes \ {n} }
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, snapshotLastIndex, snapshotLastTerm>>

BecomeLeader(n) ==
    /\ state' = [state EXCEPT ![n] = "Leader"]
    /\ leaderId' = [leaderId EXCEPT ![n] = n]
    /\ nextIndex' = [nextIndex EXCEPT ![n] = [peer \in Nodes |-> LastLogIndex(n) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![n] = [peer \in Nodes |-> 0]]
    /\ log' = [log EXCEPT ![n] = Append(log[n], [term |-> currentTerm[n], value |-> None, type |-> "NoOp"])]
    /\ UNCHANGED <<currentTerm, votedFor, commitIndex, lastApplied, votesGranted, snapshotLastIndex, snapshotLastTerm, messages>>

ElectionStart(n) == BecomePreCandidate(n)
ElectionTimeout(n) ==
    /\ state[n] \in {"Follower", "Candidate", "PreCandidate"}
    /\ ElectionStart(n)
PeriodicElectionTimeout(n) == ElectionTimeout(n)

HandleRequestVote(m) ==
    LET n == m["dest"]
        cand == m["src"]
        grantVote ==
            \/ m["lastLogTerm"] > LastLogTerm(n)
            \/ (m["lastLogTerm"] = LastLogTerm(n) /\ m["lastLogIndex"] >= LastLogIndex(n))
    IN
    /\ m["type"] = "RequestVoteReq"
    /\ IF m["term"] < currentTerm[n]
       THEN /\ messages' = (messages \ {m}) \cup
                { [ type |-> "RequestVoteResp", src |-> n, dest |-> cand, term |-> currentTerm[n], voteGranted |-> FALSE, prevote |-> m["prevote"] ] }
            /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, leaderId, votesGranted, nextIndex, matchIndex, snapshotLastIndex, snapshotLastTerm>>
       ELSE /\ IF m["term"] > currentTerm[n] /\ \lnot m["prevote"]
              THEN /\ state' = [state EXCEPT ![n] = "Follower"]
                   /\ currentTerm' = [currentTerm EXCEPT ![n] = m["term"]]
                   /\ votedFor' = [votedFor EXCEPT ![n] = IF grantVote THEN cand ELSE None]
              ELSE /\ UNCHANGED <<state, currentTerm>>
                   /\ IF (votedFor[n] = None \/ votedFor[n] = cand) /\ grantVote /\ \lnot m["prevote"]
                      THEN votedFor' = [votedFor EXCEPT ![n] = cand]
                      ELSE UNCHANGED votedFor
            /\ messages' = (messages \ {m}) \cup
                { [ type |-> "RequestVoteResp", src |-> n, dest |-> cand, term |-> currentTerm'[n], voteGranted |-> grantVote, prevote |-> m["prevote"] ] }
            /\ UNCHANGED <<log, commitIndex, lastApplied, leaderId, votesGranted, nextIndex, matchIndex, snapshotLastIndex, snapshotLastTerm>>

HandleRequestVoteResponse(m) ==
    LET n == m["dest"]
    IN
    /\ m["type"] = "RequestVoteResp"
    /\ IF m["term"] > currentTerm[n]
       THEN BecomeFollower(n, m["term"])
       ELSE IF m["term"] = currentTerm[n] \/ (m["prevote"] /\ m["term"] = currentTerm[n] + 1)
            THEN /\ IF m["voteGranted"]
                   THEN /\ votesGranted' = [votesGranted EXCEPT ![n] = votesGranted[n] \cup {m["src"]}]
                        /\ IF state[n] = "PreCandidate" /\ Quorum(votesGranted'[n])
                           THEN BecomeCandidate(n)
                           ELSE IF state[n] = "Candidate" /\ Quorum(votesGranted'[n])
                                THEN BecomeLeader(n)
                                ELSE UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, leaderId, nextIndex, matchIndex, snapshotLastIndex, snapshotLastTerm>>
                   ELSE UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, leaderId, votesGranted, nextIndex, matchIndex, snapshotLastIndex, snapshotLastTerm>>
                /\ messages' = messages \ {m}
            ELSE UNCHANGED vars

SendAppendEntries(leader, follower) ==
    /\ state[leader] = "Leader"
    /\ follower \in Nodes \ {leader}
    /\ IF nextIndex[leader][follower] <= snapshotLastIndex[leader]
       THEN /\ messages' = messages \cup
                { [ type |-> "SnapshotReq", src |-> leader, dest |-> follower, term |-> currentTerm[leader],
                    leaderId |-> leader, lastIncludedIndex |-> snapshotLastIndex[leader], lastIncludedTerm |-> snapshotLastTerm[leader] ] }
            /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, leaderId, votesGranted, nextIndex, matchIndex, snapshotLastIndex, snapshotLastTerm>>
       ELSE /\ LET prevLogIndex == nextIndex[leader][follower] - 1
                  entriesToSend == SubSeq(log[leader], (prevLogIndex - snapshotLastIndex[leader]) + 1, Len(log[leader]))
            IN
            /\ messages' = messages \cup
                { [ type |-> "AppendEntriesReq", src |-> leader, dest |-> follower, term |-> currentTerm[leader],
                    leaderId |-> leader, prevLogIndex |-> prevLogIndex, prevLogTerm |-> GetTerm(leader, prevLogIndex),
                    entries |-> entriesToSend, leaderCommit |-> commitIndex[leader] ] }
            /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, leaderId, votesGranted, nextIndex, matchIndex, snapshotLastIndex, snapshotLastTerm>>

PeriodicHeartbeat(leader) == \E follower \in Nodes \ {leader} : SendAppendEntries(leader, follower)

HandleAppendEntries(m) ==
    LET n == m["dest"]
    IN
    /\ m["type"] = "AppendEntriesReq"
    /\ IF m["term"] < currentTerm[n]
       THEN /\ messages' = (messages \ {m}) \cup { [ type |-> "AppendEntriesResp", src |-> n, dest |-> m["src"], term |-> currentTerm[n], success |-> FALSE, matchIndex |-> 0 ] }
            /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, leaderId, votesGranted, nextIndex, matchIndex, snapshotLastIndex, snapshotLastTerm>>
       ELSE LET logOK == m["prevLogIndex"] = 0 \/ (m["prevLogIndex"] <= LastLogIndex(n) /\ GetTerm(n, m["prevLogIndex"]) = m["prevLogTerm"])
            IN
            /\ state' = [state EXCEPT ![n] = "Follower"]
            /\ currentTerm' = [currentTerm EXCEPT ![n] = m["term"]]
            /\ leaderId' = [leaderId EXCEPT ![n] = m["leaderId"]]
            /\ IF \lnot logOK
               THEN /\ messages' = (messages \ {m}) \cup { [ type |-> "AppendEntriesResp", src |-> n, dest |-> m["src"], term |-> currentTerm'[n], success |-> FALSE, matchIndex |-> commitIndex[n] ] }
                    /\ UNCHANGED <<votedFor, log, commitIndex, lastApplied, votesGranted, nextIndex, matchIndex, snapshotLastIndex, snapshotLastTerm>>
               ELSE LET newLogEntries ==
                            LET existingEntryTerm(i) == GetTerm(n, m["prevLogIndex"] + i)
                                firstConflict == { i \in 1..Len(m["entries"]) : existingEntryTerm(i) /= 0 /\ existingEntryTerm(i) /= m["entries"][i]["term"] }
                            IN
                            IF firstConflict = {}
                            THEN LET currentLen = LastLogIndex(n) - m["prevLogIndex"]
                                 IN SubSeq(m["entries"], currentLen + 1, Len(m["entries"]))
                            ELSE SubSeq(m["entries"], Min(firstConflict), Len(m["entries"]))
                    IN
                    /\ log' = [log EXCEPT ![n] = AppendSeq(SubSeq(log[n], 1, m["prevLogIndex"] - snapshotLastIndex[n]), newLogEntries)]
                    /\ IF m["leaderCommit"] > commitIndex[n]
                       THEN commitIndex' = [commitIndex EXCEPT ![n] = Min({m["leaderCommit"], m["prevLogIndex"] + Len(m["entries"])})]
                       ELSE UNCHANGED commitIndex
                    /\ messages' = (messages \ {m}) \cup { [ type |-> "AppendEntriesResp", src |-> n, dest |-> m["src"], term |-> currentTerm'[n], success |-> TRUE, matchIndex |-> m["prevLogIndex"] + Len(m["entries"]) ] }
                    /\ UNCHANGED <<votedFor, lastApplied, votesGranted, nextIndex, matchIndex, snapshotLastIndex, snapshotLastTerm>>

HandleAppendEntriesResponse(m) ==
    LET leader == m["dest"]
        follower == m["src"]
    IN
    /\ m["type"] = "AppendEntriesResp"
    /\ state[leader] = "Leader"
    /\ IF m["term"] > currentTerm[leader]
       THEN BecomeFollower(leader, m["term"])
       ELSE IF m["term"] = currentTerm[leader]
            THEN /\ IF m["success"]
                   THEN /\ nextIndex' = [nextIndex EXCEPT ![leader][follower] = m["matchIndex"] + 1]
                        /\ matchIndex' = [matchIndex EXCEPT ![leader][follower] = m["matchIndex"]]
                        /\ (LET newCommitIndex ==
                                LET indices = { i \in (commitIndex[leader]+1)..LastLogIndex(leader) :
                                                /\ GetTerm(leader, i) = currentTerm[leader]
                                                /\ Quorum({p \in Nodes : [matchIndex EXCEPT ![leader][follower] = m["matchIndex"]][leader][p] >= i} \cup {leader})
                                              }
                                IN IF indices = {} THEN commitIndex[leader] ELSE Max(indices)
                           IN commitIndex' = [commitIndex EXCEPT ![leader] = newCommitIndex])
                   ELSE /\ nextIndex' = [nextIndex EXCEPT ![leader][follower] = Max({1, nextIndex[leader][follower] - 1})]
                        /\ UNCHANGED <<matchIndex, commitIndex>>
                /\ messages' = messages \ {m}
                /\ UNCHANGED <<state, currentTerm, votedFor, log, lastApplied, leaderId, votesGranted, snapshotLastIndex, snapshotLastTerm>>
            ELSE UNCHANGED vars

LogAppend(n, val, type) ==
    /\ state[n] = "Leader"
    /\ log' = [log EXCEPT ![n] = Append(log[n], [term |-> currentTerm[n], value |-> val, type |-> type])]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, leaderId, votesGranted, nextIndex, matchIndex, snapshotLastIndex, snapshotLastTerm, messages>>

LogCommit(n) ==
    /\ commitIndex[n] > lastApplied[n]
    /\ lastApplied' = [lastApplied EXCEPT ![n] = lastApplied[n] + 1]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leaderId, votesGranted, nextIndex, matchIndex, snapshotLastIndex, snapshotLastTerm, messages>>

AddNode(leader, newNode) == LogAppend(leader, newNode, "AddNode")
RemoveNode(leader, oldNode) == LogAppend(leader, oldNode, "RemoveNode")
ApplyConfigChange(n) == LogCommit(n)

SnapshotBegin(n, lastIncludedIndex) ==
    /\ lastIncludedIndex > snapshotLastIndex[n]
    /\ lastIncludedIndex <= commitIndex[n]
    /\ LET lastIncludedTerm == GetTerm(n, lastIncludedIndex)
           newLog == SubSeq(log[n], (lastIncludedIndex - snapshotLastIndex[n]) + 1, Len(log[n]))
    IN
    /\ snapshotLastIndex' = [snapshotLastIndex EXCEPT ![n] = lastIncludedIndex]
    /\ snapshotLastTerm' = [snapshotLastTerm EXCEPT ![n] = lastIncludedTerm]
    /\ log' = [log EXCEPT ![n] = newLog]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, leaderId, votesGranted, nextIndex, matchIndex, messages>>
SnapshotEnd(n) == TRUE

HandleSnapshot(m) ==
    LET n == m["dest"]
    IN
    /\ m["type"] = "SnapshotReq"
    /\ IF m["term"] < currentTerm[n]
       THEN UNCHANGED vars
       ELSE /\ IF m["term"] > currentTerm[n]
              THEN currentTerm' = [currentTerm EXCEPT ![n] = m["term"]]
              ELSE UNCHANGED currentTerm
           /\ state' = [state EXCEPT ![n] = "Follower"]
           /\ leaderId' = [leaderId EXCEPT ![n] = m["leaderId"]]
           /\ IF m["lastIncludedIndex"] > commitIndex[n]
              THEN /\ snapshotLastIndex' = [snapshotLastIndex EXCEPT ![n] = m["lastIncludedIndex"]]
                   /\ snapshotLastTerm' = [snapshotLastTerm EXCEPT ![n] = m["lastIncludedTerm"]]
                   /\ commitIndex' = [commitIndex EXCEPT ![n] = m["lastIncludedIndex"]]
                   /\ lastApplied' = [lastApplied EXCEPT ![n] = m["lastIncludedIndex"]]
                   /\ log' = [log EXCEPT ![n] = <<>>]
              ELSE UNCHANGED <<snapshotLastIndex, snapshotLastTerm, commitIndex, lastApplied, log>>
           /\ messages' = (messages \ {m}) \cup { [ type |-> "SnapshotResp", src |-> n, dest |-> m["src"], term |-> currentTerm'[n] ] }
           /\ UNCHANGED <<votedFor, votesGranted, nextIndex, matchIndex>>

HandleSnapshotResponse(m) ==
    LET leader == m["dest"]
    IN
    /\ m["type"] = "SnapshotResp"
    /\ state[leader] = "Leader"
    /\ IF m["term"] > currentTerm[leader]
       THEN BecomeFollower(leader, m["term"])
       ELSE IF m["term"] = currentTerm[leader]
            THEN /\ nextIndex' = [nextIndex EXCEPT ![leader][m["src"]] = snapshotLastIndex[leader] + 1]
                 /\ matchIndex' = [matchIndex EXCEPT ![leader][m["src"]] = snapshotLastIndex[leader]]
                 /\ messages' = messages \ {m}
                 /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, leaderId, votesGranted, snapshotLastIndex, snapshotLastTerm>>
            ELSE UNCHANGED vars

Init ==
    /\ state = [n \in Nodes |-> "Follower"]
    /\ currentTerm = [n \in Nodes |-> 0]
    /\ votedFor = [n \in Nodes |-> None]
    /\ log = [n \in Nodes |-> <<>>]
    /\ commitIndex = [n \in Nodes |-> 0]
    /\ lastApplied = [n \in Nodes |-> 0]
    /\ leaderId = [n \in Nodes |-> None]
    /\ votesGranted = [n \in Nodes |-> {}]
    /\ nextIndex = [n \in Nodes |-> [m \in Nodes |-> 1]]
    /\ matchIndex = [n \in Nodes |-> [m \in Nodes |-> 0]]
    /\ snapshotLastIndex = [n \in Nodes |-> 0]
    /\ snapshotLastTerm = [n \in Nodes |-> 0]
    /\ messages = {}

Next ==
    \/ \E n \in Nodes : PeriodicElectionTimeout(n)
    \/ \E m \in messages : HandleRequestVote(m)
    \/ \E m \in messages : HandleRequestVoteResponse(m)
    \/ \E leader \in Nodes : PeriodicHeartbeat(leader)
    \/ \E m \in messages : HandleAppendEntries(m)
    \/ \E m \in messages : HandleAppendEntriesResponse(m)
    \/ \E n \in Nodes, val \in {DefaultValue} : LogAppend(n, val, "Normal")
    \/ \E n \in Nodes : LogCommit(n)
    \/ \E leader \in Nodes, newNode \in Nodes : AddNode(leader, newNode)
    \/ \E leader \in Nodes, oldNode \in Nodes : RemoveNode(leader, oldNode)
    \/ \E n \in Nodes, idx \in {i \in 1..LastLogIndex(n) : i > snapshotLastIndex[n]} : SnapshotBegin(n, idx)
    \/ \E m \in messages : HandleSnapshot(m)
    \/ \E m \in messages : HandleSnapshotResponse(m)

Spec == Init /\ [][Next]_vars

====