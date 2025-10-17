---- MODULE redisraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags, Integers

CONSTANTS Nodes, LogValue, Nil
ASSUME IsFiniteSet(Nodes) /\ Cardinality(Nodes) >= 1
ASSUME Nil \notin Nodes

VARIABLES
    state,
    currentTerm,
    votedFor,
    log,
    commitIndex,
    lastApplied,
    nextIndex,
    matchIndex,
    votesGranted,
    messages,
    snapshotLastIndex,
    snapshotLastTerm,
    config

vars == <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, messages, snapshotLastIndex, snapshotLastTerm, config>>

States == {"Follower", "PreCandidate", "Candidate", "Leader"}
EntryType == {"Normal", "AddNode", "RemoveNode"}
Entry == [term: Nat, val: LogValue \cup Nodes, type: EntryType]
MessageBody ==
    [type: {"RequestVote"}, term: Nat, lastLogIndex: Nat, lastLogTerm: Nat, prevote: BOOLEAN] \cup
    [type: {"RequestVoteResponse"}, term: Nat, voteGranted: BOOLEAN, requestTerm: Nat, prevote: BOOLEAN] \cup
    [type: {"AppendEntries"}, term: Nat, prevLogIndex: Nat, prevLogTerm: Nat, entries: Seq(Entry), leaderCommit: Nat] \cup
    [type: {"AppendEntriesResponse"}, term: Nat, success: BOOLEAN, matchIndex: Nat] \cup
    [type: {"Snapshot"}, term: Nat, lastIncludedIndex: Nat, lastIncludedTerm: Nat] \cup
    [type: {"SnapshotResponse"}, term: Nat, success: BOOLEAN, lastIncludedIndex: Nat]
Message == [from: Nodes, to: Nodes, body: MessageBody]

LastLogIndex(l) == Len(l)
LastLogTerm(l) == IF Len(l) = 0 THEN 0 ELSE l[Len(l)]["term"]
GetEntry(l, i) == IF i > 0 /\ i <= Len(l) THEN l[i] ELSE [term |-> 0, val |-> Nil, type |-> "Normal"]
IsQuorum(s, c) == Cardinality(s) * 2 > Cardinality(c)

Init ==
    /\ state = [n \in Nodes |-> "Follower"]
    /\ currentTerm = [n \in Nodes |-> 0]
    /\ votedFor = [n \in Nodes |-> Nil]
    /\ log = [n \in Nodes |-> <<>>]
    /\ commitIndex = [n \in Nodes |-> 0]
    /\ lastApplied = [n \in Nodes |-> 0]
    /\ votesGranted = [n \in Nodes |-> {}]
    /\ messages = EmptyBag
    /\ snapshotLastIndex = [n \in Nodes |-> 0]
    /\ snapshotLastTerm = [n \in Nodes |-> 0]
    /\ config = [n \in Nodes |-> Nodes]
    /\ nextIndex = [l \in Nodes |-> [f \in Nodes |-> 1]]
    /\ matchIndex = [l \in Nodes |-> [f \in Nodes |-> 0]]

ElectionTimeout(n) ==
    /\ state[n] \in {"Follower", "Candidate", "PreCandidate"}
    /\ state' = [state EXCEPT ![n] = "PreCandidate"]
    /\ currentTerm' = currentTerm
    /\ votedFor' = votedFor
    /\ votesGranted' = [votesGranted EXCEPT ![n] = {}]
    /\ LET nextTerm == currentTerm[n] + 1
           req == [type |-> "RequestVote", term |-> nextTerm,
                   lastLogIndex |-> LastLogIndex(log[n]),
                   lastLogTerm |-> LastLogTerm(log[n]),
                   prevote |-> TRUE]
       IN messages' = messages (+) Bagify({[from |-> n, to |-> p, body |-> req] : p \in config[n] \ {n}})
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, snapshotLastIndex, snapshotLastTerm, config>>

BecomeCandidate(n) ==
    /\ state[n] = "PreCandidate"
    /\ IsQuorum(votesGranted[n], config[n])
    /\ LET nextTerm == currentTerm[n] + 1
       IN /\ state' = [state EXCEPT ![n] = "Candidate"]
          /\ currentTerm' = [currentTerm EXCEPT ![n] = nextTerm]
          /\ votedFor' = [votedFor EXCEPT ![n] = n]
          /\ votesGranted' = [votesGranted EXCEPT ![n] = {n}]
          /\ LET req == [type |-> "RequestVote", term |-> nextTerm,
                         lastLogIndex |-> LastLogIndex(log[n]),
                         lastLogTerm |-> LastLogTerm(log[n]),
                         prevote |-> FALSE]
             IN messages' = messages (+) Bagify({[from |-> n, to |-> p, body |-> req] : p \in config[n] \ {n}})
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, snapshotLastIndex, snapshotLastTerm, config>>

BecomeLeader(n) ==
    /\ state[n] = "Candidate"
    /\ IsQuorum(votesGranted[n], config[n])
    /\ state' = [state EXCEPT ![n] = "Leader"]
    /\ nextIndex' = [nextIndex EXCEPT ![n] = [p \in Nodes |-> LastLogIndex(log[n]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![n] = [p \in Nodes |-> 0] @@ [n |-> LastLogIndex(log[n])]]
    /\ LET noop == [term |-> currentTerm[n], val |-> "NoOp", type |-> "Normal"]
       IN log' = [log EXCEPT ![n] = Append(log[n], noop)]
    /\ UNCHANGED <<currentTerm, votedFor, commitIndex, lastApplied, votesGranted, messages, snapshotLastIndex, snapshotLastTerm, config>>

RecvRequestVote(n) ==
    /\ \E m \in DOMAIN messages:
        /\ m["to"] = n
        /\ m["body"]["type"] = "RequestVote"
        /\ LET req == m["body"]
               candidateId == m["from"]
               logIsOk == \/ req["lastLogTerm"] > LastLogTerm(log[n])
                          \/ (req["lastLogTerm"] = LastLogTerm(log[n]) /\
                              req["lastLogIndex"] >= LastLogIndex(log[n]))
               grantVote == \/ req["term"] > currentTerm[n]
                            \/ (req["term"] = currentTerm[n] /\
                                (votedFor[n] = Nil \/ votedFor[n] = candidateId))
               canGrant == grantVote /\ logIsOk
        IN /\ \/ /\ req["prevote"] = FALSE /\ canGrant
                  /\ currentTerm' = [currentTerm EXCEPT ![n] = req["term"]]
                  /\ votedFor' = [votedFor EXCEPT ![n] = candidateId]
                  /\ state' = [state EXCEPT ![n] = "Follower"]
                  /\ LET resp == [type |-> "RequestVoteResponse", term |-> req["term"], voteGranted |-> TRUE, requestTerm |-> req["term"], prevote |-> FALSE]
                     IN messages' = (messages (-) Bagify({m})) (+) Bagify({[from |-> n, to |-> candidateId, body |-> resp]})
               \/ /\ req["prevote"] = TRUE /\ req["term"] > currentTerm[n] /\ logIsOk
                  /\ LET resp == [type |-> "RequestVoteResponse", term |-> currentTerm[n], voteGranted |-> TRUE, requestTerm |-> req["term"], prevote |-> TRUE]
                     IN messages' = (messages (-) Bagify({m})) (+) Bagify({[from |-> n, to |-> candidateId, body |-> resp]})
                  /\ UNCHANGED <<state, currentTerm, votedFor>>
               \/ /\ \lnot ((req["prevote"] = FALSE /\ canGrant) \/ (req["prevote"] = TRUE /\ req["term"] > currentTerm[n] /\ logIsOk))
                  /\ LET newTerm == IF req["term"] > currentTerm[n] /\ req["prevote"] = FALSE THEN req["term"] ELSE currentTerm[n]
                      newState == IF req["term"] > currentTerm[n] /\ req["prevote"] = FALSE THEN "Follower" ELSE state[n]
                      newVotedFor == IF req["term"] > currentTerm[n] /\ req["prevote"] = FALSE THEN [votedFor EXCEPT ![n] = Nil] ELSE votedFor
                      resp == [type |-> "RequestVoteResponse", term |-> newTerm, voteGranted |-> FALSE, requestTerm |-> req["term"], prevote |-> req["prevote"]]
                  IN /\ messages' = (messages (-) Bagify({m})) (+) Bagify({[from |-> n, to |-> candidateId, body |-> resp]})
                     /\ currentTerm' = [currentTerm EXCEPT ![n] = newTerm]
                     /\ state' = [state EXCEPT ![n] = newState]
                     /\ votedFor' = newVotedFor
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, snapshotLastIndex, snapshotLastTerm, config>>

RecvRequestVoteResponse(n) ==
    /\ \E m \in DOMAIN messages:
        /\ m["to"] = n
        /\ m["body"]["type"] = "RequestVoteResponse"
        /\ LET resp == m["body"]
        IN /\ \/ /\ resp["term"] > currentTerm[n]
                  /\ state' = [state EXCEPT ![n] = "Follower"]
                  /\ currentTerm' = [currentTerm EXCEPT ![n] = resp["term"]]
                  /\ votedFor' = [votedFor EXCEPT ![n] = Nil]
                  /\ UNCHANGED <<votesGranted>>
              \/ /\ resp["term"] = currentTerm[n] /\ state[n] = "Candidate" /\ resp["prevote"] = FALSE /\ resp["voteGranted"]
                  /\ votesGranted' = [votesGranted EXCEPT ![n] = votesGranted[n] \cup {m["from"]}]
                  /\ UNCHANGED <<state, currentTerm, votedFor>>
              \/ /\ resp["requestTerm"] = currentTerm[n] + 1 /\ state[n] = "PreCandidate" /\ resp["prevote"] = TRUE /\ resp["voteGranted"]
                  /\ votesGranted' = [votesGranted EXCEPT ![n] = votesGranted[n] \cup {m["from"]}]
                  /\ UNCHANGED <<state, currentTerm, votedFor>>
              \/ /\ \lnot resp["voteGranted"]
                  /\ UNCHANGED <<state, currentTerm, votedFor, votesGranted>>
           /\ messages' = messages (-) Bagify({m})
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, snapshotLastIndex, snapshotLastTerm, config>>

SendAppendEntries(n) ==
    /\ state[n] = "Leader"
    /\ \E p \in config[n] \ {n}:
        /\ LET prevLogIndex == nextIndex[n][p] - 1
               prevLogTerm == IF prevLogIndex > snapshotLastIndex[n]
                              THEN GetEntry(log[n], prevLogIndex)["term"]
                              ELSE IF prevLogIndex = snapshotLastIndex[n]
                                   THEN snapshotLastTerm[n]
                                   ELSE 0
               lastEntry == LastLogIndex(log[n])
               entriesToSend == SubSeq(log[n], nextIndex[n][p], lastEntry)
        IN /\ \/ /\ nextIndex[n][p] > snapshotLastIndex[n]
                  /\ LET req == [type |-> "AppendEntries", term |-> currentTerm[n],
                                 prevLogIndex |-> prevLogIndex, prevLogTerm |-> prevLogTerm,
                                 entries |-> entriesToSend, leaderCommit |-> commitIndex[n]]
                     IN messages' = messages (+) Bagify({[from |-> n, to |-> p, body |-> req]})
               \/ /\ nextIndex[n][p] <= snapshotLastIndex[n] /\ snapshotLastIndex[n] > 0
                  /\ LET req == [type |-> "Snapshot", term |-> currentTerm[n],
                                 lastIncludedIndex |-> snapshotLastIndex[n],
                                 lastIncludedTerm |-> snapshotLastTerm[n]]
                     IN messages' = messages (+) Bagify({[from |-> n, to |-> p, body |-> req]})
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, snapshotLastIndex, snapshotLastTerm, config>>

RecvAppendEntries(n) ==
    /\ \E m \in DOMAIN messages:
        /\ m["to"] = n
        /\ m["body"]["type"] = "AppendEntries"
        /\ LET req == m["body"]
               leaderId == m["from"]
        IN /\ \/ /\ req["term"] < currentTerm[n]
                  /\ LET resp == [type |-> "AppendEntriesResponse", term |-> currentTerm[n], success |-> FALSE, matchIndex |-> 0]
                     IN messages' = (messages (-) Bagify({m})) (+) Bagify({[from |-> n, to |-> leaderId, body |-> resp]})
                  /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied>>
               \/ /\ req["term"] >= currentTerm[n]
                  /\ LET newTerm == IF req["term"] > currentTerm[n] THEN req["term"] ELSE currentTerm[n]
                      newVotedFor == IF req["term"] > currentTerm[n] THEN Nil ELSE votedFor[n]
                      prevLogIndex == req["prevLogIndex"]
                      prevLogTerm == req["prevLogTerm"]
                      localPrevTerm == IF prevLogIndex > snapshotLastIndex[n]
                                       THEN GetEntry(log[n], prevLogIndex)["term"]
                                       ELSE IF prevLogIndex = snapshotLastIndex[n]
                                            THEN snapshotLastTerm[n]
                                            ELSE 0
                      logOK == prevLogIndex = 0 \/ (prevLogIndex <= LastLogIndex(log[n]) /\ localPrevTerm = prevLogTerm)
                  IN /\ state' = [state EXCEPT ![n] = "Follower"]
                     /\ currentTerm' = [currentTerm EXCEPT ![n] = newTerm]
                     /\ votedFor' = [votedFor EXCEPT ![n] = newVotedFor]
                     /\ \/ /\ logOK
                           /\ LET newLog == Append(SubSeq(log[n], 1, req["prevLogIndex"]), req["entries"])
                                  newCommitIndex == IF req["leaderCommit"] > commitIndex[n]
                                                    THEN min({req["leaderCommit"], LastLogIndex(newLog)})
                                                    ELSE commitIndex[n]
                           IN /\ log' = [log EXCEPT ![n] = newLog]
                              /\ commitIndex' = [commitIndex EXCEPT ![n] = newCommitIndex]
                              /\ LET resp == [type |-> "AppendEntriesResponse", term |-> newTerm, success |-> TRUE, matchIndex |-> LastLogIndex(newLog)]
                                 IN messages' = (messages (-) Bagify({m})) (+) Bagify({[from |-> n, to |-> leaderId, body |-> resp]})
                        \/ /\ \lnot logOK
                           /\ LET resp == [type |-> "AppendEntriesResponse", term |-> newTerm, success |-> FALSE, matchIndex |-> commitIndex[n]]
                              IN messages' = (messages (-) Bagify({m})) (+) Bagify({[from |-> n, to |-> leaderId, body |-> resp]})
                           /\ UNCHANGED <<log, commitIndex>>
                     /\ UNCHANGED <<lastApplied>>
    /\ UNCHANGED <<nextIndex, matchIndex, votesGranted, snapshotLastIndex, snapshotLastTerm, config>>

RecvAppendEntriesResponse(n) ==
    /\ state[n] = "Leader"
    /\ \E m \in DOMAIN messages:
        /\ m["to"] = n
        /\ m["body"]["type"] = "AppendEntriesResponse"
        /\ LET resp == m["body"]
               followerId == m["from"]
        IN /\ \/ /\ resp["term"] > currentTerm[n]
                  /\ state' = [state EXCEPT ![n] = "Follower"]
                  /\ currentTerm' = [currentTerm EXCEPT ![n] = resp["term"]]
                  /\ votedFor' = [votedFor EXCEPT ![n] = Nil]
                  /\ UNCHANGED <<nextIndex, matchIndex>>
               \/ /\ resp["term"] = currentTerm[n]
                  /\ \/ /\ resp["success"]
                         /\ nextIndex' = [nextIndex EXCEPT ![n][followerId] = resp["matchIndex"] + 1]
                         /\ matchIndex' = [matchIndex EXCEPT ![n][followerId] = resp["matchIndex"]]
                     \/ /\ \lnot resp["success"]
                         /\ nextIndex' = [nextIndex EXCEPT ![n][followerId] = max({1, nextIndex[n][followerId] - 1})]
                         /\ UNCHANGED <<matchIndex>>
                  /\ UNCHANGED <<state, currentTerm, votedFor>>
           /\ messages' = messages (-) Bagify({m})
    /\ UNCHANGED <<log, commitIndex, lastApplied, votesGranted, snapshotLastIndex, snapshotLastTerm, config>>

LeaderCommit(n) ==
    /\ state[n] = "Leader"
    /\ LET possibleCommits == { i \in (commitIndex[n]+1)..LastLogIndex(log[n]) |
                                /\ GetEntry(log[n], i)["term"] = currentTerm[n]
                                /\ IsQuorum({p \in config[n] | matchIndex[n][p] >= i}, config[n]) }
    /\ \E newCommitIndex \in possibleCommits:
        /\ commitIndex' = [commitIndex EXCEPT ![n] = newCommitIndex]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, lastApplied, nextIndex, matchIndex, votesGranted, messages, snapshotLastIndex, snapshotLastTerm, config>>

Apply(n) ==
    /\ commitIndex[n] > lastApplied[n]
    /\ LET applyIndex == lastApplied[n] + 1
           entry == GetEntry(log[n], applyIndex)
       IN /\ lastApplied' = [lastApplied EXCEPT ![n] = applyIndex]
          /\ config' = IF entry["type"] = "AddNode" THEN [config EXCEPT ![n] = config[n] \cup {entry["val"]}]
                      ELSE IF entry["type"] = "RemoveNode" THEN [config EXCEPT ![n] = config[n] \ {entry["val"]}]
                      ELSE config
          /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votesGranted, messages, snapshotLastIndex, snapshotLastTerm>>

ClientRequest(n) ==
    /\ state[n] = "Leader"
    /\ \E val \in LogValue:
        /\ LET newEntry == [term |-> currentTerm[n], val |-> val, type |-> "Normal"]
        IN log' = [log EXCEPT ![n] = Append(log[n], newEntry)]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, messages, snapshotLastIndex, snapshotLastTerm, config>>

ClientRequestConfigChange(n) ==
    /\ state[n] = "Leader"
    /\ \E changeType \in {"AddNode", "RemoveNode"}, nodeToChange \in Nodes:
        /\ LET newEntry == [term |-> currentTerm[n], val |-> nodeToChange, type |-> changeType]
        IN log' = [log EXCEPT ![n] = Append(log[n], newEntry)]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, messages, snapshotLastIndex, snapshotLastTerm, config>>

BeginSnapshot(n) ==
    /\ commitIndex[n] > snapshotLastIndex[n]
    /\ LET newSnapshotIndex == commitIndex[n]
           newSnapshotTerm == GetEntry(log[n], newSnapshotIndex)["term"]
       IN /\ snapshotLastIndex' = [snapshotLastIndex EXCEPT ![n] = newSnapshotIndex]
          /\ snapshotLastTerm' = [snapshotLastTerm EXCEPT ![n] = newSnapshotTerm]
          /\ log' = [log EXCEPT ![n] = SubSeq(log[n], newSnapshotIndex + 1, Len(log[n]))]
          /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, messages, config>>

RecvSnapshot(n) ==
    /\ \E m \in DOMAIN messages:
        /\ m["to"] = n
        /\ m["body"]["type"] = "Snapshot"
        /\ LET req == m["body"]
               leaderId == m["from"]
        IN /\ \/ /\ req["term"] < currentTerm[n]
                  /\ LET resp == [type |-> "SnapshotResponse", term |-> currentTerm[n], success |-> TRUE, lastIncludedIndex |-> req["lastIncludedIndex"]]
                     IN messages' = (messages (-) Bagify({m})) (+) Bagify({[from |-> n, to |-> leaderId, body |-> resp]})
                  /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, snapshotLastIndex, snapshotLastTerm, config>>
               \/ /\ req["term"] >= currentTerm[n]
                  /\ req["lastIncludedIndex"] > commitIndex[n]
                  /\ state' = [state EXCEPT ![n] = "Follower"]
                  /\ currentTerm' = [currentTerm EXCEPT ![n] = req["term"]]
                  /\ votedFor' = [votedFor EXCEPT ![n] = Nil]
                  /\ log' = [log EXCEPT ![n] = <<>>]
                  /\ commitIndex' = [commitIndex EXCEPT ![n] = req["lastIncludedIndex"]]
                  /\ lastApplied' = [lastApplied EXCEPT ![n] = req["lastIncludedIndex"]]
                  /\ snapshotLastIndex' = [snapshotLastIndex EXCEPT ![n] = req["lastIncludedIndex"]]
                  /\ snapshotLastTerm' = [snapshotLastTerm EXCEPT ![n] = req["lastIncludedIndex"]]
                  /\ LET resp == [type |-> "SnapshotResponse", term |-> req["term"], success |-> TRUE, lastIncludedIndex |-> req["lastIncludedIndex"]]
                     IN messages' = (messages (-) Bagify({m})) (+) Bagify({[from |-> n, to |-> leaderId, body |-> resp]})
                  /\ UNCHANGED <<config>>
    /\ UNCHANGED <<nextIndex, matchIndex, votesGranted>>

RecvSnapshotResponse(n) ==
    /\ state[n] = "Leader"
    /\ \E m \in DOMAIN messages:
        /\ m["to"] = n
        /\ m["body"]["type"] = "SnapshotResponse"
        /\ LET resp == m["body"]
               followerId == m["from"]
        IN /\ \/ /\ resp["term"] > currentTerm[n]
                  /\ state' = [state EXCEPT ![n] = "Follower"]
                  /\ currentTerm' = [currentTerm EXCEPT ![n] = resp["term"]]
                  /\ votedFor' = [votedFor EXCEPT ![n] = Nil]
                  /\ UNCHANGED <<nextIndex, matchIndex>>
               \/ /\ resp["term"] = currentTerm[n] /\ resp["success"]
                  /\ nextIndex' = [nextIndex EXCEPT ![n][followerId] = resp["lastIncludedIndex"] + 1]
                  /\ matchIndex' = [matchIndex EXCEPT ![n][followerId] = resp["lastIncludedIndex"]]
                  /\ UNCHANGED <<state, currentTerm, votedFor>>
           /\ messages' = messages (-) Bagify({m})
    /\ UNCHANGED <<log, commitIndex, lastApplied, votesGranted, snapshotLastIndex, snapshotLastTerm, config>>

Next ==
    \/ \E n \in Nodes:
        \/ ElectionTimeout(n)
        \/ BecomeCandidate(n)
        \/ BecomeLeader(n)
        \/ RecvRequestVote(n)
        \/ RecvRequestVoteResponse(n)
        \/ SendAppendEntries(n)
        \/ RecvAppendEntries(n)
        \/ RecvAppendEntriesResponse(n)
        \/ LeaderCommit(n)
        \/ Apply(n)
        \/ ClientRequest(n)
        \/ ClientRequestConfigChange(n)
        \/ BeginSnapshot(n)
        \/ RecvSnapshot(n)
        \/ RecvSnapshotResponse(n)
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

====