---- MODULE etcdraft ----
EXTENDS TLC, Sequences, Naturals, FiniteSets, Bags

CONSTANTS
    Nodes,
    Data,
    Nil,
    ElectionTimeoutMin,
    ElectionTimeoutMax,
    HeartbeatInterval

ASSUME ElectionTimeoutMin > HeartbeatInterval
ASSUME ElectionTimeoutMin =< ElectionTimeoutMax

VARIABLES
    messages,
    state,
    term,
    votedFor,
    log,
    commitIndex,
    electionTimer,
    heartbeatTimer,
    nextIndex,
    matchIndex,
    votesGranted

vars == <<messages, state, term, votedFor, log, commitIndex, electionTimer, heartbeatTimer, nextIndex, matchIndex, votesGranted>>

Quorum == (Cardinality(Nodes) \div 2) + 1

LastLogIndex(l) == Len(l)
LastLogTerm(l) == IF Len(l) > 0 THEN l[Len(l)]["term"] ELSE 0

IsUpToDate(myLog, candLastIndex, candLastTerm) ==
    LET myLastTerm == LastLogTerm(myLog)
        myLastIndex == LastLogIndex(myLog)
    IN \/ candLastTerm > myLastTerm
       \/ /\ candLastTerm = myLastTerm
          /\ candLastIndex >= myLastIndex

Init ==
    /\ state = [n \in Nodes |-> "Follower"]
    /\ term = [n \in Nodes |-> 0]
    /\ votedFor = [n \in Nodes |-> Nil]
    /\ log = [n \in Nodes |-> << [term |-> 0, val |-> "Init"] >>]
    /\ commitIndex = [n \in Nodes |-> 0]
    /\ \E timer \in [Nodes -> ElectionTimeoutMin..ElectionTimeoutMax] :
        electionTimer = timer
    /\ heartbeatTimer = [n \in Nodes |-> HeartbeatInterval]
    /\ nextIndex = [n \in Nodes |-> [p \in Nodes |-> 1]]
    /\ matchIndex = [n \in Nodes |-> [p \in Nodes |-> 0]]
    /\ votesGranted = [n \in Nodes |-> {}]
    /\ messages = EmptyBag

Tick ==
    /\ electionTimer' = [n \in Nodes |->
        IF state[n] \in {"Follower", "PreCandidate", "Candidate"} /\ electionTimer[n] > 0
        THEN electionTimer[n] - 1
        ELSE electionTimer[n]]
    /\ heartbeatTimer' = [n \in Nodes |->
        IF state[n] = "Leader" /\ heartbeatTimer[n] > 0
        THEN heartbeatTimer[n] - 1
        ELSE heartbeatTimer[n]]
    /\ UNCHANGED <<messages, state, term, votedFor, log, commitIndex, nextIndex, matchIndex, votesGranted>>

ElectionTimeout(n) ==
    /\ state[n] \in {"Follower", "PreCandidate", "Candidate"}
    /\ electionTimer[n] = 0
    /\ state' = [state EXCEPT ![n] = "PreCandidate"]
    /\ votesGranted' = [votesGranted EXCEPT ![n] = {n}]
    /\ LET
        nextTerm == term[n] + 1
        lastIdx == LastLogIndex(log[n])
        lastTerm == LastLogTerm(log[n])
        newMsgs == { [ type |-> "MsgPreVote", from |-> n, to |-> p,
                       term |-> nextTerm,
                       lastLogIndex |-> lastIdx, lastLogTerm |-> lastTerm ]
                     : p \in Nodes }
       IN messages' = messages (+) Bag(newMsgs)
    /\ \E newTimeout \in ElectionTimeoutMin..ElectionTimeoutMax:
        electionTimer' = [electionTimer EXCEPT ![n] = newTimeout]
    /\ UNCHANGED <<term, votedFor, log, commitIndex, heartbeatTimer, nextIndex, matchIndex>>

HeartbeatTimeout(n) ==
    /\ state[n] = "Leader"
    /\ heartbeatTimer[n] = 0
    /\ LET
        Broadcast(p) ==
            [ type |-> "MsgApp", from |-> n, to |-> p, term |-> term[n],
              prevLogIndex |-> LastLogIndex(log[n]),
              prevLogTerm |-> LastLogTerm(log[n]),
              entries |-> << >>,
              commitIndex |-> commitIndex[n] ]
        newMsgs == { Broadcast(p) : p \in Nodes \ {n} }
       IN messages' = messages (+) Bag(newMsgs)
    /\ heartbeatTimer' = [heartbeatTimer EXCEPT ![n] = HeartbeatInterval]
    /\ UNCHANGED <<state, term, votedFor, log, commitIndex, electionTimer, nextIndex, matchIndex, votesGranted>>

ClientRequest(leader, val) ==
    /\ state[leader] = "Leader"
    /\ LET newEntry == [term |-> term[leader], val |-> val]
    IN log' = [log EXCEPT ![leader] = Append(log[leader], newEntry)]
    /\ matchIndex' = [matchIndex EXCEPT ![leader] = [matchIndex[leader] EXCEPT ![leader] = Len(log[leader]) + 1]]
    /\ UNCHANGED <<messages, state, term, votedFor, commitIndex, electionTimer, heartbeatTimer, nextIndex, votesGranted>>

LeaderReplicateLog(leader, peer) ==
    /\ state[leader] = "Leader"
    /\ peer \in Nodes \ {leader}
    /\ LET
        prevLogIndex == nextIndex[leader][peer] - 1
        prevLogTerm == IF prevLogIndex > 0 THEN log[leader][prevLogIndex]["term"] ELSE 0
        entriesToSend == SubSeq(log[leader], nextIndex[leader][peer], Len(log[leader]))
        msg == [ type |-> "MsgApp", from |-> leader, to |-> peer, term |-> term[leader],
                 prevLogIndex |-> prevLogIndex,
                 prevLogTerm |-> prevLogTerm,
                 entries |-> entriesToSend,
                 commitIndex |-> commitIndex[leader] ]
       IN messages' = messages (+) Bag({msg})
    /\ UNCHANGED <<state, term, votedFor, log, commitIndex, electionTimer, heartbeatTimer, nextIndex, matchIndex, votesGranted>>

LoseMessage(msg) ==
    /\ msg \in DOMAIN messages
    /\ messages' = messages (-) Bag({msg})
    /\ UNCHANGED <<state, term, votedFor, log, commitIndex, electionTimer, heartbeatTimer, nextIndex, matchIndex, votesGranted>>

StepDownOnHigherTerm(n, msg) ==
    /\ msg["to"] = n
    /\ msg["term"] > term[n]
    /\ msg["type"] \in {"MsgApp", "MsgVote", "MsgHeartbeat"}
    /\ state' = [state EXCEPT ![n] = "Follower"]
    /\ term' = [term EXCEPT ![n] = msg["term"]]
    /\ votedFor' = [votedFor EXCEPT ![n] = Nil]
    /\ \E newTimeout \in ElectionTimeoutMin..ElectionTimeoutMax:
        electionTimer' = [electionTimer EXCEPT ![n] = newTimeout]
    /\ messages' = messages (-) Bag({msg})
    /\ UNCHANGED <<log, commitIndex, heartbeatTimer, nextIndex, matchIndex, votesGranted>>

HandlePreVoteRequest(n, msg) ==
    /\ msg["type"] = "MsgPreVote"
    /\ msg["to"] = n
    /\ msg["term"] > term[n]
    /\ LET
        upToDate == IsUpToDate(log[n], msg["lastLogIndex"], msg["lastLogTerm"])
        resp == [ type |-> "MsgPreVoteResp", from |-> n, to |-> msg["from"],
                  term |-> msg["term"], reject |-> \lnot upToDate ]
       IN messages' = (messages (-) Bag({msg})) (+) Bag({resp})
    /\ UNCHANGED <<state, term, votedFor, log, commitIndex, electionTimer, heartbeatTimer, nextIndex, matchIndex, votesGranted>>

HandlePreVoteResponse(n, msg) ==
    /\ msg["type"] = "MsgPreVoteResp"
    /\ msg["to"] = n
    /\ state[n] = "PreCandidate"
    /\ msg["term"] = term[n] + 1
    /\ IF msg["reject"]
       THEN /\ messages' = messages (-) Bag({msg})
            /\ UNCHANGED <<state, term, votedFor, log, commitIndex, electionTimer, heartbeatTimer, nextIndex, matchIndex, votesGranted>>
       ELSE /\ LET newVotes = votesGranted[n] \cup {msg["from"]}
            IN  IF Cardinality(newVotes) >= Quorum
                THEN /\ state' = [state EXCEPT ![n] = "Candidate"]
                     /\ term' = [term EXCEPT ![n] = term[n] + 1]
                     /\ votedFor' = [votedFor EXCEPT ![n] = n]
                     /\ votesGranted' = [votesGranted EXCEPT ![n] = {n}]
                     /\ LET
                         lastIdx == LastLogIndex(log[n])
                         lastTerm == LastLogTerm(log[n])
                         newMsgs == { [ type |-> "MsgVote", from |-> n, to |-> p,
                                        term |-> term[n] + 1,
                                        lastLogIndex |-> lastIdx, lastLogTerm |-> lastTerm ]
                                      : p \in Nodes }
                        IN messages' = (messages (-) Bag({msg})) (+) Bag(newMsgs)
                     /\ UNCHANGED <<log, commitIndex, electionTimer, heartbeatTimer, nextIndex, matchIndex>>
                ELSE /\ votesGranted' = [votesGranted EXCEPT ![n] = newVotes]
                     /\ messages' = messages (-) Bag({msg})
                     /\ UNCHANGED <<state, term, votedFor, log, commitIndex, electionTimer, heartbeatTimer, nextIndex, matchIndex>>

HandleVoteRequest(n, msg) ==
    /\ msg["type"] = "MsgVote"
    /\ msg["to"] = n
    /\ msg["term"] = term[n]
    /\ LET
        grantVote == /\ votedFor[n] \in {Nil, msg["from"]}
                     /\ IsUpToDate(log[n], msg["lastLogIndex"], msg["lastLogTerm"])
        resp == [ type |-> "MsgVoteResp", from |-> n, to |-> msg["from"],
                  term |-> term[n], reject |-> \lnot grantVote ]
       IN messages' = (messages (-) Bag({msg})) (+) Bag({resp})
    /\ IF grantVote
       THEN /\ votedFor' = [votedFor EXCEPT ![n] = msg["from"]]
            /\ \E newTimeout \in ElectionTimeoutMin..ElectionTimeoutMax:
                electionTimer' = [electionTimer EXCEPT ![n] = newTimeout]
       ELSE UNCHANGED <<votedFor, electionTimer>>
    /\ UNCHANGED <<state, term, log, commitIndex, heartbeatTimer, nextIndex, matchIndex, votesGranted>>

HandleVoteResponse(n, msg) ==
    /\ msg["type"] = "MsgVoteResp"
    /\ msg["to"] = n
    /\ state[n] = "Candidate"
    /\ msg["term"] = term[n]
    /\ IF msg["reject"]
       THEN /\ messages' = messages (-) Bag({msg})
            /\ UNCHANGED <<state, term, votedFor, log, commitIndex, electionTimer, heartbeatTimer, nextIndex, matchIndex, votesGranted>>
       ELSE /\ LET newVotes = votesGranted[n] \cup {msg["from"]}
            IN  IF Cardinality(newVotes) >= Quorum
                THEN /\ state' = [state EXCEPT ![n] = "Leader"]
                     /\ votesGranted' = [votesGranted EXCEPT ![n] = newVotes]
                     /\ nextIndex' = [nextIndex EXCEPT ![n] = [p \in Nodes |-> LastLogIndex(log[n]) + 1]]
                     /\ matchIndex' = [matchIndex EXCEPT ![n] = [p \in Nodes |-> 0]]
                     /\ heartbeatTimer' = [heartbeatTimer EXCEPT ![n] = HeartbeatInterval]
                     /\ LET
                         Broadcast(p) ==
                             [ type |-> "MsgApp", from |-> n, to |-> p, term |-> term[n],
                               prevLogIndex |-> LastLogIndex(log[n]),
                               prevLogTerm |-> LastLogTerm(log[n]),
                               entries |-> << >>,
                               commitIndex |-> commitIndex[n] ]
                         newMsgs == { Broadcast(p) : p \in Nodes \ {n} }
                        IN messages' = (messages (-) Bag({msg})) (+) Bag(newMsgs)
                     /\ UNCHANGED <<term, votedFor, log, commitIndex, electionTimer>>
                ELSE /\ votesGranted' = [votesGranted EXCEPT ![n] = newVotes]
                     /\ messages' = messages (-) Bag({msg})
                     /\ UNCHANGED <<state, term, votedFor, log, commitIndex, electionTimer, heartbeatTimer, nextIndex, matchIndex>>

HandleAppendEntries(n, msg) ==
    /\ msg["type"] = "MsgApp"
    /\ msg["to"] = n
    /\ msg["term"] = term[n]
    /\ state[n] \in {"Follower", "PreCandidate", "Candidate"}
    /\ state' = [state EXCEPT ![n] = "Follower"]
    /\ \E newTimeout \in ElectionTimeoutMin..ElectionTimeoutMax:
        electionTimer' = [electionTimer EXCEPT ![n] = newTimeout]
    /\ LET
        prevLogExists == msg["prevLogIndex"] <= Len(log[n])
        prevTermMatches == msg["prevLogIndex"] = 0 \/ (prevLogExists /\ log[n][msg["prevLogIndex"]]["term"] = msg["prevLogTerm"])
       IN IF prevTermMatches
          THEN /\ LET newLog == SubSeq(log[n], 1, msg["prevLogIndex"]) \o msg["entries"]
               IN /\ log' = [log EXCEPT ![n] = newLog]
                  /\ commitIndex' = [commitIndex EXCEPT ![n] = IF msg["commitIndex"] < Len(newLog) THEN msg["commitIndex"] ELSE Len(newLog)]
                  /\ LET resp == [type |-> "MsgAppResp", from |-> n, to |-> msg["from"], term |-> term[n],
                                  reject |-> FALSE, index |-> Len(newLog)]
                     IN messages' = (messages (-) Bag({msg})) (+) Bag({resp})
          ELSE /\ LET resp == [type |-> "MsgAppResp", from |-> n, to |-> msg["from"], term |-> term[n],
                            reject |-> TRUE, index |-> msg["prevLogIndex"]]
               IN messages' = (messages (-) Bag({msg})) (+) Bag({resp})
               /\ UNCHANGED <<log, commitIndex>>
    /\ UNCHANGED <<term, votedFor, heartbeatTimer, nextIndex, matchIndex, votesGranted>>

HandleAppendEntriesResponse(n, msg) ==
    /\ msg["type"] = "MsgAppResp"
    /\ msg["to"] = n
    /\ state[n] = "Leader"
    /\ msg["term"] = term[n]
    /\ messages' = messages (-) Bag({msg})
    /\ IF msg["reject"]
       THEN /\ nextIndex' = [nextIndex EXCEPT ![n] = [nextIndex[n] EXCEPT ![msg["from"]] = IF 1 > nextIndex[n][msg["from"]] - 1 THEN 1 ELSE nextIndex[n][msg["from"]] - 1]]
            /\ UNCHANGED <<matchIndex, commitIndex>>
       ELSE /\ LET newMatchIndexForN == [matchIndex[n] EXCEPT ![msg["from"]] = msg["index"]]
                  PossibleCommits ==
                      { N \in commitIndex[n]+1 .. LastLogIndex(log[n]) :
                          /\ log[n][N]["term"] = term[n]
                          /\ Cardinality({p \in Nodes | p /= n /\ newMatchIndexForN[p] >= N} \cup {n}) >= Quorum }
                  newCommitIndex == IF PossibleCommits = {} THEN commitIndex[n] ELSE Max(PossibleCommits)
             IN /\ matchIndex' = [matchIndex EXCEPT ![n] = newMatchIndexForN]
                /\ commitIndex' = [commitIndex EXCEPT ![n] = newCommitIndex]
            /\ nextIndex' = [nextIndex EXCEPT ![n] = [nextIndex[n] EXCEPT ![msg["from"]] = msg["index"] + 1]]
    /\ UNCHANGED <<state, term, votedFor, log, electionTimer, heartbeatTimer, votesGranted>>

Next ==
    \/ Tick
    \/ (\E n \in Nodes :
        \/ ElectionTimeout(n)
        \/ HeartbeatTimeout(n))
    \/ (\E leader \in Nodes, val \in Data: ClientRequest(leader, val))
    \/ (\E leader \in Nodes, peer \in Nodes: LeaderReplicateLog(leader, peer))
    \/ (\E msg \in DOMAIN messages:
        \/ LoseMessage(msg)
        \/ StepDownOnHigherTerm(msg["to"], msg)
        \/ HandlePreVoteRequest(msg["to"], msg)
        \/ HandlePreVoteResponse(msg["to"], msg)
        \/ HandleVoteRequest(msg["to"], msg)
        \/ HandleVoteResponse(msg["to"], msg)
        \/ HandleAppendEntries(msg["to"], msg)
        \/ HandleAppendEntriesResponse(msg["to"], msg)
      )

Spec == Init /\ [][Next]_vars

====
```