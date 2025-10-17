---- MODULE etcdraft ----
EXTENDS TLC, Sequences, Naturals, FiniteSets, Bags

CONSTANTS Server, Value, Nil

ASSUME Server \subseteq Nat
ASSUME Nil \notin (Server \cup Value \cup Nat)

VARIABLES
    state,
    term,
    votedFor,
    log,
    commitIndex,
    matchIndex,
    nextIndex,
    votesGranted,
    messages

vars == <<state, term, votedFor, log, commitIndex, matchIndex, nextIndex, votesGranted, messages>>

TypeOK ==
    /\ state \in [Server -> {"Follower", "PreCandidate", "Candidate", "Leader"}]
    /\ term \in [Server -> Nat]
    /\ votedFor \in [Server -> Server \cup {Nil}]
    /\ \A s \in Server: log[s] \in Seq([term: Nat, val: Value \cup {"NoOp"}])
    /\ commitIndex \in [Server -> Nat]
    /\ matchIndex \in [Server -> [Server -> Nat]]
    /\ nextIndex \in [Server -> [Server -> Nat]]
    /\ votesGranted \in [Server -> SUBSET Server]
    /\ IsBag(messages)

Quorum == Cardinality(Server) \div 2 + 1

LastLogTerm(l) == IF Len(l) = 0 THEN 0 ELSE l[Len(l)]["term"]
LastLogIndex(l) == Len(l)

IsUpToDate(candidateLogTerm, candidateLogIndex, myLog) ==
    LET myLastTerm == LastLogTerm(myLog)
        myLastIndex == LastLogIndex(myLog)
    IN \/ candidateLogTerm > myLastTerm
       \/ (candidateLogTerm = myLastTerm /\ candidateLogIndex >= myLastIndex)

Init ==
    /\ state = [s \in Server |-> "Follower"]
    /\ term = [s \in Server |-> 0]
    /\ votedFor = [s \in Server |-> Nil]
    /\ log = [s \in Server |-> <<>>]
    /\ commitIndex = [s \in Server |-> 0]
    /\ matchIndex = [s \in Server |-> [p \in Server |-> 0]]
    /\ nextIndex = [s \in Server |-> [p \in Server |-> 1]]
    /\ votesGranted = [s \in Server |-> {}]
    /\ messages = EmptyBag

\* Actions

ElectionTimeout(s) ==
    /\ \/ state[s] = "Follower"
       \/ state[s] = "PreCandidate"
       \/ state[s] = "Candidate"
    /\ state' = [state EXCEPT ![s] = "PreCandidate"]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
    /\ messages' = messages (+) Bag({
        [type |-> "MsgPreVote", from |-> s, to |-> p, term |-> term[s] + 1,
         logTerm |-> LastLogTerm(log[s]), index |-> LastLogIndex(log[s])]
        : p \in Server \ {s}
       })
    /\ UNCHANGED <<term, votedFor, log, commitIndex, matchIndex, nextIndex>>

ClientRequest(val) ==
    /\ \E leader \in Server: state[leader] = "Leader"
    /\ messages' = messages (+) Bag({[type |-> "MsgProp", value |-> val]})
    /\ UNCHANGED <<state, term, votedFor, log, commitIndex, matchIndex, nextIndex, votesGranted>>

HandleProp(s, m) ==
    /\ m["type"] = "MsgProp"
    /\ state[s] = "Leader"
    /\ LET newEntry == [term |-> term[s], val |-> m["value"]]
           newLog == Append(log[s], newEntry)
    IN /\ log' = [log EXCEPT ![s] = newLog]
       /\ matchIndex' = [matchIndex EXCEPT ![s][s] = LastLogIndex(newLog)]
       /\ nextIndex' = [nextIndex EXCEPT ![s][s] = LastLogIndex(newLog) + 1]
       /\ messages' = (messages (-) Bag({m}))
                      (+) Bag({
                          [type |-> "MsgApp", from |-> s, to |-> p, term |-> term[s],
                           prevLogIndex |-> LastLogIndex(log[s]),
                           prevLogTerm |-> LastLogTerm(log[s]),
                           entries |-> <<newEntry>>,
                           commit |-> commitIndex[s]]
                          : p \in Server \ {s}
                         })
       /\ UNCHANGED <<state, term, votedFor, commitIndex, votesGranted>>

HandlePreVote(s, m) ==
    /\ m["type"] = "MsgPreVote"
    /\ LET candLogOk == IsUpToDate(m["logTerm"], m["index"], log[s])
           grantVote == m["term"] > term[s] /\ candLogOk
    IN /\ messages' = (messages (-) Bag({m}))
                      (+) Bag({[type |-> "MsgPreVoteResp", from |-> s, to |-> m["from"],
                               term |-> m["term"], reject |-> NOT grantVote]})
       /\ UNCHANGED <<state, term, votedFor, log, commitIndex, matchIndex, nextIndex, votesGranted>>

HandlePreVoteResp(s, m) ==
    /\ m["type"] = "MsgPreVoteResp"
    /\ state[s] = "PreCandidate"
    /\ m["term"] = term[s] + 1
    /\ IF m["reject"] THEN
        /\ messages' = messages (-) Bag({m})
        /\ UNCHANGED <<state, term, votedFor, log, commitIndex, matchIndex, nextIndex, votesGranted>>
    ELSE
        /\ LET newVotes == votesGranted[s] \cup {m["from"]}
        IN IF Cardinality(newVotes) >= Quorum THEN
             /\ state' = [state EXCEPT ![s] = "Candidate"]
             /\ term' = [term EXCEPT ![s] = term[s] + 1]
             /\ votedFor' = [votedFor EXCEPT ![s] = s]
             /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
             /\ messages' = (messages (-) Bag({m}))
                            (+) Bag({
                                [type |-> "MsgVote", from |-> s, to |-> p, term |-> term[s] + 1,
                                 logTerm |-> LastLogTerm(log[s]), index |-> LastLogIndex(log[s])]
                                : p \in Server \ {s}
                               })
             /\ UNCHANGED <<log, commitIndex, matchIndex, nextIndex>>
           ELSE
             /\ votesGranted' = [votesGranted EXCEPT ![s] = newVotes]
             /\ messages' = messages (-) Bag({m})
             /\ UNCHANGED <<state, term, votedFor, log, commitIndex, matchIndex, nextIndex>>

HandleVote(s, m) ==
    /\ m["type"] = "MsgVote"
    /\ LET candLogOk == IsUpToDate(m["logTerm"], m["index"], log[s])
           canVote == votedFor[s] = Nil \/ votedFor[s] = m["from"]
           grantVote == m["term"] = term[s] /\ canVote /\ candLogOk
    IN /\ messages' = (messages (-) Bag({m}))
                      (+) Bag({[type |-> "MsgVoteResp", from |-> s, to |-> m["from"],
                               term |-> term[s], reject |-> NOT grantVote]})
       /\ IF grantVote THEN
            /\ votedFor' = [votedFor EXCEPT ![s] = m["from"]]
       ELSE
            /\ UNCHANGED votedFor
       /\ UNCHANGED <<state, term, log, commitIndex, matchIndex, nextIndex, votesGranted>>

HandleVoteResp(s, m) ==
    /\ m["type"] = "MsgVoteResp"
    /\ state[s] = "Candidate"
    /\ m["term"] = term[s]
    /\ IF m["reject"] THEN
        /\ messages' = messages (-) Bag({m})
        /\ UNCHANGED <<state, term, votedFor, log, commitIndex, matchIndex, nextIndex, votesGranted>>
    ELSE
        /\ LET newVotes == votesGranted[s] \cup {m["from"]}
        IN IF Cardinality(newVotes) >= Quorum THEN
             /\ state' = [state EXCEPT ![s] = "Leader"]
             /\ votesGranted' = [votesGranted EXCEPT ![s] = newVotes]
             /\ LET newEntry == [term |-> term[s], val |-> "NoOp"]
                    newLog == Append(log[s], newEntry)
                    newLastIndex == LastLogIndex(newLog)
                    newNextIndexBase == [s1 \in Server |-> [s2 \in Server |-> LastLogIndex(log[s]) + 1]]
                    newMatchIndexBase == [s1 \in Server |-> [s2 \in Server |-> 0]]
             IN /\ log' = [log EXCEPT ![s] = newLog]
                /\ nextIndex' = [newNextIndexBase EXCEPT ![s][s] = newLastIndex + 1]
                /\ matchIndex' = [newMatchIndexBase EXCEPT ![s][s] = newLastIndex]
                /\ messages' = (messages (-) Bag({m}))
                               (+) Bag({
                                   [type |-> "MsgApp", from |-> s, to |-> p, term |-> term[s],
                                    prevLogIndex |-> LastLogIndex(log[s]),
                                    prevLogTerm |-> LastLogTerm(log[s]),
                                    entries |-> <<newEntry>>,
                                    commit |-> commitIndex[s]]
                                   : p \in Server \ {s}
                                  })
                /\ UNCHANGED <<term, votedFor, commitIndex>>
           ELSE
             /\ votesGranted' = [votesGranted EXCEPT ![s] = newVotes]
             /\ messages' = messages (-) Bag({m})
             /\ UNCHANGED <<state, term, votedFor, log, commitIndex, matchIndex, nextIndex>>

HandleAppendEntries(s, m) ==
    /\ m["type"] = "MsgApp"
    /\ LET prevLogIndex == m["prevLogIndex"]
           prevLogTerm == m["prevLogTerm"]
           logOk == /\ prevLogIndex = 0
                    \/ /\ prevLogIndex <= Len(log[s])
                       /\ log[s][prevLogIndex]["term"] = prevLogTerm
    IN /\ IF logOk THEN
            /\ LET conflictIndexSet == { i \in (prevLogIndex + 1)..Len(log[s]) : log[s][i]["term"] # m["entries"][i - prevLogIndex]["term"] }
                   firstConflict == IF conflictIndexSet = {} THEN Nil ELSE CHOOSE i \in conflictIndexSet : TRUE
                   newLog == IF firstConflict = Nil
                                THEN log[s] \o SubSeq(m["entries"], Len(log[s]) - prevLogIndex + 1, Len(m["entries"]))
                                ELSE SubSeq(log[s], 1, firstConflict - 1) \o m["entries"]
                   newLastIndex == LastLogIndex(newLog)
            IN /\ log' = [log EXCEPT ![s] = newLog]
               /\ commitIndex' = [commitIndex EXCEPT ![s] = min(m["commit"], newLastIndex)]
               /\ messages' = (messages (-) Bag({m}))
                               (+) Bag({[type |-> "MsgAppResp", from |-> s, to |-> m["from"],
                                        term |-> term[s], index |-> newLastIndex,
                                        reject |-> FALSE]})
        ELSE
            /\ messages' = (messages (-) Bag({m}))
                           (+) Bag({[type |-> "MsgAppResp", from |-> s, to |-> m["from"],
                                    term |-> term[s], index |-> 0, reject |-> TRUE,
                                    rejectHint |-> min(prevLogIndex, LastLogIndex(log[s]))]})
            /\ UNCHANGED <<log, commitIndex>>
    /\ UNCHANGED <<state, term, votedFor, matchIndex, nextIndex, votesGranted>>

HandleAppendEntriesResp(s, m) ==
    /\ m["type"] = "MsgAppResp"
    /\ state[s] = "Leader"
    /\ m["term"] = term[s]
    /\ messages' = messages (-) Bag({m})
    /\ IF m["reject"] THEN
        /\ nextIndex' = [nextIndex EXCEPT ![s][m["from"]] = min(nextIndex[s][m["from"]] - 1, m["rejectHint"] + 1)]
        /\ UNCHANGED <<state, term, votedFor, log, commitIndex, matchIndex, votesGranted>>
    ELSE
        /\ LET newMatchIndex == [matchIndex EXCEPT ![s][m["from"]] = m["index"]]
        IN /\ matchIndex' = newMatchIndex
           /\ nextIndex' = [nextIndex EXCEPT ![s][m["from"]] = m["index"] + 1]
           /\ LET PossibleCommits == { N \in (commitIndex[s]+1)..Len(log[s]) :
                                         /\ log[s][N]["term"] = term[s]
                                         /\ Cardinality({p \in Server : newMatchIndex[s][p] >= N}) >= Quorum }
                  newCommitIndex == IF PossibleCommits = {} THEN commitIndex[s] ELSE CHOOSE N \in PossibleCommits : TRUE
           IN /\ commitIndex' = [commitIndex EXCEPT ![s] = newCommitIndex]
              /\ UNCHANGED <<state, term, votedFor, log, votesGranted>>

Heartbeat(s) ==
    /\ state[s] = "Leader"
    /\ messages' = messages (+) Bag({
        [type |-> "MsgApp", from |-> s, to |-> p, term |-> term[s],
         prevLogIndex |-> LastLogIndex(log[s]),
         prevLogTerm |-> LastLogTerm(log[s]),
         entries |-> <<>>,
         commit |-> commitIndex[s]]
        : p \in Server \ {s}
       })
    /\ UNCHANGED <<state, term, votedFor, log, commitIndex, matchIndex, nextIndex, votesGranted>>

BecomeFollower(s, newTerm) ==
    /\ state' = [state EXCEPT ![s] = "Follower"]
    /\ term' = [term EXCEPT ![s] = newTerm]
    /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
    /\ UNCHANGED <<log, commitIndex, matchIndex, nextIndex, votesGranted, messages>>

Receive(m) ==
    LET s == m["to"]
    IN \/ /\ m["term"] > term[s]
          /\ LET state_f == [state EXCEPT ![s] = "Follower"]
                 term_f == [term EXCEPT ![s] = m["term"]]
                 votedFor_f == [votedFor EXCEPT ![s] = Nil]
          IN /\ state' = state_f
             /\ term' = term_f
             /\ \/ /\ m["type"] = "MsgVote"
                   /\ LET candLogOk == IsUpToDate(m["logTerm"], m["index"], log[s])
                          canVote == votedFor_f[s] = Nil \/ votedFor_f[s] = m["from"]
                          grantVote == m["term"] = term_f[s] /\ canVote /\ candLogOk
                   IN /\ messages' = (messages (-) Bag({m}))
                                     (+) Bag({[type |-> "MsgVoteResp", from |-> s, to |-> m["from"],
                                              term |-> term_f[s], reject |-> NOT grantVote]})
                      /\ IF grantVote THEN
                           votedFor' = [votedFor_f EXCEPT ![s] = m["from"]]
                         ELSE
                           votedFor' = votedFor_f
                      /\ UNCHANGED <<log, commitIndex, matchIndex, nextIndex, votesGranted>>
                \/ /\ m["type"] = "MsgApp"
                   /\ LET prevLogIndex == m["prevLogIndex"]
                          prevLogTerm == m["prevLogTerm"]
                          logOk == /\ prevLogIndex = 0
                                   \/ /\ prevLogIndex <= Len(log[s])
                                      /\ log[s][prevLogIndex]["term"] = prevLogTerm
                   IN /\ votedFor' = votedFor_f
                      /\ IF logOk THEN
                           /\ LET conflictIndexSet == { i \in (prevLogIndex + 1)..Len(log[s]) : log[s][i]["term"] # m["entries"][i - prevLogIndex]["term"] }
                                  firstConflict == IF conflictIndexSet = {} THEN Nil ELSE CHOOSE i \in conflictIndexSet : TRUE
                                  newLog == IF firstConflict = Nil
                                               THEN log[s] \o SubSeq(m["entries"], Len(log[s]) - prevLogIndex + 1, Len(m["entries"]))
                                               ELSE SubSeq(log[s], 1, firstConflict - 1) \o m["entries"]
                                  newLastIndex == LastLogIndex(newLog)
                           IN /\ log' = [log EXCEPT ![s] = newLog]
                              /\ commitIndex' = [commitIndex EXCEPT ![s] = min(m["commit"], newLastIndex)]
                              /\ messages' = (messages (-) Bag({m}))
                                              (+) Bag({[type |-> "MsgAppResp", from |-> s, to |-> m["from"],
                                                       term |-> term_f[s], index |-> newLastIndex,
                                                       reject |-> FALSE]})
                              /\ UNCHANGED <<matchIndex, nextIndex, votesGranted>>
                         ELSE
                           /\ messages' = (messages (-) Bag({m}))
                                          (+) Bag({[type |-> "MsgAppResp", from |-> s, to |-> m["from"],
                                                   term |-> term_f[s], index |-> 0, reject |-> TRUE,
                                                   rejectHint |-> min(prevLogIndex, LastLogIndex(log[s]))]})
                           /\ UNCHANGED <<log, commitIndex, matchIndex, nextIndex, votesGranted>>
                \/ /\ m["type"] \notin {"MsgVote", "MsgApp"}
                   /\ messages' = messages (-) Bag({m})
                   /\ votedFor' = votedFor_f
                   /\ UNCHANGED <<log, commitIndex, matchIndex, nextIndex, votesGranted>>

       \/ /\ m["term"] < term[s]
          /\ LET respType == IF m["type"] = "MsgApp" THEN "MsgAppResp"
                             ELSE IF m["type"] = "MsgVote" THEN "MsgVoteResp"
                             ELSE "MsgPreVoteResp"
          IN /\ messages' = (messages (-) Bag({m}))
                         (+) Bag({[type |-> respType,
                                  from |-> s, to |-> m["from"], term |-> term[s], reject |-> TRUE]})
             /\ UNCHANGED <<state, term, votedFor, log, commitIndex, matchIndex, nextIndex, votesGranted>>

       \/ /\ m["term"] = term[s]
          /\ \/ HandleProp(s, m)
             \/ HandlePreVote(s, m)
             \/ HandlePreVoteResp(s, m)
             \/ HandleVote(s, m)
             \/ HandleVoteResp(s, m)
             \/ HandleAppendEntries(s, m)
             \/ HandleAppendEntriesResp(s, m)
             \/ /\ m["type"] = "MsgHeartbeat"
                /\ state[s] # "Leader"
                /\ commitIndex' = [commitIndex EXCEPT ![s] = min(m["commit"], LastLogIndex(log[s]))]
                /\ messages' = (messages (-) Bag({m})) (+) Bag({[type |-> "MsgHeartbeatResp", from |-> s, to |-> m["from"]]})
                /\ UNCHANGED <<state, term, votedFor, log, matchIndex, nextIndex, votesGranted>>

Next ==
    \/ \E s \in Server: ElectionTimeout(s)
    \/ \E val \in Value: ClientRequest(val)
    \/ \E s \in Server: Heartbeat(s)
    \/ \E m \in BagToSet(messages): Receive(m)

Spec == Init /\ [][Next]_vars

====
```