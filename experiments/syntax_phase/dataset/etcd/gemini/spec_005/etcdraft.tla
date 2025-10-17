---- MODULE etcdraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS
    Nodes,
    Data,
    ElectionTimeout,
    HeartbeatTimeout

ASSUME
    /\ Nodes = {"n1", "n2", "n3"}
    /\ Data = {"d1"}
    /\ ElectionTimeout > HeartbeatTimeout
    /\ HeartbeatTimeout > 0

VARIABLES
    term,
    state,
    votedFor,
    log,
    commitIndex,
    electionElapsed,
    heartbeatElapsed,
    votesGranted,
    matchIndex,
    nextIndex,
    msgs

vars == <<term, state, votedFor, log, commitIndex, electionElapsed,
          heartbeatElapsed, votesGranted, matchIndex, nextIndex, msgs>>

Quorum == (Cardinality(Nodes) \div 2) + 1

MessageTypes == { "MsgHup", "MsgApp", "MsgAppResp", "MsgVote", "MsgVoteResp",
                  "MsgPreVote", "MsgPreVoteResp", "MsgProp" }
NodeStates == { "Follower", "PreCandidate", "Candidate", "Leader" }

LogEntry(t, d) == [term |-> t, data |-> d]

EmptyLog == << [term |-> 0, data |-> "Init"] >>

LastLogIndex(n) == Len(log[n]) - 1
LastLogTerm(n) == IF LastLogIndex(n) = 0 THEN 0 ELSE log[n][LastLogIndex(n)+1]["term"]

isUpToDate(n, m) ==
    LET n_last_term == LastLogTerm(n) IN
    LET n_last_index == LastLogIndex(n) IN
    \/ m["prevLogTerm"] > n_last_term
    \/ (m["prevLogTerm"] = n_last_term /\ m["prevLogIndex"] >= n_last_index)

Init ==
    /\ term = [n \in Nodes |-> 0]
    /\ state = [n \in Nodes |-> "Follower"]
    /\ votedFor = [n \in Nodes |-> "None"]
    /\ log = [n \in Nodes |-> EmptyLog]
    /\ commitIndex = [n \in Nodes |-> 0]
    /\ electionElapsed = [n \in Nodes |-> 0]
    /\ heartbeatElapsed = [n \in Nodes |-> 0]
    /\ votesGranted = [n \in Nodes |-> {}]
    /\ matchIndex = [n \in Nodes |-> [i \in Nodes |-> 0]]
    /\ nextIndex = [n \in Nodes |-> [i \in Nodes |-> 1]]
    /\ msgs = EmptyBag

Tick(n) ==
    /\ electionElapsed' = [electionElapsed EXCEPT ![n] = @ + 1]
    /\ UNCHANGED <<term, state, votedFor, log, commitIndex, heartbeatElapsed,
                   votesGranted, matchIndex, nextIndex, msgs>>

Timeout(n) ==
    /\ state[n] \in {"Follower", "PreCandidate", "Candidate"}
    /\ electionElapsed[n] >= ElectionTimeout
    /\ msgs' = msgs (+) Bag({[
            type |-> "MsgHup", from |-> n, to |-> n,
            mterm |-> 0, prevLogIndex |-> 0, prevLogTerm |-> 0,
            entries |-> <<>>, commit |-> 0, reject |-> FALSE
        ]})
    /\ electionElapsed' = [electionElapsed EXCEPT ![n] = 0]
    /\ UNCHANGED <<term, state, votedFor, log, commitIndex, heartbeatElapsed,
                   votesGranted, matchIndex, nextIndex>>

LeaderTick(n) ==
    /\ state[n] = "Leader"
    /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![n] = @ + 1]
    /\ UNCHANGED <<term, state, votedFor, log, commitIndex, electionElapsed,
                   votesGranted, matchIndex, nextIndex, msgs>>

LeaderHeartbeat(n) ==
    /\ state[n] = "Leader"
    /\ heartbeatElapsed[n] >= HeartbeatTimeout
    /\ msgs' = msgs (+) Bag({[
            type |-> "MsgApp", from |-> n, to |-> peer,
            mterm |-> term[n],
            prevLogIndex |-> LastLogIndex(n),
            prevLogTerm |-> LastLogTerm(n),
            entries |-> <<>>,
            commit |-> commitIndex[n],
            reject |-> FALSE
        ] : peer \in Nodes \ {n}})
    /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![n] = 0]
    /\ UNCHANGED <<term, state, votedFor, log, commitIndex, electionElapsed,
                   votesGranted, matchIndex, nextIndex>>

ClientRequest(n, d) ==
    /\ state[n] = "Leader"
    /\ d \in Data
    /\ LET newEntry == LogEntry(term[n], d) IN
       LET newLog == Append(log[n], newEntry) IN
       /\ log' = [log EXCEPT ![n] = newLog]
       /\ matchIndex' = [matchIndex EXCEPT ![n] = [matchIndex[n] EXCEPT ![n] = LastLogIndex(n) + 1]]
       /\ msgs' = msgs (+) Bag({[
               type |-> "MsgApp", from |-> n, to |-> peer,
               mterm |-> term[n],
               prevLogIndex |-> LastLogIndex(n),
               prevLogTerm |-> LastLogTerm(n),
               entries |-> <<newEntry>>,
               commit |-> commitIndex[n],
               reject |-> FALSE
           ] : peer \in Nodes \ {n}})
    /\ UNCHANGED <<term, state, votedFor, commitIndex, electionElapsed,
                   heartbeatElapsed, votesGranted, nextIndex>>

Receive(m) ==
    LET n == m["to"] IN
    \/ /\ m["mterm"] > term[n]
       /\ m["type"] \in {"MsgApp", "MsgVote", "MsgVoteResp", "MsgAppResp", "MsgPreVote", "MsgPreVoteResp"}
       /\ state' = [state EXCEPT ![n] = "Follower"]
       /\ term' = [term EXCEPT ![n] = m["mterm"]]
       /\ votedFor' = [votedFor EXCEPT ![n] = "None"]
       /\ electionElapsed' = [electionElapsed EXCEPT ![n] = 0]
       /\ UNCHANGED <<log, commitIndex, heartbeatElapsed, votesGranted, matchIndex, nextIndex, msgs>>
    \/ /\ m["mterm"] < term[n]
       /\ \/ m["type"] = "MsgApp"
          \/ m["type"] = "MsgVote"
          \/ m["type"] = "MsgPreVote"
       /\ LET respType == IF m["type"] = "MsgApp" THEN "MsgAppResp"
                          ELSE IF m["type"] = "MsgVote" THEN "MsgVoteResp"
                          ELSE "MsgPreVoteResp" IN
          msgs' = msgs (+) Bag({[
              type |-> respType, from |-> n, to |-> m["from"],
              mterm |-> term[n],
              prevLogIndex |-> 0, prevLogTerm |-> 0,
              entries |-> <<>>, commit |-> 0, reject |-> TRUE
          ]})
          /\ UNCHANGED <<term, state, votedFor, log, commitIndex, electionElapsed,
                         heartbeatElapsed, votesGranted, matchIndex, nextIndex>>
    \/ /\ m["mterm"] = term[n]
       /\ \/ /\ m["type"] = "MsgHup"
             /\ state[n] = "Follower"
             /\ state' = [state EXCEPT ![n] = "PreCandidate"]
             /\ votesGranted' = [votesGranted EXCEPT ![n] = {n}]
             /\ msgs' = msgs (+) Bag({[
                     type |-> "MsgPreVote", from |-> n, to |-> peer,
                     mterm |-> term[n] + 1,
                     prevLogIndex |-> LastLogIndex(n),
                     prevLogTerm |-> LastLogTerm(n),
                     entries |-> <<>>, commit |-> 0, reject |-> FALSE
                 ] : peer \in Nodes \ {n}})
             /\ UNCHANGED <<term, votedFor, log, commitIndex, electionElapsed,
                            heartbeatElapsed, matchIndex, nextIndex>>
          \/ /\ m["type"] = "MsgPreVote"
             /\ LET grant == isUpToDate(n, m) IN
                /\ msgs' = msgs (+) Bag({[
                        type |-> "MsgPreVoteResp", from |-> n, to |-> m["from"],
                        mterm |-> m["mterm"],
                        prevLogIndex |-> 0, prevLogTerm |-> 0,
                        entries |-> <<>>, commit |-> 0, reject |-> \lnot grant
                    ]})
                /\ UNCHANGED <<term, state, votedFor, log, commitIndex, electionElapsed,
                               heartbeatElapsed, votesGranted, matchIndex, nextIndex>>
          \/ /\ m["type"] = "MsgVote"
             /\ LET grant == (votedFor[n] = "None" \/ votedFor[n] = m["from"]) /\ isUpToDate(n, m) IN
                /\ IF grant
                   THEN /\ votedFor' = [votedFor EXCEPT ![n] = m["from"]]
                        /\ electionElapsed' = [electionElapsed EXCEPT ![n] = 0]
                        /\ msgs' = msgs (+) Bag({[
                                type |-> "MsgVoteResp", from |-> n, to |-> m["from"],
                                mterm |-> m["mterm"],
                                prevLogIndex |-> 0, prevLogTerm |-> 0,
                                entries |-> <<>>, commit |-> 0, reject |-> FALSE
                            ]})
                        /\ UNCHANGED <<term, state, log, commitIndex, heartbeatElapsed,
                                       votesGranted, matchIndex, nextIndex>>
                   ELSE /\ msgs' = msgs (+) Bag({[
                                type |-> "MsgVoteResp", from |-> n, to |-> m["from"],
                                mterm |-> term[n],
                                prevLogIndex |-> 0, prevLogTerm |-> 0,
                                entries |-> <<>>, commit |-> 0, reject |-> TRUE
                            ]})
                        /\ UNCHANGED <<term, state, votedFor, log, commitIndex, electionElapsed,
                                       heartbeatElapsed, votesGranted, matchIndex, nextIndex>>
          \/ /\ m["type"] = "MsgPreVoteResp"
             /\ state[n] = "PreCandidate"
             /\ \/ /\ m["reject"] = TRUE
                   /\ UNCHANGED vars
                \/ /\ m["reject"] = FALSE
                   /\ LET newVotes == votesGranted[n] \cup {m["from"]} IN
                      \/ /\ Cardinality(newVotes) >= Quorum
                         /\ term' = [term EXCEPT ![n] = @ + 1]
                         /\ state' = [state EXCEPT ![n] = "Candidate"]
                         /\ votedFor' = [votedFor EXCEPT ![n] = n]
                         /\ votesGranted' = [votesGranted EXCEPT ![n] = {n}]
                         /\ msgs' = msgs (+) Bag({[
                                 type |-> "MsgVote", from |-> n, to |-> peer,
                                 mterm |-> term[n] + 1,
                                 prevLogIndex |-> LastLogIndex(n),
                                 prevLogTerm |-> LastLogTerm(n),
                                 entries |-> <<>>, commit |-> 0, reject |-> FALSE
                             ] : peer \in Nodes \ {n}})
                         /\ UNCHANGED <<log, commitIndex, electionElapsed, heartbeatElapsed,
                                        matchIndex, nextIndex>>
                      \/ /\ Cardinality(newVotes) < Quorum
                         /\ votesGranted' = [votesGranted EXCEPT ![n] = newVotes]
                         /\ UNCHANGED <<term, state, votedFor, log, commitIndex, electionElapsed,
                                        heartbeatElapsed, matchIndex, nextIndex, msgs>>
          \/ /\ m["type"] = "MsgVoteResp"
             /\ state[n] = "Candidate"
             /\ \/ /\ m["reject"] = TRUE
                   /\ UNCHANGED vars
                \/ /\ m["reject"] = FALSE
                   /\ LET newVotes == votesGranted[n] \cup {m["from"]} IN
                      \/ /\ Cardinality(newVotes) >= Quorum
                         /\ LET newEntry == LogEntry(term[n], "Init") IN
                            LET newLog == Append(log[n], newEntry) IN
                            LET newLastIndex == Len(newLog) - 1 IN
                            /\ state' = [state EXCEPT ![n] = "Leader"]
                            /\ log' = [log EXCEPT ![n] = newLog]
                            /\ nextIndex' = [nextIndex EXCEPT ![n] = [p \in Nodes |-> newLastIndex + 1]]
                            /\ matchIndex' = [matchIndex EXCEPT ![n] = [[p \in Nodes |-> 0] EXCEPT ![n] = newLastIndex]]
                            /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![n] = 0]
                            /\ msgs' = msgs (+) Bag({[
                                    type |-> "MsgApp", from |-> n, to |-> peer,
                                    mterm |-> term[n],
                                    prevLogIndex |-> LastLogIndex(n),
                                    prevLogTerm |-> LastLogTerm(n),
                                    entries |-> <<newEntry>>,
                                    commit |-> commitIndex[n],
                                    reject |-> FALSE
                                ] : peer \in Nodes \ {n}})
                         /\ UNCHANGED <<term, votedFor, commitIndex, electionElapsed, votesGranted>>
                      \/ /\ Cardinality(newVotes) < Quorum
                         /\ votesGranted' = [votesGranted EXCEPT ![n] = newVotes]
                         /\ UNCHANGED <<term, state, votedFor, log, commitIndex, electionElapsed,
                                        heartbeatElapsed, matchIndex, nextIndex, msgs>>
          \/ /\ m["type"] = "MsgApp"
             /\ state[n] \in {"Follower", "PreCandidate", "Candidate"}
             /\ state' = [state EXCEPT ![n] = "Follower"]
             /\ electionElapsed' = [electionElapsed EXCEPT ![n] = 0]
             /\ LET prevLogOK == /\ m["prevLogIndex"] < Len(log[n])
                                /\ log[n][m["prevLogIndex"] + 1]["term"] = m["prevLogTerm"] IN
                IF prevLogOK
                THEN /\ LET newLog == SubSeq(log[n], 1, m["prevLogIndex"] + 1) \o m["entries"] IN
                     /\ log' = [log EXCEPT ![n] = newLog]
                     /\ LET newLastIndex == m["prevLogIndex"] + Len(m["entries"]) IN
                        /\ commitIndex' = [commitIndex EXCEPT ![n] = Min(m["commit"], newLastIndex)]
                        /\ msgs' = msgs (+) Bag({[
                                type |-> "MsgAppResp", from |-> n, to |-> m["from"],
                                mterm |-> term[n],
                                prevLogIndex |-> newLastIndex,
                                prevLogTerm |-> 0,
                                entries |-> <<>>, commit |-> 0, reject |-> FALSE
                            ]})
                     /\ UNCHANGED <<term, votedFor, heartbeatElapsed, votesGranted, matchIndex, nextIndex>>
                ELSE /\ msgs' = msgs (+) Bag({[
                             type |-> "MsgAppResp", from |-> n, to |-> m["from"],
                             mterm |-> term[n],
                             prevLogIndex |-> LastLogIndex(n),
                             prevLogTerm |-> LastLogTerm(n),
                             entries |-> <<>>, commit |-> 0, reject |-> TRUE
                         ]})
                     /\ UNCHANGED <<term, log, commitIndex, votedFor, heartbeatElapsed,
                                    votesGranted, matchIndex, nextIndex>>
          \/ /\ m["type"] = "MsgAppResp"
             /\ state[n] = "Leader"
             /\ LET peer == m["from"] IN
                \/ /\ m["reject"] = TRUE
                   /\ nextIndex' = [nextIndex EXCEPT ![n] = [nextIndex[n] EXCEPT ![peer] = @ - 1]]
                   /\ UNCHANGED <<term, state, votedFor, log, commitIndex, electionElapsed,
                                  heartbeatElapsed, votesGranted, matchIndex, msgs>>
                \/ /\ m["reject"] = FALSE
                   /\ LET newMatchIndex == [matchIndex[n] EXCEPT ![peer] = m["prevLogIndex"]] IN
                      /\ matchIndex' = [matchIndex EXCEPT ![n] = newMatchIndex]
                      /\ nextIndex' = [nextIndex EXCEPT ![n] = [nextIndex[n] EXCEPT ![peer] = m["prevLogIndex"] + 1]]
                      /\ LET PossibleCommits ==
                                { idx \in commitIndex[n]+1..LastLogIndex(n) :
                                    /\ log[n][idx+1]["term"] = term[n]
                                    /\ Cardinality({p \in Nodes : newMatchIndex[p] >= idx}) >= Quorum
                                }
                         IN
                         /\ commitIndex' = [commitIndex EXCEPT ![n] =
                                            IF PossibleCommits = {} THEN @ ELSE Max(PossibleCommits)]
                         /\ UNCHANGED <<term, state, votedFor, log, electionElapsed,
                                        heartbeatElapsed, votesGranted, msgs>>

Next ==
    \/ \E n \in Nodes :
        \/ Tick(n)
        \/ Timeout(n)
        \/ LeaderTick(n)
        \/ LeaderHeartbeat(n)
        \/ \E d \in Data : ClientRequest(n, d)
    \/ \E m \in BagToSet(msgs) :
        \/ (Receive(m) /\ msgs' = msgs -+ Bag({m}))
        \/ (msgs' = msgs -+ Bag({m}) /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

====
