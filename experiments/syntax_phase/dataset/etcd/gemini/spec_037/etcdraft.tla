---- MODULE etcdraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Nodes, Value, Nil

ASSUME IsFiniteSet(Nodes)
ASSUME IsFiniteSet(Value)
ASSUME Nil \notin Nodes

Quorum == Cardinality(Nodes) \div 2 + 1
ElectionTimeoutMin == 5
ElectionTimeoutMax == 10

MessageTypes == {"MsgProp", "MsgHup", "MsgPreVoteReq", "MsgPreVoteResp", "MsgVoteReq", "MsgVoteResp", "MsgAppReq", "MsgAppResp"}
NodeStates == {"Follower", "PreCandidate", "Candidate", "Leader"}

LastLogIndex(log) == Len(log)
LastLogTerm(log) == IF log = <<>> THEN 0 ELSE log[Len(log)]["term"]

IsUpToDate(myLog, candLastLogIndex, candLastLogTerm) ==
    LET myLastLogTerm == LastLogTerm(myLog)
        myLastLogIndex == LastLogIndex(myLog)
    IN \/ candLastLogTerm > myLastLogTerm
       \/ /\ candLastLogTerm = myLastLogTerm
          /\ candLastLogIndex >= myLastLogIndex

VARIABLES
    term,
    state,
    votedFor,
    log,
    commitIndex,
    votesGranted,
    matchIndex,
    nextIndex,
    messages,
    electionTimer,
    randomizedElectionTimeout

vars == <<term, state, votedFor, log, commitIndex, votesGranted, matchIndex, nextIndex, messages, electionTimer, randomizedElectionTimeout>>

Init ==
    /\ term = [n \in Nodes |-> 0]
    /\ state = [n \in Nodes |-> "Follower"]
    /\ votedFor = [n \in Nodes |-> Nil]
    /\ log = [n \in Nodes |-> << >>]
    /\ commitIndex = [n \in Nodes |-> 0]
    /\ votesGranted = [n \in Nodes |-> {}]
    /\ matchIndex = [l \in Nodes |-> [f \in Nodes |-> 0]]
    /\ nextIndex = [l \in Nodes |-> [f \in Nodes |-> 1]]
    /\ messages = EmptyBag
    /\ electionTimer = [n \in Nodes |-> 0]
    /\ randomizedElectionTimeout \in [Nodes -> (ElectionTimeoutMin..ElectionTimeoutMax)]

BecomeFollower(n, newTerm) ==
    /\ term' = [term EXCEPT ![n] = newTerm]
    /\ state' = [state EXCEPT ![n] = "Follower"]
    /\ votedFor' = [votedFor EXCEPT ![n] = Nil]
    /\ votesGranted' = [votesGranted EXCEPT ![n] = {}]
    /\ electionTimer' = [electionTimer EXCEPT ![n] = 0]
    /\ \E t \in ElectionTimeoutMin..ElectionTimeoutMax:
        randomizedElectionTimeout' = [randomizedElectionTimeout EXCEPT ![n] = t]
    /\ UNCHANGED <<log, commitIndex, matchIndex, nextIndex, messages>>

Tick(n) ==
    /\ electionTimer' = [electionTimer EXCEPT ![n] = electionTimer[n] + 1]
    /\ UNCHANGED <<term, state, votedFor, log, commitIndex, votesGranted, matchIndex, nextIndex, messages, randomizedElectionTimeout>>

Timeout(n) ==
    /\ state[n] \in {"Follower", "Candidate", "PreCandidate"}
    /\ electionTimer[n] >= randomizedElectionTimeout[n]
    /\ state' = [state EXCEPT ![n] = "PreCandidate"]
    /\ votesGranted' = [votesGranted EXCEPT ![n] = {n}]
    /\ electionTimer' = [electionTimer EXCEPT ![n] = 0]
    /\ \E t \in ElectionTimeoutMin..ElectionTimeoutMax:
        randomizedElectionTimeout' = [randomizedElectionTimeout EXCEPT ![n] = t]
    /\ messages' = messages (+) Bag({
            [
                type |-> "MsgPreVoteReq",
                from |-> n,
                to |-> peer,
                term |-> term[n] + 1,
                lastLogIndex |-> LastLogIndex(log[n]),
                lastLogTerm |-> LastLogTerm(log[n])
            ] : peer \in Nodes \ {n}
        })
    /\ UNCHANGED <<term, votedFor, log, commitIndex, matchIndex, nextIndex>>

HandlePreVoteRequest(n) ==
    \E m \in BagToSet(messages):
        /\ m["type"] = "MsgPreVoteReq"
        /\ m["to"] = n
        /\ LET candTerm = m["term"]
               candId = m["from"]
               candLastLogIndex = m["lastLogIndex"]
               candLastLogTerm = m["lastLogTerm"]
               grant == /\ candTerm > term[n]
                        /\ IsUpToDate(log[n], candLastLogIndex, candLastLogTerm)
        IN /\ messages' = (messages (-) {m})
                          (+) {[
                                type |-> "MsgPreVoteResp",
                                from |-> n,
                                to |-> candId,
                                term |-> candTerm,
                                voteGranted |-> grant
                            ]}
           /\ UNCHANGED <<term, state, votedFor, log, commitIndex, votesGranted, matchIndex, nextIndex, electionTimer, randomizedElectionTimeout>>

HandlePreVoteResponse(n) ==
    \E m \in BagToSet(messages):
        /\ m["type"] = "MsgPreVoteResp"
        /\ m["to"] = n
        /\ state[n] = "PreCandidate"
        /\ LET respTerm = m["term"]
               voter = m["from"]
        IN /\ respTerm = term[n] + 1
           /\ IF m["voteGranted"]
              THEN /\ LET newVotesGranted == votesGranted[n] \cup {voter}
                   IN IF Cardinality(newVotesGranted) >= Quorum
                         THEN (* Start real election *)
                              /\ state' = [state EXCEPT ![n] = "Candidate"]
                              /\ term' = [term EXCEPT ![n] = term[n] + 1]
                              /\ votedFor' = [votedFor EXCEPT ![n] = n]
                              /\ votesGranted' = [votesGranted EXCEPT ![n] = {n}]
                              /\ messages' = (messages (-) {m}) (+) Bag({
                                       [
                                           type |-> "MsgVoteReq",
                                           from |-> n,
                                           to |-> peer,
                                           term |-> term[n] + 1,
                                           lastLogIndex |-> LastLogIndex(log[n]),
                                           lastLogTerm |-> LastLogTerm(log[n])
                                       ] : peer \in Nodes \ {n}
                                   })
                              /\ UNCHANGED <<log, commitIndex, matchIndex, nextIndex, electionTimer, randomizedElectionTimeout>>
                         ELSE /\ messages' = messages (-) {m}
                              /\ votesGranted' = [votesGranted EXCEPT ![n] = newVotesGranted]
                              /\ UNCHANGED <<term, state, votedFor, log, commitIndex, matchIndex, nextIndex, electionTimer, randomizedElectionTimeout>>
              ELSE /\ messages' = messages (-) {m}
                   /\ UNCHANGED <<votesGranted, term, state, votedFor, log, commitIndex, matchIndex, nextIndex, electionTimer, randomizedElectionTimeout>>

HandleVoteRequest(n) ==
    \E m \in BagToSet(messages):
        /\ m["type"] = "MsgVoteReq"
        /\ m["to"] = n
        /\ LET candTerm = m["term"]
               candId = m["from"]
               candLastLogIndex = m["lastLogIndex"]
               candLastLogTerm = m["lastLogTerm"]
        IN /\ \/ /\ candTerm < term[n]
                 /\ messages' = (messages (-) {m}) (+) {[
                                      type |-> "MsgVoteResp",
                                      from |-> n,
                                      to |-> candId,
                                      term |-> term[n],
                                      voteGranted |-> FALSE
                                  ]}
                 /\ UNCHANGED <<term, state, votedFor, log, commitIndex, votesGranted, matchIndex, nextIndex, electionTimer, randomizedElectionTimeout>>
              \/ /\ candTerm > term[n]
                 /\ IsUpToDate(log[n], candLastLogIndex, candLastLogTerm)
                 /\ messages' = (messages (-) {m}) (+) {[
                                      type |-> "MsgVoteResp",
                                      from |-> n,
                                      to |-> candId,
                                      term |-> candTerm,
                                      voteGranted |-> TRUE
                                  ]}
                 /\ term' = [term EXCEPT ![n] = candTerm]
                 /\ state' = [state EXCEPT ![n] = "Follower"]
                 /\ votedFor' = [votedFor EXCEPT ![n] = candId]
                 /\ UNCHANGED <<log, commitIndex, votesGranted, matchIndex, nextIndex, electionTimer, randomizedElectionTimeout>>
              \/ /\ candTerm = term[n]
                 /\ votedFor[n] \in {Nil, candId}
                 /\ IsUpToDate(log[n], candLastLogIndex, candLastLogTerm)
                 /\ messages' = (messages (-) {m}) (+) {[
                                      type |-> "MsgVoteResp",
                                      from |-> n,
                                      to |-> candId,
                                      term |-> term[n],
                                      voteGranted |-> TRUE
                                  ]}
                 /\ votedFor' = [votedFor EXCEPT ![n] = candId]
                 /\ UNCHANGED <<term, state, log, commitIndex, votesGranted, matchIndex, nextIndex, electionTimer, randomizedElectionTimeout>>
              \/ /\ candTerm >= term[n]
                 /\ NOT(IsUpToDate(log[n], candLastLogIndex, candLastLogTerm) /\ (votedFor[n] \in {Nil, candId}))
                 /\ messages' = (messages (-) {m}) (+) {[
                                      type |-> "MsgVoteResp",
                                      from |-> n,
                                      to |-> candId,
                                      term |-> term[n],
                                      voteGranted |-> FALSE
                                  ]}
                 /\ UNCHANGED <<term, state, votedFor, log, commitIndex, votesGranted, matchIndex, nextIndex, electionTimer, randomizedElectionTimeout>>

HandleVoteResponse(n) ==
    \E m \in BagToSet(messages):
        /\ m["type"] = "MsgVoteResp"
        /\ m["to"] = n
        /\ state[n] = "Candidate"
        /\ LET respTerm = m["term"]
               voter = m["from"]
        IN /\ respTerm = term[n]
           /\ messages' = messages (-) {m}
           /\ IF m["voteGranted"]
              THEN /\ LET newVotesGranted == votesGranted[n] \cup {voter}
                   IN /\ votesGranted' = [votesGranted EXCEPT ![n] = newVotesGranted]
                      /\ IF Cardinality(newVotesGranted) >= Quorum
                         THEN (* Become Leader *)
                              /\ state' = [state EXCEPT ![n] = "Leader"]
                              /\ nextIndex' = [nextIndex EXCEPT ![n] = [p \in Nodes |-> LastLogIndex(log[n]) + 1]]
                              /\ matchIndex' = [matchIndex EXCEPT ![n] = [p \in Nodes |-> 0]]
                              /\ UNCHANGED <<term, votedFor, log, commitIndex, electionTimer, randomizedElectionTimeout>>
                         ELSE /\ UNCHANGED <<term, state, votedFor, log, commitIndex, matchIndex, nextIndex, electionTimer, randomizedElectionTimeout>>
              ELSE /\ UNCHANGED <<votesGranted, term, state, votedFor, log, commitIndex, matchIndex, nextIndex, electionTimer, randomizedElectionTimeout>>

ClientRequest(v) ==
    \E n \in Nodes:
        /\ state[n] = "Leader"
        /\ LET newEntry == [term |-> term[n], value |-> v]
        IN /\ log' = [log EXCEPT ![n] = Append(log[n], newEntry)]
           /\ UNCHANGED <<term, state, votedFor, commitIndex, votesGranted, matchIndex, nextIndex, messages, electionTimer, randomizedElectionTimeout>>

ReplicateLog(n) ==
    /\ state[n] = "Leader"
    /\ \E peer \in Nodes \ {n}:
        /\ nextIndex[n][peer] <= LastLogIndex(log[n])
        /\ LET prevLogIndex == nextIndex[n][peer] - 1
               prevLogTerm == IF prevLogIndex > 0 THEN log[n][prevLogIndex]["term"] ELSE 0
               lastEntry == LastLogIndex(log[n])
               entriesToSend == SubSeq(log[n], nextIndex[n][peer], lastEntry)
        IN /\ messages' = messages (+) {[
                   type |-> "MsgAppReq",
                   from |-> n,
                   to |-> peer,
                   term |-> term[n],
                   prevLogIndex |-> prevLogIndex,
                   prevLogTerm |-> prevLogTerm,
                   entries |-> entriesToSend,
                   leaderCommit |-> commitIndex[n]
               ]}
           /\ UNCHANGED <<term, state, votedFor, log, commitIndex, votesGranted, matchIndex, nextIndex, electionTimer, randomizedElectionTimeout>>

Heartbeat(n) ==
    /\ state[n] = "Leader"
    /\ \E peer \in Nodes \ {n}:
        /\ nextIndex[n][peer] > LastLogIndex(log[n])
        /\ LET prevLogIndex == LastLogIndex(log[n])
               prevLogTerm == LastLogTerm(log[n])
        IN /\ messages' = messages (+) {[
                   type |-> "MsgAppReq",
                   from |-> n,
                   to |-> peer,
                   term |-> term[n],
                   prevLogIndex |-> prevLogIndex,
                   prevLogTerm |-> prevLogTerm,
                   entries |-> << >>,
                   leaderCommit |-> commitIndex[n]
               ]}
           /\ UNCHANGED <<term, state, votedFor, log, commitIndex, votesGranted, matchIndex, nextIndex, electionTimer, randomizedElectionTimeout>>

HandleAppendEntriesRequest(n) ==
    \E m \in BagToSet(messages):
        /\ m["type"] = "MsgAppReq"
        /\ m["to"] = n
        /\ LET leaderTerm = m["term"]
               leaderId = m["from"]
               prevLogIndex = m["prevLogIndex"]
               prevLogTerm = m["prevLogTerm"]
               entries = m["entries"]
               leaderCommit = m["leaderCommit"]
        IN /\ IF leaderTerm < term[n]
              THEN /\ messages' = (messages (-) {m}) (+) {[
                           type |-> "MsgAppResp",
                           from |-> n,
                           to |-> leaderId,
                           term |-> term[n],
                           success |-> FALSE,
                           matchIndex |-> 0
                       ]}
                   /\ UNCHANGED <<term, state, votedFor, log, commitIndex, votesGranted, matchIndex, nextIndex, electionTimer, randomizedElectionTimeout>>
              ELSE /\ electionTimer' = [electionTimer EXCEPT ![n] = 0]
                   /\ term' = [term EXCEPT ![n] = leaderTerm]
                   /\ state' = [state EXCEPT ![n] = IF state[n] = "Leader" THEN "Follower" ELSE state[n]]
                   /\ LET logOK == /\ prevLogIndex <= LastLogIndex(log[n])
                                   /\ (prevLogIndex = 0 \/ log[n][prevLogIndex]["term"] = prevLogTerm)
                   IN IF logOK
                      THEN /\ LET conflictingIndices == { i \in 1..Len(entries):
                                                      /\ prevLogIndex + i <= Len(log[n])
                                                      /\ log[n][prevLogIndex + i]["term"] /= entries[i]["term"] }
                           IN LET newLog == IF conflictingIndices = {}
                                            THEN AppendSeq(SubSeq(log[n], 1, prevLogIndex), entries)
                                            ELSE LET conflictIndex == CHOOSE i \in conflictingIndices: \A j \in conflictingIndices: i <= j
                                                 IN AppendSeq(SubSeq(log[n], 1, prevLogIndex + conflictIndex - 1), SubSeq(entries, conflictIndex, Len(entries)))
                           IN /\ log' = [log EXCEPT ![n] = newLog]
                              /\ commitIndex' = [commitIndex EXCEPT ![n] = Max({commitIndex[n], Min({leaderCommit, LastLogIndex(newLog)})})]
                              /\ messages' = (messages (-) {m}) (+) {[
                                           type |-> "MsgAppResp",
                                           from |-> n,
                                           to |-> leaderId,
                                           term |-> leaderTerm,
                                           success |-> TRUE,
                                           matchIndex |-> LastLogIndex(newLog)
                                       ]}
                              /\ UNCHANGED <<votedFor, votesGranted, matchIndex, nextIndex, randomizedElectionTimeout>>
                      ELSE /\ messages' = (messages (-) {m}) (+) {[
                                           type |-> "MsgAppResp",
                                           from |-> n,
                                           to |-> leaderId,
                                           term |-> leaderTerm,
                                           success |-> FALSE,
                                           matchIndex |-> 0
                                       ]}
                           /\ UNCHANGED <<votedFor, log, commitIndex, votesGranted, matchIndex, nextIndex, randomizedElectionTimeout>>

HandleAppendEntriesResponse(n) ==
    \E m \in BagToSet(messages):
        /\ m["type"] = "MsgAppResp"
        /\ m["to"] = n
        /\ state[n] = "Leader"
        /\ LET respTerm = m["term"]
               followerId = m["from"]
        IN /\ respTerm = term[n]
           /\ messages' = messages (-) {m}
           /\ IF m["success"]
              THEN /\ LET newMatchIndex == [matchIndex[n] EXCEPT ![followerId] = m["matchIndex"]]
                   IN /\ matchIndex' = [matchIndex EXCEPT ![n] = newMatchIndex]
                      /\ nextIndex' = [nextIndex EXCEPT ![n] = [nextIndex[n] EXCEPT ![followerId] = m["matchIndex"] + 1]]
                      /\ LET potentialCommits == { i \in (commitIndex[n]+1)..LastLogIndex(log[n]) :
                                                       /\ log[n][i]["term"] = term[n]
                                                       /\ Cardinality({p \in Nodes : newMatchIndex[p] >= i}) >= Quorum
                                                   }
                      IN commitIndex' = [commitIndex EXCEPT ![n] = IF potentialCommits = {} THEN commitIndex[n] ELSE Max(potentialCommits)]
                      /\ UNCHANGED <<term, state, votedFor, log, votesGranted, electionTimer, randomizedElectionTimeout>>
              ELSE /\ nextIndex' = [nextIndex EXCEPT ![n] = [nextIndex[n] EXCEPT ![followerId] = Max({1, nextIndex[n][followerId] - 1})]]
                   /\ UNCHANGED <<term, state, votedFor, log, commitIndex, votesGranted, matchIndex, electionTimer, randomizedElectionTimeout>>

DropMessage ==
    \E m \in BagToSet(messages):
        /\ messages' = messages (-) {m}
        /\ UNCHANGED <<term, state, votedFor, log, commitIndex, votesGranted, matchIndex, nextIndex, electionTimer, randomizedElectionTimeout>>

HandleHigherTermMessage(n) ==
    \E m \in BagToSet(messages):
        /\ m["to"] = n
        /\ m["term"] > term[n]
        /\ messages' = messages (-) {m}
        /\ BecomeFollower(n, m["term"])

Next ==
    \/ \E n \in Nodes: Tick(n)
    \/ \E n \in Nodes: Timeout(n)
    \/ \E n \in Nodes: HandlePreVoteRequest(n)
    \/ \E n \in Nodes: HandlePreVoteResponse(n)
    \/ \E n \in Nodes: HandleVoteRequest(n)
    \/ \E n \in Nodes: HandleVoteResponse(n)
    \/ \E v \in Value: ClientRequest(v)
    \/ \E n \in Nodes: ReplicateLog(n)
    \/ \E n \in Nodes: Heartbeat(n)
    \/ \E n \in Nodes: HandleAppendEntriesRequest(n)
    \/ \E n \in Nodes: HandleAppendEntriesResponse(n)
    \/ \E n \in Nodes: HandleHigherTermMessage(n)
    \/ DropMessage

====