---- MODULE redisraft ----
EXTENDS TLC, Sequences, Naturals, FiniteSets, Bags

CONSTANTS
    Servers,    \* The set of server IDs, e.g., {"s1", "s2", "s3"}
    Commands,   \* A set of possible client commands
    Nil         \* A value distinct from any server ID

ASSUME /\ IsFiniteSet(Servers)
       /\ IsFiniteSet(Commands)
       /\ Nil \notin Servers

States == {"FOLLOWER", "PRECANDIDATE", "CANDIDATE", "LEADER"}
MsgTypes == {"RequestVote", "RequestVoteResponse", "AppendEntries", "AppendEntriesResponse", "Snapshot"}
LogTypes == {"NORMAL", "ADD_NODE", "REMOVE_NODE"}

VARIABLES
    servers_state,
    messages

vars == <<servers_state, messages>>

\* Helper operators
QuorumSize(nodes) == Cardinality(nodes) \div 2 + 1

LastLogIndex(s_state) == s_state["snapshotLastIndex"] + Len(s_state["log"])

LastLogTerm(s_state) ==
    IF Len(s_state["log"]) = 0 THEN
        s_state["snapshotLastTerm"]
    ELSE
        (s_state["log"][Len(s_state["log"])])["term"]

GetEntry(s_state, index) ==
    IF index > s_state["snapshotLastIndex"] /\ index <= LastLogIndex(s_state) THEN
        s_state["log"][index - s_state["snapshotLastIndex"]]
    ELSE
        [term |-> -1, command |-> "Invalid", type |-> "NORMAL"]

IsUpToDate(candidate_last_term, candidate_last_idx, my_last_term, my_last_idx) ==
    \/ candidate_last_term > my_last_term
    \/ (candidate_last_term = my_last_term /\ candidate_last_idx >= my_last_idx)

\* Initial state of the system
Init ==
    /\ servers_state = [s \in Servers |->
        [
            state |-> "FOLLOWER",
            term |-> 0,
            votedFor |-> Nil,
            log |-> << >>,
            commitIndex |-> 0,
            lastApplied |-> 0,
            nodes |-> Servers,
            leaderId |-> Nil,
            votesGranted |-> {},
            nextIndex |-> [p \in Servers |-> 1],
            matchIndex |-> [p \in Servers |-> 0],
            snapshotLastIndex |-> 0,
            snapshotLastTerm |-> 0,
            snapshotInProgress |-> FALSE
        ]
      ]
    /\ messages = {}

\* State Transitions
BecomeFollower(s, newTerm) ==
    /\ servers_state[s]["state"] # "FOLLOWER" \/ servers_state[s]["term"] # newTerm
    /\ servers_state' = [servers_state EXCEPT
        ![s].state = "FOLLOWER",
        ![s].term = newTerm,
        ![s].votedFor = Nil,
        ![s].leaderId = Nil
    ]
    /\ UNCHANGED messages

BecomePreCandidate(s) ==
    /\ servers_state[s]["state"] \in {"FOLLOWER", "PRECANDIDATE"}
    /\ servers_state' = [servers_state EXCEPT
        ![s].state = "PRECANDIDATE",
        ![s].votesGranted = {s}
    ]
    /\ messages' = messages \cup
        {[ type |-> "RequestVote", from |-> s, to |-> p,
           term |-> servers_state[s]["term"] + 1, prevote |-> TRUE,
           lastLogIndex |-> LastLogIndex(servers_state[s]),
           lastLogTerm |-> LastLogTerm(servers_state[s])
         ] : p \in servers_state[s]["nodes"] \ {s}}

BecomeCandidate(s) ==
    /\ servers_state[s]["state"] \in {"FOLLOWER", "PRECANDIDATE", "CANDIDATE"}
    /\ (LET newTerm = servers_state[s]["term"] + 1 IN
       servers_state' = [servers_state EXCEPT
           ![s].state = "CANDIDATE",
           ![s].term = newTerm,
           ![s].votedFor = s,
           ![s].votesGranted = {s}
       ])
    /\ messages' = messages \cup
        {[ type |-> "RequestVote", from |-> s, to |-> p,
           term |-> servers_state'[s]["term"], prevote |-> FALSE,
           lastLogIndex |-> LastLogIndex(servers_state[s]),
           lastLogTerm |-> LastLogTerm(servers_state[s])
         ] : p \in servers_state[s]["nodes"] \ {s}}

BecomeLeader(s) ==
    /\ servers_state[s]["state"] = "CANDIDATE"
    /\ Cardinality(servers_state[s]["votesGranted"]) >= QuorumSize(servers_state[s]["nodes"])
    /\ LET
        s_state = servers_state[s]
        newLog = Append(s_state["log"], [term |-> s_state["term"], command |-> "NoOp", type |-> "NORMAL"])
        newLastIndex = s_state["snapshotLastIndex"] + Len(newLog)
       IN
        servers_state' = [servers_state EXCEPT
            ![s].state = "LEADER",
            ![s].leaderId = s,
            ![s].log = newLog,
            ![s].nextIndex = [p \in s_state["nodes"] |-> newLastIndex + 1],
            ![s].matchIndex = [p \in s_state["nodes"] |-> IF p = s THEN newLastIndex ELSE 0]
        ]
    /\ UNCHANGED messages

\* Vote Processing
RecvRequestVote(s, msg) ==
    /\ msg \in messages
    /\ msg["type"] = "RequestVote"
    /\ msg["to"] = s
    /\ LET
        s_state = servers_state[s]
        higherTerm = msg["term"] > s_state["term"]
        sameTerm = msg["term"] = s_state["term"]
        canVote = s_state["votedFor"] = Nil \/ s_state["votedFor"] = msg["from"]
        logOK = IsUpToDate(msg["lastLogTerm"], msg["lastLogIndex"], LastLogTerm(s_state), LastLogIndex(s_state))
        grant = \/ (msg["term"] > s_state["term"] /\ logOK)
                \/ (msg["term"] = s_state["term"] /\ canVote /\ logOK)
        isPreVote = msg["prevote"]
        newState = [servers_state EXCEPT
            ![s].term = IF higherTerm THEN msg["term"] ELSE s_state["term"],
            ![s].state = IF higherTerm THEN "FOLLOWER" ELSE s_state["state"],
            ![s].votedFor = IF higherTerm THEN Nil
                             ELSE IF grant /\ \neg isPreVote THEN msg["from"]
                             ELSE s_state["votedFor"]
        ]
       IN
        servers_state' = newState
        /\ messages' = (messages \ {msg}) \cup
            {[ type |-> "RequestVoteResponse", from |-> s, to |-> msg["from"],
               term |-> newState[s]["term"], voteGranted |-> grant, prevote |-> isPreVote,
               requestTerm |-> msg["term"]
             ]}

RecvRequestVoteResponse(s, msg) ==
    /\ msg \in messages
    /\ msg["type"] = "RequestVoteResponse"
    /\ msg["to"] = s
    /\ LET s_state = servers_state[s] IN
       \/ (msg["prevote"] /\ s_state["state"] = "PRECANDIDATE" /\ msg["requestTerm"] = s_state["term"] + 1)
       \/ (\neg msg["prevote"] /\ s_state["state"] = "CANDIDATE" /\ msg["requestTerm"] = s_state["term"])
    /\ IF msg["term"] > servers_state[s]["term"] THEN
        /\ BecomeFollower(s, msg["term"])
        /\ messages' = messages \ {msg}
       ELSE
        /\ servers_state' = [servers_state EXCEPT
            ![s].votesGranted = IF msg["voteGranted"]
                                THEN s_state["votesGranted"] \cup {msg["from"]}
                                ELSE s_state["votesGranted"]
        ]
        /\ messages' = messages \ {msg}

\* Log Replication
RecvAppendEntries(s, msg) ==
    /\ msg \in messages
    /\ msg["type"] = "AppendEntries"
    /\ msg["to"] = s
    /\ LET s_state = servers_state[s] IN
       \/ /\ msg["term"] < s_state["term"]
          /\ servers_state' = servers_state
          /\ messages' = (messages \ {msg}) \cup
              {[ type |-> "AppendEntriesResponse", from |-> s, to |-> msg["from"],
                 term |-> s_state["term"], success |-> FALSE, current_idx |-> LastLogIndex(s_state)
               ]}
       \/ /\ msg["term"] >= s_state["term"]
          /\ LET
                new_s_state_term = [s_state EXCEPT !.term = msg["term"], !.state = "FOLLOWER", !.leaderId = msg["from"]]
                current_s_state = IF msg["term"] > s_state["term"] THEN new_s_state_term ELSE [s_state EXCEPT !.leaderId = msg["from"]]
                prevEntry = GetEntry(current_s_state, msg["prevLogIndex"])
                logOK = msg["prevLogIndex"] = 0 \/ (prevEntry["term"] # -1 /\ prevEntry["term"] = msg["prevLogTerm"])
                firstConflict = CHOOSE i \in 1..Len(msg["entries"]) :
                                    (LET idx = msg["prevLogIndex"] + i IN
                                    GetEntry(current_s_state, idx)["term"] # -1 /\ GetEntry(current_s_state, idx)["term"] # msg["entries"][i]["term"])
                newLog = IF logOK THEN
                            IF firstConflict = Nil THEN
                                Append(current_s_state["log"], msg["entries"])
                            ELSE
                                Append(SubSeq(current_s_state["log"], 1, msg["prevLogIndex"] + firstConflict - 1 - current_s_state["snapshotLastIndex"]),
                                       SubSeq(msg["entries"], firstConflict, Len(msg["entries"])))
                         ELSE current_s_state["log"]
                final_s_state = [current_s_state EXCEPT !.log = newLog]
                final_s_state_committed = [final_s_state EXCEPT
                    !.commitIndex = IF logOK THEN max(final_s_state["commitIndex"], min(msg["leaderCommit"], LastLogIndex(final_s_state)))
                                    ELSE final_s_state["commitIndex"]
                ]
             IN
             servers_state' = [servers_state EXCEPT ![s] = final_s_state_committed]
             /\ messages' = (messages \ {msg}) \cup
                 {[ type |-> "AppendEntriesResponse", from |-> s, to |-> msg["from"],
                    term |-> servers_state'[s]["term"], success |-> logOK,
                    current_idx |-> IF logOK THEN LastLogIndex(servers_state'[s]) ELSE LastLogIndex(s_state)
                  ]}

RecvAppendEntriesResponse(s, msg) ==
    /\ msg \in messages
    /\ msg["type"] = "AppendEntriesResponse"
    /\ msg["to"] = s
    /\ LET s_state = servers_state[s] IN
       /\ s_state["state"] = "LEADER"
       /\ IF msg["term"] > s_state["term"] THEN
            /\ BecomeFollower(s, msg["term"])
            /\ messages' = messages \ {msg}
          ELSE IF msg["term"] = s_state["term"] THEN
            /\ LET peer = msg["from"] IN
               \/ (/\ msg["success"]
                   /\ LET newMatch = max(s_state["matchIndex"][peer], msg["current_idx"])
                          newNext = newMatch + 1
                          newMatches = [s_state["matchIndex"] EXCEPT ![peer] = newMatch]
                          sortedMatches = SortSeq([newMatches[p] : p \in s_state["nodes"]])
                          majorityIdx = sortedMatches[QuorumSize(s_state["nodes"])]
                          newCommitIndex = IF majorityIdx > s_state["commitIndex"] /\ GetEntry(s_state, majorityIdx)["term"] = s_state["term"]
                                           THEN majorityIdx ELSE s_state["commitIndex"]
                      IN servers_state' = [servers_state EXCEPT
                           ![s].matchIndex[peer] = newMatch,
                           ![s].nextIndex[peer] = newNext,
                           ![s].commitIndex = newCommitIndex
                       ])
               \/ (/\ \neg msg["success"]
                   /\ servers_state' = [servers_state EXCEPT ![s].nextIndex[peer] = max(1, s_state["nextIndex"][peer] - 1)])
            /\ messages' = messages \ {msg}
          ELSE
            /\ UNCHANGED vars

\* Leader Operations
SendAppendEntries(s, peer) ==
    /\ LET s_state = servers_state[s] IN
       /\ s_state["state"] = "LEADER"
       /\ peer \in s_state["nodes"] \ {s}
       /\ LET
            next = s_state["nextIndex"][peer]
            prevIdx = next - 1
            prevTerm = IF prevIdx = s_state["snapshotLastIndex"] THEN s_state["snapshotLastTerm"]
                       ELSE IF prevIdx > s_state["snapshotLastIndex"] THEN GetEntry(s_state, prevIdx)["term"]
                       ELSE 0
            entries = SubSeq(s_state["log"], next - s_state["snapshotLastIndex"], Len(s_state["log"]))
          IN
            /\ messages' = messages \cup
                {[ type |-> "AppendEntries", from |-> s, to |-> peer,
                   term |-> s_state["term"], leaderId |-> s,
                   prevLogIndex |-> prevIdx, prevLogTerm |-> prevTerm,
                   entries |-> entries, leaderCommit |-> s_state["commitIndex"]
                 ]}
    /\ UNCHANGED servers_state

\* Election Management
ElectionStart(s) ==
    \/ BecomePreCandidate(s)
    \/ BecomeCandidate(s)

ElectionTimeout(s) ==
    /\ servers_state[s]["state"] \in {"FOLLOWER", "CANDIDATE", "PRECANDIDATE"}
    /\ ElectionStart(s)

\* Log Management
LogAppend(s, cmd, type) ==
    /\ LET s_state = servers_state[s] IN
       /\ s_state["state"] = "LEADER"
       /\ cmd \in Commands \cup {"NoOp"}
       /\ type \in LogTypes
       /\ LET newEntry = [term |-> s_state["term"], command |-> cmd, type |-> type] IN
          servers_state' = [servers_state EXCEPT ![s].log = Append(s_state["log"], newEntry)]
    /\ UNCHANGED messages

LogCommit(s) ==
    /\ LET s_state = servers_state[s] IN
       /\ s_state["commitIndex"] > s_state["lastApplied"]
       /\ LET idxToApply = s_state["lastApplied"] + 1 IN
       /\ LET entry = GetEntry(s_state, idxToApply) IN
          /\ servers_state' = [servers_state EXCEPT
                ![s].lastApplied = idxToApply,
                ![s].nodes = IF entry["type"] = "ADD_NODE" THEN s_state["nodes"] \cup {entry["command"]}
                          ELSE IF entry["type"] = "REMOVE_NODE" THEN s_state["nodes"] \ {entry["command"]}
                          ELSE s_state["nodes"]
             ]
    /\ UNCHANGED messages

\* Node Management
AddNode(s, newNode) == LogAppend(s, newNode, "ADD_NODE")
RemoveNode(s, oldNode) == LogAppend(s, oldNode, "REMOVE_NODE")

\* Snapshot Handling
SnapshotBegin(s) ==
    /\ LET s_state = servers_state[s] IN
       /\ s_state["commitIndex"] > s_state["snapshotLastIndex"]
       /\ \neg s_state["snapshotInProgress"]
       /\ servers_state' = [servers_state EXCEPT ![s].snapshotInProgress = TRUE]
    /\ UNCHANGED messages

SnapshotEnd(s) ==
    /\ LET s_state = servers_state[s] IN
       /\ s_state["snapshotInProgress"]
       /\ LET
            newSnapshotLastIndex = s_state["commitIndex"]
            newSnapshotLastTerm = GetEntry(s_state, newSnapshotLastIndex)["term"]
            firstKept = newSnapshotLastIndex - s_state["snapshotLastIndex"] + 1
            newLog = IF firstKept > Len(s_state["log"]) THEN << >> ELSE SubSeq(s_state["log"], firstKept, Len(s_state["log"]))
          IN
            servers_state' = [servers_state EXCEPT
                ![s].snapshotInProgress = FALSE,
                ![s].snapshotLastIndex = newSnapshotLastIndex,
                ![s].snapshotLastTerm = newSnapshotLastTerm,
                ![s].log = newLog
            ]
    /\ UNCHANGED messages

SendSnapshot(s, peer) ==
    /\ LET s_state = servers_state[s] IN
       /\ s_state["state"] = "LEADER"
       /\ peer \in s_state["nodes"] \ {s}
       /\ s_state["nextIndex"][peer] <= s_state["snapshotLastIndex"]
       /\ messages' = messages \cup
           {[ type |-> "Snapshot", from |-> s, to |-> peer,
              term |-> s_state["term"], leaderId |-> s,
              lastIncludedIndex |-> s_state["snapshotLastIndex"],
              lastIncludedTerm |-> s_state["snapshotLastTerm"]
            ]}
    /\ servers_state' = [servers_state EXCEPT ![s].nextIndex[peer] = s_state["snapshotLastIndex"] + 1]

RecvSnapshot(s, msg) ==
    /\ msg \in messages
    /\ msg["type"] = "Snapshot"
    /\ msg["to"] = s
    /\ LET s_state = servers_state[s] IN
       /\ msg["term"] >= s_state["term"]
       /\ LET
            new_s_state_term = [s_state EXCEPT !.term = msg["term"], !.state = "FOLLOWER", !.leaderId = msg["from"]]
            current_s_state = IF msg["term"] > s_state["term"] THEN new_s_state_term ELSE [s_state EXCEPT !.leaderId = msg["from"]]
            updated_s_state =
                IF msg["lastIncludedIndex"] > current_s_state["snapshotLastIndex"] THEN
                    LET
                        lastLogIdx = LastLogIndex(current_s_state)
                        newLog = IF msg["lastIncludedIndex"] >= lastLogIdx THEN << >>
                                 ELSE SubSeq(current_s_state["log"], msg["lastIncludedIndex"] - current_s_state["snapshotLastIndex"] + 1, Len(current_s_state["log"]))
                    IN
                        [current_s_state EXCEPT
                            !.snapshotLastIndex = msg["lastIncludedIndex"],
                            !.snapshotLastTerm = msg["lastIncludedTerm"],
                            !.log = newLog,
                            !.commitIndex = max(current_s_state["commitIndex"], msg["lastIncludedIndex"]),
                            !.lastApplied = max(current_s_state["lastApplied"], msg["lastIncludedIndex"])
                        ]
                ELSE
                    current_s_state
          IN
            servers_state' = [servers_state EXCEPT ![s] = updated_s_state]
    /\ messages' = messages \ {msg}

Next ==
    \/ \E s \in Servers :
        \/ BecomeLeader(s)
        \/ ElectionTimeout(s)
        \/ LogCommit(s)
        \/ SnapshotBegin(s)
        \/ SnapshotEnd(s)
    \/ \E s \in Servers, p \in servers_state[s]["nodes"] :
        \/ SendAppendEntries(s, p)
        \/ SendSnapshot(s, p)
    \/ \E s \in Servers, cmd \in Commands:
        \/ LogAppend(s, cmd, "NORMAL")
        \/ AddNode(s, cmd)    \* Using Commands to represent new node IDs for simplicity
        \/ RemoveNode(s, cmd) \* Using Commands to represent old node IDs for simplicity
    \/ \E s \in Servers, msg \in messages:
        \/ RecvRequestVote(s, msg)
        \/ RecvRequestVoteResponse(s, msg)
        \/ RecvAppendEntries(s, msg)
        \/ RecvAppendEntriesResponse(s, msg)
        \/ RecvSnapshot(s, msg)

Spec == Init /\ [][Next]_vars

====