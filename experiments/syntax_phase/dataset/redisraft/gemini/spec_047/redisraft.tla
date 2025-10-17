---- MODULE redisraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Server, None

\* FIX: The TLC error 'ConfigFileException' is caused by an invalid expression for 'Value'
\* in the .cfg file. The fix is to define 'Value' as an operator within the specification
\* itself, instead of declaring it as a CONSTANT that requires an assignment in the
\* configuration file. The corresponding invalid assignment must be removed from the .cfg file.
Value == Server \cup {"some_data"}

ASSUME IsFiniteSet(Server)
ASSUME None \notin Server

VARIABLES
    state,
    currentTerm,
    votedFor,
    log,
    commitIndex,
    lastApplied,
    nodes,
    leaderId,
    snapshot_last_idx,
    snapshot_last_term,
    nextIndex,
    matchIndex,
    votesGranted,
    messages

vars == <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nodes, leaderId,
          snapshot_last_idx, snapshot_last_term, nextIndex, matchIndex, votesGranted, messages>>

TypeOK ==
    /\ state \in [Server -> {"FOLLOWER", "PRECANDIDATE", "CANDIDATE", "LEADER"}]
    /\ currentTerm \in [Server -> Nat]
    /\ votedFor \in [Server -> Server \cup {None}]
    /\ \A s \in Server: \A e \in DOMAIN log[s]:
        log[s][e] \in [term: Nat, type: {"Normal", "AddNode", "RemoveNode", "NoOp"}, data: Value]
    /\ commitIndex \in [Server -> Nat]
    /\ lastApplied \in [Server -> Nat]
    /\ nodes \in [Server -> SUBSET Server]
    /\ leaderId \in [Server -> Server \cup {None}]
    /\ snapshot_last_idx \in [Server -> Nat]
    /\ snapshot_last_term \in [Server -> Nat]
    /\ nextIndex \in [Server -> [Server -> Nat]]
    /\ matchIndex \in [Server -> [Server -> Nat]]
    /\ votesGranted \in [Server -> SUBSET Server]

Quorum(s) == (Cardinality(nodes[s]) \div 2) + 1

LastLogIndex(s) == Len(log[s]) + snapshot_last_idx[s]
LastLogTerm(s) == IF Len(log[s]) = 0 THEN snapshot_last_term[s] ELSE (log[s][Len(log[s])]).term
GetEntry(s, idx) ==
    IF idx > snapshot_last_idx[s] /\ idx <= LastLogIndex(s)
    THEN log[s][idx - snapshot_last_idx[s]]
    ELSE [term |-> 0, type |-> "Normal", data |-> None]

IsUpToDate(s, candLogIndex, candLogTerm) ==
    LET myLogIndex == LastLogIndex(s)
        myLogTerm  == LastLogTerm(s)
    IN \/ candLogTerm > myLogTerm
       \/ (candLogTerm = myLogTerm /\ candLogIndex >= myLogIndex)

Init ==
    /\ state = [s \in Server |-> "FOLLOWER"]
    /\ currentTerm = [s \in Server |-> 0]
    /\ votedFor = [s \in Server |-> None]
    /\ log = [s \in Server |-> << >>]
    /\ commitIndex = [s \in Server |-> 0]
    /\ lastApplied = [s \in Server |-> 0]
    /\ nodes = [s \in Server |-> Server]
    /\ leaderId = [s \in Server |-> None]
    /\ snapshot_last_idx = [s \in Server |-> 0]
    /\ snapshot_last_term = [s \in Server |-> 0]
    /\ nextIndex = [s \in Server |-> [p \in Server |-> 1]]
    /\ matchIndex = [s \in Server |-> [p \in Server |-> 0]]
    /\ votesGranted = [s \in Server |-> {}]
    /\ messages = EmptyBag

\* State Transitions (embedded in actions)
BecomeFollower(s, term) ==
    /\ state' = [state EXCEPT ![s] = "FOLLOWER"]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = term]
    /\ votedFor' = [votedFor EXCEPT ![s] = None]
    /\ leaderId' = [leaderId EXCEPT ![s] = None]

BecomePreCandidate(s) ==
    /\ state[s] \in {"FOLLOWER", "CANDIDATE"}
    /\ state' = [state EXCEPT ![s] = "PRECANDIDATE"]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {}]
    /\ messages' = messages \+ Bag({[
            type |-> "RequestVote",
            source |-> s,
            dest |-> p,
            term |-> currentTerm[s] + 1,
            lastLogIndex |-> LastLogIndex(s),
            lastLogTerm |-> LastLogTerm(s),
            prevote |-> TRUE
        ] : p \in nodes[s] \ {s}})
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied, nodes, leaderId,
                   snapshot_last_idx, snapshot_last_term, nextIndex, matchIndex>>

BecomeCandidate(s) ==
    /\ state[s] = "PRECANDIDATE"
    /\ Cardinality(votesGranted[s]) >= Quorum(s)
    /\ LET newTerm == currentTerm[s] + 1
       IN /\ state' = [state EXCEPT ![s] = "CANDIDATE"]
          /\ currentTerm' = [currentTerm EXCEPT ![s] = newTerm]
          /\ votedFor' = [votedFor EXCEPT ![s] = s]
          /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
          /\ leaderId' = [leaderId EXCEPT ![s] = None]
          /\ messages' = messages \+ Bag({[
                type |-> "RequestVote",
                source |-> s,
                dest |-> p,
                term |-> newTerm,
                lastLogIndex |-> LastLogIndex(s),
                lastLogTerm |-> LastLogTerm(s),
                prevote |-> FALSE
            ] : p \in nodes[s] \ {s}})
    /\ UNCHANGED <<log, commitIndex, lastApplied, nodes, snapshot_last_idx, snapshot_last_term, nextIndex, matchIndex>>

BecomeLeader(s) ==
    /\ state[s] = "CANDIDATE"
    /\ Cardinality(votesGranted[s]) >= Quorum(s)
    /\ state' = [state EXCEPT ![s] = "LEADER"]
    /\ leaderId' = [leaderId EXCEPT ![s] = s]
    /\ nextIndex' = [nextIndex EXCEPT ![s] = [p \in Server |-> LastLogIndex(s) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![s] = [p \in Server |-> 0]]
    /\ log' = [log EXCEPT ![s] = Append(log[s], [term |-> currentTerm[s], type |-> "NoOp", data |-> None])]
    /\ UNCHANGED <<currentTerm, votedFor, commitIndex, lastApplied, nodes,
                   snapshot_last_idx, snapshot_last_term, votesGranted, messages>>

\* Vote Processing
RecvRequestVote(s) ==
    \E msg \in BagToSet(messages):
        /\ msg.type = "RequestVote"
        /\ msg.dest = s
        /\ LET candTerm = msg.term
               cand = msg.source
               grant = IF candTerm < currentTerm[s]
                       THEN FALSE
                       ELSE IF candTerm > currentTerm[s]
                            THEN IsUpToDate(s, msg.lastLogIndex, msg.lastLogTerm)
                            ELSE (votedFor[s] \in {None, cand}) /\ IsUpToDate(s, msg.lastLogIndex, msg.lastLogTerm)
               responseTerm = IF candTerm > currentTerm[s] THEN candTerm ELSE currentTerm[s]
               response(granted) == [type |-> "RequestVoteResponse", source |-> s, dest |-> cand,
                                     term |-> responseTerm, vote_granted |-> granted, prevote |-> msg.prevote,
                                     request_term |-> msg.term]
           IN \/ /\ grant
                 /\ \lnot msg.prevote
                 /\ BecomeFollower(s, responseTerm)
                 /\ votedFor' = [votedFor EXCEPT ![s] = cand]
                 /\ messages' = (messages \- {msg}) \+ {response(TRUE)}
                 /\ UNCHANGED <<log, commitIndex, lastApplied, nodes, snapshot_last_idx,
                                snapshot_last_term, nextIndex, matchIndex, votesGranted>>
              \/ /\ grant
                 /\ msg.prevote
                 /\ messages' = (messages \- {msg}) \+ {response(TRUE)}
                 /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nodes, leaderId,
                                snapshot_last_idx, snapshot_last_term, nextIndex, matchIndex, votesGranted>>
              \/ /\ \lnot grant
                 /\ messages' = (messages \- {msg}) \+ {response(FALSE)}
                 /\ IF candTerm > currentTerm[s]
                    THEN /\ BecomeFollower(s, candTerm)
                         /\ UNCHANGED <<votedFor, log, commitIndex, lastApplied, nodes, snapshot_last_idx,
                                        snapshot_last_term, nextIndex, matchIndex, votesGranted>>
                    ELSE UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nodes, leaderId,
                                     snapshot_last_idx, snapshot_last_term, nextIndex, matchIndex, votesGranted>>

RecvRequestVoteResponse(s) ==
    \E msg \in BagToSet(messages):
        /\ msg.type = "RequestVoteResponse"
        /\ msg.dest = s
        /\ messages' = messages \- {msg}
        /\ IF msg.term > currentTerm[s]
           THEN /\ BecomeFollower(s, msg.term)
                /\ UNCHANGED <<votedFor, log, commitIndex, lastApplied, nodes, snapshot_last_idx,
                               snapshot_last_term, nextIndex, matchIndex, votesGranted>>
           ELSE /\ LET validPreVote = state[s] = "PRECANDIDATE" /\ msg.prevote /\ msg.request_term = currentTerm[s] + 1
                      validVote = state[s] = "CANDIDATE" /\ \lnot msg.prevote /\ msg.request_term = currentTerm[s]
                  IN IF (validPreVote \/ validVote) /\ msg.vote_granted
                     THEN votesGranted' = [votesGranted EXCEPT ![s] = votesGranted[s] \cup {msg.source}]
                     ELSE UNCHANGED votesGranted
                /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nodes, leaderId,
                               snapshot_last_idx, snapshot_last_term, nextIndex, matchIndex>>

\* Log Replication
RecvAppendEntries(s) ==
    \E msg \in BagToSet(messages):
        /\ msg.type = "AppendEntries"
        /\ msg.dest = s
        /\ LET reqTerm = msg.term
               pli = msg.prevLogIndex
               plt = msg.prevLogTerm
               success = \/ reqTerm < currentTerm[s]
                         \/ pli > LastLogIndex(s)
                         \/ (pli > snapshot_last_idx[s] /\ GetEntry(s, pli).term /= plt)
                         \/ (pli = snapshot_last_idx[s] /\ plt /= snapshot_last_term[s])
               response(ok) = [type |-> "AppendEntriesResponse", source |-> s, dest |-> msg.source,
                               term |-> currentTerm[s], success |-> ok, current_idx |-> LastLogIndex(s)]
           IN \/ /\ \lnot success
                 /\ state' = [state EXCEPT ![s] = "FOLLOWER"]
                 /\ leaderId' = [leaderId EXCEPT ![s] = msg.source]
                 /\ LET conflictIdx = CHOOSE i \in 1..Len(msg.entries) :
                                        pli + i > LastLogIndex(s) \/ GetEntry(s, pli + i).term /= msg.entries[i].term
                    IN log' = [log EXCEPT ![s] =
                                Append(SubSeq(log[s], 1, pli - snapshot_last_idx[s]),
                                       SubSeq(msg.entries, 1, Len(msg.entries)))]
                 /\ commitIndex' = [commitIndex EXCEPT ![s] = max(commitIndex[s], min(msg.leaderCommit, LastLogIndex(s)))]
                 /\ messages' = (messages \- {msg}) \+ {response(TRUE)}
                 /\ UNCHANGED <<currentTerm, votedFor, lastApplied, nodes, snapshot_last_idx,
                                snapshot_last_term, nextIndex, matchIndex, votesGranted>>
              \/ /\ success
                 /\ messages' = (messages \- {msg}) \+ {response(FALSE)}
                 /\ IF reqTerm > currentTerm[s]
                    THEN /\ BecomeFollower(s, reqTerm)
                         /\ UNCHANGED <<votedFor, log, commitIndex, lastApplied, nodes, snapshot_last_idx,
                                        snapshot_last_term, nextIndex, matchIndex, votesGranted>>
                    ELSE UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nodes, leaderId,
                                     snapshot_last_idx, snapshot_last_term, nextIndex, matchIndex, votesGranted>>

RecvAppendEntriesResponse(s) ==
    \E msg \in BagToSet(messages):
        /\ msg.type = "AppendEntriesResponse"
        /\ msg.dest = s
        /\ state[s] = "LEADER"
        /\ messages' = messages \- {msg}
        /\ IF msg.term > currentTerm[s]
           THEN /\ BecomeFollower(s, msg.term)
                /\ UNCHANGED <<votedFor, log, commitIndex, lastApplied, nodes, snapshot_last_idx,
                               snapshot_last_term, nextIndex, matchIndex, votesGranted>>
           ELSE /\ IF msg.success
                  THEN /\ nextIndex' = [nextIndex EXCEPT ![s][msg.source] = msg.current_idx + 1]
                       /\ matchIndex' = [matchIndex EXCEPT ![s][msg.source] = msg.current_idx]
                       /\ LET newCommitIndex =
                                LET possible = {i \in commitIndex[s]+1 .. LastLogIndex(s) |
                                                /\ GetEntry(s, i).term = currentTerm[s]
                                                /\ Cardinality({p \in nodes[s] | matchIndex[s][p] >= i}) >= Quorum(s)}
                                IN IF possible = {} THEN commitIndex[s] ELSE Max(possible)
                          IN commitIndex' = [commitIndex EXCEPT ![s] = newCommitIndex]
                  ELSE /\ nextIndex' = [nextIndex EXCEPT ![s][msg.source] = nextIndex[s][msg.source] - 1]
                       /\ UNCHANGED <<matchIndex, commitIndex>>
                /\ UNCHANGED <<state, currentTerm, votedFor, log, lastApplied, nodes, leaderId,
                               snapshot_last_idx, snapshot_last_term, votesGranted>>

\* Leader Operations
SendAppendEntries(s) ==
    /\ state[s] = "LEADER"
    /\ \E peer \in nodes[s] \ {s}:
        /\ LET next = nextIndex[s][peer]
           IN /\ next > snapshot_last_idx[s]
              /\ LET prevTerm = IF next - 1 = snapshot_last_idx[s]
                                THEN snapshot_last_term[s]
                                ELSE GetEntry(s, next - 1).term
                     entriesToSend = SubSeq(log[s], next - snapshot_last_idx[s], Len(log[s]))
                     msg = [type |-> "AppendEntries", source |-> s, dest |-> peer, term |-> currentTerm[s],
                            leaderId |-> s, prevLogIndex |-> next - 1, prevLogTerm |-> prevTerm,
                            entries |-> entriesToSend, leaderCommit |-> commitIndex[s]]
                 IN messages' = messages \+ {msg}
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nodes, leaderId,
                   snapshot_last_idx, snapshot_last_term, nextIndex, matchIndex, votesGranted>>

SendHeartbeat(s) ==
    /\ state[s] = "LEADER"
    /\ \E peer \in nodes[s] \ {s}:
        /\ LET next = nextIndex[s][peer]
           IN /\ next > LastLogIndex(s)
              /\ LET prevTerm = LastLogTerm(s)
                     msg = [type |-> "AppendEntries", source |-> s, dest |-> peer, term |-> currentTerm[s],
                            leaderId |-> s, prevLogIndex |-> LastLogIndex(s), prevLogTerm |-> prevTerm,
                            entries |-> << >>, leaderCommit |-> commitIndex[s]]
                 IN messages' = messages \+ {msg}
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nodes, leaderId,
                   snapshot_last_idx, snapshot_last_term, nextIndex, matchIndex, votesGranted>>

\* Election Management
ElectionStart(s) == BecomePreCandidate(s)
ElectionTimeout(s) == ElectionStart(s)

\* Log Management
LogAppend(s) ==
    /\ state[s] = "LEADER"
    /\ \/ LET newEntry = [term |-> currentTerm[s], type |-> "Normal", data |-> "some_data"]
          IN log' = [log EXCEPT ![s] = Append(log[s], newEntry)]
       \/ \E newNode \in Server \ nodes[s] :
          LET newEntry = [term |-> currentTerm[s], type |-> "AddNode", data |-> newNode]
          IN log' = [log EXCEPT ![s] = Append(log[s], newEntry)]
       \/ \E oldNode \in nodes[s] \ {s} :
          LET newEntry = [term |-> currentTerm[s], type |-> "RemoveNode", data |-> oldNode]
          IN log' = [log EXCEPT ![s] = Append(log[s], newEntry)]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, nodes, leaderId,
                   snapshot_last_idx, snapshot_last_term, nextIndex, matchIndex, votesGranted, messages>>

LogDelete(s) == FALSE \* Handled in RecvAppendEntries
LogCommit(s) == FALSE \* Handled in RecvAppendEntriesResponse

\* Periodic Tasks
PeriodicElectionTimeout(s) == ElectionTimeout(s)
PeriodicHeartbeat(s) == SendHeartbeat(s)

\* Node Management
AddNode(s) == FALSE \* Handled by LogAppend and ApplyConfigChange
RemoveNode(s) == FALSE \* Handled by LogAppend and ApplyConfigChange

\* Snapshot Handling
SnapshotBegin(s) ==
    /\ state[s] = "LEADER"
    /\ commitIndex[s] > snapshot_last_idx[s]
    /\ \E new_snap_idx \in snapshot_last_idx[s]+1 .. commitIndex[s]:
        /\ LET new_snap_term = GetEntry(s, new_snap_idx).term
           IN /\ snapshot_last_idx' = [snapshot_last_idx EXCEPT ![s] = new_snap_idx]
              /\ snapshot_last_term' = [snapshot_last_term EXCEPT ![s] = new_snap_term]
              /\ log' = [log EXCEPT ![s] = SubSeq(log[s], new_snap_idx - snapshot_last_idx[s] + 1, Len(log[s]))]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, nodes, leaderId,
                   nextIndex, matchIndex, votesGranted, messages>>

SnapshotEnd(s) == FALSE \* Combined with SnapshotBegin

SendSnapshot(s) ==
    /\ state[s] = "LEADER"
    /\ \E peer \in nodes[s] \ {s}:
        /\ nextIndex[s][peer] <= snapshot_last_idx[s]
        /\ LET msg = [type |-> "InstallSnapshot", source |-> s, dest |-> peer, term |-> currentTerm[s],
                      last_idx |-> snapshot_last_idx[s], last_term |-> snapshot_last_term[s]]
           IN messages' = messages \+ {msg}
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nodes, leaderId,
                   snapshot_last_idx, snapshot_last_term, nextIndex, matchIndex, votesGranted>>

RecvSnapshot(s) ==
    \E msg \in BagToSet(messages):
        /\ msg.type = "InstallSnapshot"
        /\ msg.dest = s
        /\ messages' = messages \- {msg}
        /\ IF msg.term < currentTerm[s]
           THEN UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nodes, leaderId,
                            snapshot_last_idx, snapshot_last_term, nextIndex, matchIndex, votesGranted>>
           ELSE /\ IF msg.term > currentTerm[s]
                  THEN BecomeFollower(s, msg.term)
                  ELSE UNCHANGED <<state, currentTerm, leaderId>>
                /\ IF msg.last_idx > commitIndex[s]
                   THEN /\ log' = [log EXCEPT ![s] = << >>]
                        /\ snapshot_last_idx' = [snapshot_last_idx EXCEPT ![s] = msg.last_idx]
                        /\ snapshot_last_term' = [snapshot_last_term EXCEPT ![s] = msg.last_term]
                        /\ commitIndex' = [commitIndex EXCEPT ![s] = msg.last_idx]
                        /\ lastApplied' = [lastApplied EXCEPT ![s] = msg.last_idx]
                   ELSE UNCHANGED <<log, snapshot_last_idx, snapshot_last_term, commitIndex, lastApplied>>
                /\ UNCHANGED <<votedFor, nodes, nextIndex, matchIndex, votesGranted>>

\* Configuration
ApplyConfigChange(s) ==
    /\ commitIndex[s] > lastApplied[s]
    /\ LET idx = lastApplied[s] + 1
           entry = GetEntry(s, idx)
       IN /\ lastApplied' = [lastApplied EXCEPT ![s] = idx]
          /\ IF entry.type = "AddNode"
             THEN nodes' = [nodes EXCEPT ![s] = nodes[s] \cup {entry.data}]
             ELSE IF entry.type = "RemoveNode"
                  THEN nodes' = [nodes EXCEPT ![s] = nodes[s] \ {entry.data}]
                  ELSE UNCHANGED nodes
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leaderId,
                   snapshot_last_idx, snapshot_last_term, nextIndex, matchIndex, votesGranted, messages>>

Next ==
    \/ \E s \in Server:
        \/ PeriodicElectionTimeout(s)
        \/ BecomeCandidate(s)
        \/ BecomeLeader(s)
        \/ RecvRequestVote(s)
        \/ RecvRequestVoteResponse(s)
        \/ RecvAppendEntries(s)
        \/ RecvAppendEntriesResponse(s)
        \/ PeriodicHeartbeat(s)
        \/ SendAppendEntries(s)
        \/ LogAppend(s)
        \/ ApplyConfigChange(s)
        \/ SnapshotBegin(s)
        \/ SendSnapshot(s)
        \/ RecvSnapshot(s)

Spec == Init /\ [][Next]_vars

====