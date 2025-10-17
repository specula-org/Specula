---- MODULE etcdraft ----
EXTENDS Naturals, Sequences, FiniteSets, TLC
CONSTANTS Nodes, Keys, Values, Null

VARIABLES state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, kvStore, leader, msgQueue, uncommittedSize

vars == <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, kvStore, leader, msgQueue, uncommittedSize>>

NodeSet == Nodes
None == CHOOSE n : n \notin NodeSet
LocalAppendThread == CHOOSE t : t \notin NodeSet \cup {None}
LocalApplyThread == CHOOSE a : a \notin NodeSet \cup {None, LocalAppendThread}
States == {"Follower", "Candidate", "Leader", "PreCandidate"}
MsgTypes == {"MsgHup", "MsgBeat", "MsgProp", "MsgApp", "MsgAppResp", "MsgVote", "MsgVoteResp", "MsgPreVote", "MsgPreVoteResp", "MsgSnap", "MsgHeartbeat", "MsgHeartbeatResp", "MsgReadIndex", "MsgReadIndexResp", "MsgForgetLeader", "MsgTransferLeader", "MsgTimeoutNow", "MsgStorageAppend", "MsgStorageApply", "MsgStorageAppendResp", "MsgStorageApplyResp", "MsgSnapStatus", "MsgCheckQuorum", "MsgUnreachable"}
ReadOptions == {"ReadOnlySafe", "ReadOnlyLeaseBased"}
CampaignTypes == {"CampaignPreElection", "CampaignElection", "CampaignTransfer"}
OpTypes == {"Put", "Get", "Delete"}

IsLocalMsgTarget(t) == t \in {LocalAppendThread, LocalApplyThread}

Max(a, b) == IF a > b THEN a ELSE b
Min(a, b) == IF a < b THEN a ELSE b

Init ==
    /\ state = [n \in NodeSet |-> "Follower"]
    /\ currentTerm = [n \in NodeSet |-> 0]
    /\ votedFor = [n \in NodeSet |-> None]
    /\ log = [n \in NodeSet |-> <<>>]
    /\ commitIndex = [n \in NodeSet |-> 0]
    /\ lastApplied = [n \in NodeSet |-> 0]
    /\ nextIndex = [n \in NodeSet |-> [p \in NodeSet |-> 1]]
    /\ matchIndex = [n \in NodeSet |-> [p \in NodeSet |-> 0]]
    /\ kvStore = [n \in NodeSet |-> [k \in Keys |-> Null]]
    /\ leader = [n \in NodeSet |-> None]
    /\ msgQueue = [n \in NodeSet |-> {}]
    /\ uncommittedSize = [n \in NodeSet |-> 0]

TypeOK ==
    /\ state \in [NodeSet -> States]
    /\ currentTerm \in [NodeSet -> Nat]
    /\ votedFor \in [NodeSet -> NodeSet \cup {None}]
    /\ log \in [NodeSet -> Seq([type: OpTypes, term: Nat, index: Nat, key: Keys, value: Values \cup {Null}, clientId: Nat, requestId: Nat])]
    /\ commitIndex \in [NodeSet -> Nat]
    /\ lastApplied \in [NodeSet -> Nat]
    /\ nextIndex \in [NodeSet -> [NodeSet -> Nat]]
    /\ matchIndex \in [NodeSet -> [NodeSet -> Nat]]
    /\ kvStore \in [NodeSet -> [Keys -> Values \cup {Null}]]
    /\ leader \in [NodeSet -> NodeSet \cup {None}]
    /\ msgQueue \in [NodeSet -> SUBSET [type: MsgTypes, from: NodeSet \cup {None}, to: NodeSet \cup {LocalAppendThread, LocalApplyThread}, term: Nat, logTerm: Nat, index: Nat, entries: Seq([type: OpTypes, key: Keys, value: Values \cup {Null}, clientId: Nat, requestId: Nat]), commit: Nat, reject: BOOLEAN, rejectHint: Nat, context: STRING]]
    /\ uncommittedSize \in [NodeSet -> Nat]

TermGte(n, t) == currentTerm[n] >= t
TermEq(n, t) == currentTerm[n] = t
LogTermAt(n, i) == IF i = 0 THEN 0 ELSE IF i <= Len(log[n]) THEN log[n][i].term ELSE 0
LastLogIndex(n) == Len(log[n])
LastLogTerm(n) == LogTermAt(n, LastLogIndex(n))
LogMatch(n, prevIndex, prevTerm) == 
    /\ prevIndex <= LastLogIndex(n)
    /\ LogTermAt(n, prevIndex) = prevTerm

QuorumActive == 
    LET activeNodes == {n \in NodeSet: \E m \in msgQueue[n] : m.type \in {"MsgApp", "MsgHeartbeat", "MsgVote", "MsgPreVote"}}
    IN Cardinality(activeNodes) > Cardinality(NodeSet) \div 2

HasLeader == \E n \in NodeSet: state[n] = "Leader"

IsLeader(n) == state[n] = "Leader"

Promotable(n) == 
    /\ ~IsLeader(n)
    /\ \A p \in NodeSet: matchIndex[p][n] >= commitIndex[n]

BecomeFollower(n, term, lead) ==
    /\ state' = [state EXCEPT ![n] = "Follower"]
    /\ currentTerm' = [currentTerm EXCEPT ![n] = term]
    /\ votedFor' = [votedFor EXCEPT ![n] = None]
    /\ leader' = [leader EXCEPT ![n] = lead]
    /\ uncommittedSize' = [uncommittedSize EXCEPT ![n] = 0]

BecomeCandidate(n) ==
    /\ state' = [state EXCEPT ![n] = "Candidate"]
    /\ currentTerm' = [currentTerm EXCEPT ![n] = currentTerm[n] + 1]
    /\ votedFor' = [votedFor EXCEPT ![n] = n]
    /\ leader' = [leader EXCEPT ![n] = None]

BecomeLeader(n) ==
    /\ state' = [state EXCEPT ![n] = "Leader"]
    /\ leader' = [leader EXCEPT ![n] = n]
    /\ nextIndex' = [nextIndex EXCEPT ![n] = [p \in NodeSet |-> LastLogIndex(n) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![n] = [p \in NodeSet |-> 0]]
    /\ uncommittedSize' = [uncommittedSize EXCEPT ![n] = 0]
    /\ LET newLog == Append(log[n], [type |-> "Put", term |-> currentTerm[n], index |-> LastLogIndex(n)+1, key |-> CHOOSE k \in Keys: TRUE, value |-> Null, clientId |-> 0, requestId |-> 0])
       IN log' = [log EXCEPT ![n] = newLog]

SendMsg(m) == 
    LET queue == msgQueue[m.to] \cup {m}
    IN msgQueue' = [msgQueue EXCEPT ![m.to] = queue]

HandleAppendEntries(n, m) ==
    /\ m.type = "MsgApp"
    /\ msgQueue' = [msgQueue EXCEPT ![n] = msgQueue[n] \ {m}]
    /\ IF m.term < currentTerm[n] 
       THEN SendMsg([type |-> "MsgAppResp", to |-> m.from, from |-> n, term |-> currentTerm[n], index |-> m.index, reject |-> TRUE, rejectHint |-> LastLogIndex(n), logTerm |-> 0, entries |-> <<>>, commit |-> 0, context |-> ""])
       ELSE 
            /\ BecomeFollower(n, m.term, m.from)
            /\ IF LogMatch(n, m.index, m.logTerm)
               THEN LET newLog == IF m.entries /= <<>> THEN log[n] \o m.entries ELSE log[n]
                   IN /\ log' = [log EXCEPT ![n] = newLog]
                      /\ commitIndex' = [commitIndex EXCEPT ![n] = Max(commitIndex[n], Min(m.commit, LastLogIndex(n)))]
                      /\ SendMsg([type |-> "MsgAppResp", to |-> m.from, from |-> n, term |-> currentTerm[n], index |-> LastLogIndex(n), reject |-> FALSE, rejectHint |-> 0, logTerm |-> 0, entries |-> <<>>, commit |-> 0, context |-> ""])
               ELSE SendMsg([type |-> "MsgAppResp", to |-> m.from, from |-> n, term |-> currentTerm[n], index |-> m.index, reject |-> TRUE, rejectHint |-> LastLogIndex(n), logTerm |-> 0, entries |-> <<>>, commit |-> 0, context |-> ""])

HandleVoteRequest(n, m) ==
    /\ m.type \in {"MsgVote", "MsgPreVote"}
    /\ msgQueue' = [msgQueue EXCEPT ![n] = msgQueue[n] \ {m}]
    /\ IF m.term < currentTerm[n] 
       THEN SendMsg([type |-> voteRespMsgType(m.type), to |-> m.from, from |-> n, term |-> currentTerm[n], reject |-> TRUE, index |-> 0, logTerm |-> 0, entries |-> <<>>, commit |-> 0, rejectHint |-> 0, context |-> ""])
       ELSE 
            LET canVote == (votedFor[n] = None \/ votedFor[n] = m.from) /\ LastLogIndex(n) <= m.index /\ LastLogTerm(n) <= m.logTerm
            IN IF canVote
               THEN /\ votedFor' = [votedFor EXCEPT ![n] = m.from]
                    /\ SendMsg([type |-> voteRespMsgType(m.type), to |-> m.from, from |-> n, term |-> currentTerm[n], reject |-> FALSE, index |-> 0, logTerm |-> 0, entries |-> <<>>, commit |-> 0, rejectHint |-> 0, context |-> ""])
               ELSE SendMsg([type |-> voteRespMsgType(m.type), to |-> m.from, from |-> n, term |-> currentTerm[n], reject |-> TRUE, index |-> 0, logTerm |-> 0, entries |-> <<>>, commit |-> 0, rejectHint |-> 0, context |-> ""])

voteRespMsgType(t) == IF t = "MsgVote" THEN "MsgVoteResp" ELSE "MsgPreVoteResp"

ProcessClientOp(n, op) ==
    /\ IsLeader(n)
    /\ LET newIndex == LastLogIndex(n) + 1
           newEntry == [type |-> op.type, term |-> currentTerm[n], index |-> newIndex, key |-> op.key, value |-> op.value, clientId |-> op.clientId, requestId |-> op.requestId]
           newLog == Append(log[n], newEntry)
       IN /\ log' = [log EXCEPT ![n] = newLog]
          /\ msgQueue' = [q \in NodeSet |-> 
                         IF q = n THEN msgQueue[q] 
                         ELSE msgQueue[q] \cup {[type |-> "MsgApp", to |-> q, from |-> n, term |-> currentTerm[n], index |-> LastLogIndex(n), logTerm |-> LastLogTerm(n), entries |-> <<newEntry>>, commit |-> commitIndex[n], reject |-> FALSE, rejectHint |-> 0, context |-> ""]} ]

ApplyCommitted(n) ==
    /\ lastApplied[n] < commitIndex[n]
    /\ LET idx == lastApplied[n] + 1
           entry == log[n][idx]
       IN /\ lastApplied' = [lastApplied EXCEPT ![n] = idx]
          /\ IF entry.type = "Put" 
             THEN kvStore' = [kvStore EXCEPT ![n][entry.key] = entry.value]
             ELSE IF entry.type = "Delete"
                  THEN kvStore' = [kvStore EXCEPT ![n][entry.key] = Null]

ReplicateLog(n) ==
    /\ IsLeader(n)
    /\ msgQueue' = [q \in NodeSet |-> 
                   IF q = n THEN msgQueue[q] 
                   ELSE LET prevIndex == nextIndex[n][q] - 1
                            prevTerm == LogTermAt(n, prevIndex)
                            entries == SubSeq(log[n], nextIndex[n][q], LastLogIndex(n))
                        IN msgQueue[q] \cup {[type |-> "MsgApp", to |-> q, from |-> n, term |-> currentTerm[n], index |-> prevIndex, logTerm |-> prevTerm, entries |-> entries, commit |-> commitIndex[n], reject |-> FALSE, rejectHint |-> 0, context |-> ""]} ]

HandleReadIndex(n, m) ==
    /\ m.type = "MsgReadIndex"
    /\ IsLeader(n)
    /\ LET readCtx == m.context
       IN msgQueue' = [q \in NodeSet |->
                       IF q = n
                       THEN msgQueue[q] \ {m}
                       ELSE msgQueue[q] \cup {[type |-> "MsgHeartbeat", to |-> q, from |-> n, term |-> currentTerm[n], context |-> readCtx, logTerm |-> 0, index |-> 0, entries |-> <<>>, commit |-> 0, reject |-> FALSE, rejectHint |-> 0]} ]

Next ==
    \E n \in NodeSet:
        \/ \E m \in msgQueue[n]:
            \/ HandleAppendEntries(n, m)
            \/ HandleVoteRequest(n, m)
            \/ HandleReadIndex(n, m)
        \/ \E op \in [type: OpTypes, key: Keys, value: Values \cup {Null}, clientId: Nat, requestId: Nat]:
            ProcessClientOp(n, op)
        \/ ApplyCommitted(n)
        \/ ReplicateLog(n)
        \/ \E t \in {"MsgHup", "MsgBeat"}:
            LET m == [type |-> t, from |-> n]
            IN IF m.type = "MsgHup" /\ state[n] = "Follower" THEN BecomeCandidate(n)
               ELSE IF m.type = "MsgBeat" /\ state[n] = "Leader" THEN ReplicateLog(n) 

Spec == Init /\ [][Next]_vars

Termination ==
    WF_vars(Next)

LeaderCompleteness ==
    \A n1, n2 \in NodeSet:
        \A idx \in 1..Len(log[n1]):
            IF idx <= commitIndex[n1] /\ state[n1] = "Leader"
            THEN \E S \in SUBSET NodeSet:
                    /\ Cardinality(S) > Cardinality(NodeSet) \div 2
                    /\ \A n3 \in S: idx <= Len(log[n3]) /\ log[n3][idx] = log[n1][idx]

StateMachineSafety ==
    \A n1, n2 \in NodeSet, idx \in 1..Min(LastLogIndex(n1), LastLogIndex(n2)):
        IF idx <= lastApplied[n1] /\ idx <= lastApplied[n2]
        THEN kvStore[n1][log[n1][idx].key] = kvStore[n2][log[n2][idx].key]

ElectionSafety ==
    \A t \in Nat:
        Cardinality({n \in NodeSet: state[n] = "Leader" /\ currentTerm[n] = t}) <= 1

LinearizableReads ==
    \A n \in NodeSet:
        \A m \in {msg \in msgQueue[n]: msg.type = "MsgReadIndexResp"}:
            \E idx \in 1..commitIndex[leader[n]]:
                m.index = idx /\ \A k \in Keys: kvStore[n][k] = kvStore[leader[n]][k]

====