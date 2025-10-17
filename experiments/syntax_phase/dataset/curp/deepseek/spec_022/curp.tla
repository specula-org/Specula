---- MODULE curp ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Replicas, Clients, Keys, Values, MaxSeqNum

(* Assume Commands is Keys × Values *)
Commands == Keys × Values
Key(cmd) == cmd[1]

ProposeId == Clients × (1..MaxSeqNum)

VARIABLES leaderId, term, committedIndex, committedCommands, specPool, uncommPool, clientTrackers, clientSeq

vars == <<leaderId, term, committedIndex, committedCommands, specPool, uncommPool, clientTrackers, clientSeq>>

Init == 
    /\ leaderId \notin Replicas
    /\ term = 0
    /\ committedIndex = 0
    /\ committedCommands = {}
    /\ specPool = [r \in Replicas |-> {}]
    /\ uncommPool = [r \in Replicas |-> {}]
    /\ clientTrackers = [r \in Replicas |-> [c \in Clients |-> 0]]
    /\ clientSeq = [c \in Clients |-> 0]

Propose(client, cmd) == 
    /\ clientSeq[client] < MaxSeqNum
    /\ LET s == clientSeq[client] + 1 IN
       ( clientSeq' = [clientSeq EXCEPT ![client] = s]
         /\ \A r \in Replicas : 
              IF s > clientTrackers[r][client] /\ \neg (\E pid_c \in specPool[r] : Key(pid_c[2]) = Key(cmd))
              THEN /\ specPool' = [specPool EXCEPT ![r] = specPool[r] \cup { <<client, s>>, cmd }]
                   /\ clientTrackers' = [clientTrackers EXCEPT ![r] = [clientTrackers[r] EXCEPT ![client] = s]]
              ELSE UNCHANGED <<specPool, clientTrackers>>
       )
    /\ UNCHANGED <<leaderId, term, committedIndex, committedCommands, uncommPool>>

ProcessProposeLeader(r, cmd) == 
    /\ leaderId = r
    /\ \E pid \in ProposeId : 
        /\ <<pid, cmd>> \in specPool[r]
        /\ LET conflict == (\E pid2_c2 \in specPool[r] : Key(pid2_c2[2]) = Key(cmd) /\ pid2_c2[1] # pid) \/ 
                         (\E pid2_c2 \in uncommPool[r] : Key(pid2_c2[2]) = Key(cmd))
        IN
        IF conflict
        THEN UNCHANGED <<specPool, uncommPool>>
        ELSE /\ uncommPool' = [uncommPool EXCEPT ![r] = uncommPool[r] \cup {<<pid, cmd>>}]
             /\ UNCHANGED <<specPool>>
    /\ UNCHANGED <<leaderId, term, committedIndex, committedCommands, clientTrackers, clientSeq>>

Commit == 
    \E pid \in ProposeId, cmd \in Commands : 
        /\ \E r \in Replicas : <<pid, cmd>> \in uncommPool[r]
        /\ committedIndex' = committedIndex + 1
        /\ committedCommands' = committedCommands \cup {pid}
        /\ UNCHANGED <<leaderId, term, specPool, uncommPool, clientTrackers, clientSeq>>

ProcessCommitMsg(r) == 
    /\ specPool' = [specPool EXCEPT ![r] = { pid_c \in specPool[r] : pid_c[1] \notin committedCommands }]
    /\ UNCHANGED <<leaderId, term, committedIndex, committedCommands, uncommPool, clientTrackers, clientSeq>>

LeaderChange(l) == 
    /\ leaderId' = l
    /\ term' = term + 1
    /\ LET N == Cardinality(Replicas) IN
       LET Quorum == N \div 2 + 1 IN
       LET RecoverQuorum == Quorum \div 2 + 1 IN
       LET otherReplicas == Replicas \ {l} IN
       LET recoveredSet == { pid_c \in ProposeId \times Commands : 
                             Cardinality({r \in otherReplicas : pid_c \in specPool[r]}) >= RecoverQuorum }
       IN
       /\ specPool' = [specPool EXCEPT ![l] = recoveredSet]
       /\ uncommPool' = [uncommPool EXCEPT ![l] = recoveredSet]
       /\ UNCHANGED <<committedIndex, committedCommands, clientTrackers, clientSeq>>

Next == 
    \/ \E client \in Clients, cmd \in Commands : Propose(client, cmd)
    \/ \E r \in Replicas, cmd \in Commands : ProcessProposeLeader(r, cmd)
    \/ Commit
    \/ \E r \in Replicas : ProcessCommitMsg(r)
    \/ \E l \in Replicas : LeaderChange(l)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====