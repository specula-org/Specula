---- MODULE curp ----
EXTENDS TLC, Sequences, Naturals, FiniteSets, Functions

CONSTANTS
    Replicas,       \* The set of server IDs
    Commands,       \* The set of all possible commands
    Keys,           \* The set of all possible keys
    CommandKeys,    \* A function mapping a command to the set of keys it accesses
    Nil             \* A value indicating no leader, not in Replicas

ASSUME Nil \notin Replicas
ASSUME \A cmd \in Commands : IsAFunction(CommandKeys) /\ CommandKeys[cmd] \in SUBSET Keys

VARIABLES
    leaderId,           \* The ID of the current leader replica
    term,               \* The current consensus term
    sp,                 \* Speculative pool for each replica: [replicaId -> SUBSET Commands]
    ucp,                \* The leader's uncommitted pool: SUBSET Commands
    committed,          \* Commands committed by backend, awaiting GC: SUBSET Commands
    pendingProposals,   \* Per-replica buffer of commands from clients: [replicaId -> SUBSET Commands]
    processedCommits    \* Tracks which replica has GC'd which committed command: [replicaId -> SUBSET Commands]

vars == <<leaderId, term, sp, ucp, committed, pendingProposals, processedCommits>>

\* Helper operator for conflict detection
IsConflict(cmd1, cmd2) == CommandKeys[cmd1] \cap CommandKeys[cmd2] /= {}

\* Helper operator for quorum sizes
Quorum(n) == (n \div 2) + 1
RecoverQuorum(n) == (Quorum(n) \div 2) + 1
SuperQuorum(n) == (n - Quorum(n)) + RecoverQuorum(n)

\* Helper operator to find the intersection of a set of sets
Intersect(S) == {x \in UNION S : \A s \in S : x \in s}

TypeOK ==
    /\ leaderId \in Replicas \cup {Nil}
    /\ term \in Nat
    /\ sp \in [Replicas -> SUBSET Commands]
    /\ ucp \in SUBSET Commands
    /\ committed \in SUBSET Commands
    /\ pendingProposals \in [Replicas -> SUBSET Commands]
    /\ processedCommits \in [Replicas -> SUBSET Commands]

Init ==
    /\ leaderId = Nil
    /\ term = 0
    /\ sp = [r \in Replicas |-> {}]
    /\ ucp = {}
    /\ committed = {}
    /\ pendingProposals = [r \in Replicas |-> {}]
    /\ processedCommits = [r \in Replicas |-> {}]

\* 【Client Proposal】A client sends a command to all replicas.
Propose(cmd) ==
    /\ pendingProposals' = [r \in Replicas |-> pendingProposals[r] \cup {cmd}]
    /\ UNCHANGED <<leaderId, term, sp, ucp, committed, processedCommits>>

\* 【Leader Processing】The leader processes a proposed command.
ProcessProposeLeader(r, cmd) ==
    /\ r = leaderId
    /\ cmd \in pendingProposals[r]
    /\ LET hasConflict == \E c \in (sp[r] \cup ucp) : IsConflict(cmd, c) IN
       IF hasConflict THEN
           /\ ucp' = ucp \cup {cmd}
           /\ sp' = sp
       ELSE
           /\ sp' = [sp EXCEPT ![r] = @ \cup {cmd}]
           /\ ucp' = ucp
    /\ pendingProposals' = [pendingProposals EXCEPT ![r] = @ \ {cmd}]
    /\ UNCHANGED <<leaderId, term, committed, processedCommits>>

\* 【Non-leader Processing】A non-leader replica processes a proposed command.
ProcessProposeNonLeader(r, cmd) ==
    /\ r /= leaderId
    /\ r \in Replicas
    /\ cmd \in pendingProposals[r]
    /\ LET hasConflict == \E c \in sp[r] : IsConflict(cmd, c) IN
       IF hasConflict THEN
           /\ sp' = sp
       ELSE
           /\ sp' = [sp EXCEPT ![r] = @ \cup {cmd}]
    /\ pendingProposals' = [pendingProposals EXCEPT ![r] = @ \ {cmd}]
    /\ UNCHANGED <<leaderId, term, ucp, committed, processedCommits>>

\* 【Fast Path Commit】A command is committed via the fast path if a super quorum agrees.
FastPathCommit(cmd) ==
    /\ cmd \notin committed
    /\ cmd \notin ucp
    /\ \E Q \in SUBSET Replicas:
        /\ Cardinality(Q) >= SuperQuorum(Cardinality(Replicas))
        /\ \A r \in Q : cmd \in sp[r]
        /\ \A r \in Q : \A c \in sp[r] \ {cmd} : \lnot IsConflict(cmd, c)
    /\ committed' = committed \cup {cmd}
    /\ UNCHANGED <<leaderId, term, sp, ucp, pendingProposals, processedCommits>>

\* 【Backend Protocol Commit】The backend consensus protocol commits a command from the uncommitted pool (slow path).
Commit(cmd) ==
    /\ cmd \in ucp
    /\ ucp' = ucp \ {cmd}
    /\ committed' = committed \cup {cmd}
    /\ UNCHANGED <<leaderId, term, sp, pendingProposals, processedCommits>>

\* 【Commit Processing】A replica processes a committed command and performs garbage collection.
ProcessCommitMsg(r, cmd) ==
    /\ r \in Replicas
    /\ cmd \in committed
    /\ cmd \notin processedCommits[r]
    /\ LET new_sp_r == {c \in sp[r] : c /= cmd /\ \lnot IsConflict(c, cmd)} IN
       sp' = [sp EXCEPT ![r] = new_sp_r]
    /\ processedCommits' = [processedCommits EXCEPT ![r] = @ \cup {cmd}]
    /\ UNCHANGED <<leaderId, term, ucp, committed, pendingProposals>>

\* Supporting action to clean up fully processed commands from tracking sets.
GarbageCollectCommitted(cmd) ==
    /\ cmd \in committed
    /\ \A rep \in Replicas : cmd \in processedCommits[rep]
    /\ committed' = committed \ {cmd}
    /\ processedCommits' = [rep \in Replicas |-> processedCommits[rep] \ {cmd}]
    /\ UNCHANGED <<leaderId, term, sp, ucp, pendingProposals>>

\* 【Backend Protocol Leader Change】A new leader is elected and recovers its state.
LeaderChange(l) ==
    /\ l \in Replicas
    /\ term' = term + 1
    /\ leaderId' = l
    /\ \E Q \in SUBSET Replicas:
        /\ Cardinality(Q) >= RecoverQuorum(Cardinality(Replicas))
        /\ LET collected_sps == {sp[r] : r \in Q}
               recovered_sp == UNION collected_sps
               recovered_ucp == IF collected_sps = {} THEN {} ELSE Intersect(collected_sps)
           IN /\ sp' = [sp EXCEPT ![l] = recovered_sp]
              /\ ucp' = recovered_ucp
    /\ pendingProposals' = [r \in Replicas |-> {}]
    /\ committed' = {}
    /\ processedCommits' = [r \in Replicas |-> {}]

Next ==
    \/ \E cmd \in Commands : Propose(cmd)
    \/ \E r \in Replicas, cmd \in Commands : ProcessProposeLeader(r, cmd)
    \/ \E r \in Replicas, cmd \in Commands : ProcessProposeNonLeader(r, cmd)
    \/ \E cmd \in Commands : FastPathCommit(cmd)
    \/ \E cmd \in Commands : Commit(cmd)
    \/ \E r \in Replicas, cmd \in Commands : ProcessCommitMsg(r, cmd)
    \/ \E cmd \in Commands : GarbageCollectCommitted(cmd)
    \/ \E l \in Replicas : LeaderChange(l)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====
