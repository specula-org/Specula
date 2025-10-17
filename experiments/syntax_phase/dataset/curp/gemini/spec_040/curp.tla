---- MODULE curp ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Server, Command, Key
CONSTANT keyOf

Quorum(S) == Cardinality(S) \div 2 + 1
RecoverQuorum(S) == Quorum(S) \div 2 + 1
SuperQuorum(S) == (Cardinality(S) - Quorum(S)) + RecoverQuorum(S)

VARIABLES
    leader,
    spec_pool,
    uncommitted_pool,
    committed,
    proposals

vars == <<leader, spec_pool, uncommitted_pool, committed, proposals>>

Conflicts(cmd, pool) ==
    \E p_cmd \in pool: keyOf[p_cmd] = keyOf[cmd]

Init ==
    /\ \E l \in Server: leader = l
    /\ spec_pool = [s \in Server |-> {}]
    /\ uncommitted_pool = [s \in Server |-> {}]
    /\ committed = {}
    /\ proposals = {}

Propose(cmd) ==
    /\ cmd \notin proposals
    /\ cmd \notin committed
    /\ proposals' = proposals \cup {cmd}
    /\ UNCHANGED <<leader, spec_pool, uncommitted_pool, committed>>

ProcessProposeLeader(r, cmd) ==
    /\ r = leader
    /\ cmd \in proposals
    /\ cmd \notin uncommitted_pool[r]
    /\ LET conflict == Conflicts(cmd, spec_pool[r]) \/ Conflicts(cmd, uncommitted_pool[r])
       IN /\ spec_pool' = [spec_pool EXCEPT ![r] = @ \cup {cmd}]
          /\ uncommitted_pool' = [uncommitted_pool EXCEPT ![r] = @ \cup {cmd}]
    /\ UNCHANGED <<leader, committed, proposals>>

ProcessProposeNonLeader(r, cmd) ==
    /\ r /= leader
    /\ cmd \in proposals
    /\ cmd \notin spec_pool[r]
    /\ LET conflict == Conflicts(cmd, spec_pool[r])
       IN /\ spec_pool' = [spec_pool EXCEPT ![r] = @ \cup {cmd}]
    /\ UNCHANGED <<leader, uncommitted_pool, committed, proposals>>

Commit(cmd) ==
    /\ cmd \in uncommitted_pool[leader]
    /\ cmd \notin committed
    /\ committed' = committed \cup {cmd}
    /\ proposals' = proposals \ {cmd}
    /\ UNCHANGED <<leader, spec_pool, uncommitted_pool>>

ProcessCommitMsg(r, cmd) ==
    /\ cmd \in committed
    /\ cmd \in uncommitted_pool[r]
    /\ uncommitted_pool' = [uncommitted_pool EXCEPT ![r] = @ \ {cmd}]
    /\ LET conflicting_in_spec == {scmd \in spec_pool[r] | keyOf[scmd] = keyOf[cmd]}
       IN spec_pool' = [spec_pool EXCEPT ![r] = @ \ conflicting_in_spec]
    /\ UNCHANGED <<leader, committed, proposals>>

LeaderChange(l) ==
    /\ l \in Server
    /\ l /= leader
    /\ \E quorum_servers \in {S \in SUBSET Server | Cardinality(S) >= Quorum(Server)}:
        LET
            AllSpecCmds == UNION {spec_pool[s] : s \in quorum_servers}
            RecoveredCmds == { c \in AllSpecCmds |
                                Cardinality({s \in quorum_servers | c \in spec_pool[s]}) >= RecoverQuorum(Server)
                             }
        IN /\ leader' = l
           /\ uncommitted_pool' = [uncommitted_pool EXCEPT ![l] = RecoveredCmds]
           /\ spec_pool' = [spec_pool EXCEPT ![l] = RecoveredCmds]
    /\ UNCHANGED <<committed, proposals>>

Next ==
    \/ \E cmd \in Command : Propose(cmd)
    \/ \E r \in Server, cmd \in proposals : ProcessProposeLeader(r, cmd)
    \/ \E r \in Server, cmd \in proposals : ProcessProposeNonLeader(r, cmd)
    \/ \E cmd \in Command : Commit(cmd)
    \/ \E r \in Server, cmd \in committed : ProcessCommitMsg(r, cmd)
    \/ \E l \in Server : LeaderChange(l)

Spec == Init /\ [][Next]_vars

====