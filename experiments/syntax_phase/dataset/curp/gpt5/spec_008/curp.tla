---- MODULE curp ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS
    REPLICAS,
    CMDS,
    KEYS,
    Keys

ASSUME
    REPLICAS # {} /\
    CMDS \subseteq DOMAIN Keys /\
    Keys \in [CMDS -> SUBSET KEYS]

(*
  Helper quorum functions
*)
Quorum(n) == n \div 2 + 1
RecoverQuorum(n) == Quorum(n) \div 2 + 1
SuperQuorum(n) == (n - Quorum(n)) + RecoverQuorum(n)

N == Cardinality(REPLICAS)

ResponseKinds == {"none","fast","slow"}

NonLeaders(ldr) == REPLICAS \ {ldr}

ConflictsWithSet(cmd, S) ==
    \E c \in S: (Keys[c] \cap Keys[cmd]) # {}

LeaderConflict(cmd, ldr, specPool, ucp) ==
    ConflictsWithSet(cmd, specPool[ldr] \cup ucp)

(*
  State variables
*)
VARIABLES
    leader,             \* current leader in REPLICAS
    specPool,           \* [r \in REPLICAS -> SUBSET CMDS]
    ucp,                \* SET of uncommitted commands at leader
    committed,          \* SET of committed commands
    applied,            \* [r \in REPLICAS -> SUBSET CMDS]
    pending,            \* SET of proposed (in-flight) commands
    useFast,            \* [CMDS -> BOOLEAN], chosen per command at Propose
    leaderConflict,     \* [CMDS -> BOOLEAN], computed by ProcessProposeLeader
    records,            \* [CMDS -> SUBSET REPLICAS], non-leader successful records
    responded           \* [CMDS -> ResponseKinds]

vars == << leader, specPool, ucp, committed, applied, pending, useFast, leaderConflict, records, responded >>

Init ==
    /\ leader \in REPLICAS
    /\ specPool \in [REPLICAS -> SUBSET CMDS]
    /\ \A r \in REPLICAS: specPool[r] = {}
    /\ ucp = {}
    /\ committed = {}
    /\ applied \in [REPLICAS -> SUBSET CMDS]
    /\ \A r \in REPLICAS: applied[r] = {}
    /\ pending = {}
    /\ useFast \in [CMDS -> BOOLEAN]
    /\ leaderConflict \in [CMDS -> BOOLEAN]
    /\ \A c \in CMDS: leaderConflict[c] = FALSE
    /\ records \in [CMDS -> SUBSET REPLICAS]
    /\ \A c \in CMDS: records[c] = {}
    /\ responded \in [CMDS -> ResponseKinds]
    /\ \A c \in CMDS: responded[c] = "none"

(*
  Core actions
*)

Propose(cmd) ==
    /\ cmd \in CMDS
    /\ cmd \notin committed
    /\ cmd \notin pending
    /\ \E b \in BOOLEAN:
         /\ pending' = pending \cup {cmd}
         /\ useFast' = [useFast EXCEPT ![cmd] = b]
         /\ records' = [records EXCEPT ![cmd] = {}]
         /\ UNCHANGED << leader, specPool, ucp, committed, applied, leaderConflict, responded >>

ProcessProposeLeader(r, cmd) ==
    /\ r = leader
    /\ cmd \in pending
    /\ cmd \notin specPool[leader]
    /\ LET conflict == LeaderConflict(cmd, leader, specPool, ucp) IN
       /\ specPool' = [specPool EXCEPT ![leader] = @ \cup {cmd}]
       /\ ucp' = ucp \cup {cmd}
       /\ leaderConflict' = [leaderConflict EXCEPT ![cmd] = conflict]
       /\ UNCHANGED << leader, committed, applied, pending, useFast, records, responded >>

ProcessProposeNonLeader(r, cmd) ==
    /\ r \in NonLeaders(leader)
    /\ cmd \in pending
    /\ cmd \notin specPool[r]
    /\ IF ConflictsWithSet(cmd, specPool[r]) THEN
         /\ specPool' = specPool
         /\ records' = records
       ELSE
         /\ specPool' = [specPool EXCEPT ![r] = @ \cup {cmd}]
         /\ records' = [records EXCEPT ![cmd] = @ \cup {r}]
    /\ UNCHANGED << leader, ucp, committed, applied, pending, useFast, leaderConflict, responded >>

(*
  Fast-path client response: requires no leader conflict and sufficient non-leader records
*)
RespondFast(cmd) ==
    /\ cmd \in pending
    /\ responded[cmd] = "none"
    /\ useFast[cmd] = TRUE
    /\ leaderConflict[cmd] = FALSE
    /\ Cardinality(records[cmd]) >= SuperQuorum(N) - 1
    /\ responded' = [responded EXCEPT ![cmd] = "fast"]
    /\ UNCHANGED << leader, specPool, ucp, committed, applied, pending, useFast, leaderConflict, records >>

(*
  Abstract backend consensus commit of an uncommitted command
*)
Commit ==
    /\ ucp # {}
    /\ \E cmd \in ucp:
         /\ ucp' = ucp \ {cmd}
         /\ committed' = committed \cup {cmd}
         /\ UNCHANGED << leader, specPool, applied, pending, useFast, leaderConflict, records, responded >>

(*
  Replica processes committed command and applies garbage collection
*)
ProcessCommitMsg(r, cmd) ==
    /\ r \in REPLICAS
    /\ cmd \in committed
    /\ cmd \notin applied[r]
    /\ applied' = [applied EXCEPT ![r] = @ \cup {cmd}]
    /\ specPool' = [specPool EXCEPT ![r] = @ \ {cmd}]
    /\ responded' =
         IF responded[cmd] = "none"
         THEN [responded EXCEPT ![cmd] = "slow"]
         ELSE responded
    /\ UNCHANGED << leader, ucp, committed, pending, useFast, leaderConflict, records >>

(*
  Backend protocol leader change with speculative pool recovery
  New leader collects speculative pools from replicas; any cmd present in at least RecoverQuorum(N)
  speculative pools and not yet committed is restored into leader's ucp and specPool
*)
LeaderChange(l) ==
    /\ l \in REPLICAS
    /\ l # leader
    /\ leader' = l
    /\ LET eligible ==
           { c \in CMDS :
                c \notin committed /\
                Cardinality({ r \in REPLICAS : c \in specPool[r] }) >= RecoverQuorum(N)
            }
       IN
         /\ ucp' = (ucp \cup eligible)
         /\ specPool' = [specPool EXCEPT ![l] = @ \cup eligible]
    /\ UNCHANGED << committed, applied, pending, useFast, leaderConflict, records, responded >>

(*
  Next-state relation
*)
Next ==
    \E cmd \in CMDS:
        Propose(cmd)
    \/ \E r \in REPLICAS, cmd \in CMDS:
        ProcessProposeLeader(r, cmd)
    \/ \E r \in REPLICAS, cmd \in CMDS:
        ProcessProposeNonLeader(r, cmd)
    \/ \E cmd \in CMDS:
        RespondFast(cmd)
    \/ Commit
    \/ \E r \in REPLICAS, cmd \in CMDS:
        ProcessCommitMsg(r, cmd)
    \/ \E l \in REPLICAS:
        LeaderChange(l)

Spec == Init /\ [][Next]_vars

====