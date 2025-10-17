---- MODULE curp ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS
    REPLICAS,
    CMDS,
    KEYS,
    KEY \in [CMDS -> KEYS]

Size == Cardinality(REPLICAS)
Quorum == (Size \div 2) + 1
RecoverQuorum == (Quorum \div 2) + 1
SuperQuorum == (Size - Quorum) + RecoverQuorum

VARIABLES
    Leader,
    Spec, \* [REPLICAS -> SUBSET CMDS]
    Ucp,  \* [REPLICAS -> SUBSET CMDS]
    Committed, \* SUBSET CMDS
    Proposed,  \* SUBSET CMDS
    Responded, \* SUBSET CMDS
    Acc, \* [CMDS -> SUBSET REPLICAS] followers that recorded without conflict
    LConf \* SUBSET CMDS, leader-side conflict detected

Followers == REPLICAS \ {Leader}

ConflictsInSpec(r, c) == \E d \in Spec[r]: KEY[d] = KEY[c]
ConflictsInUcp(r, c) == \E d \in Ucp[r]: KEY[d] = KEY[c]
CountSpec(c) == Cardinality({ r \in REPLICAS: c \in Spec[r] })
UCPUnion == UNION { Ucp[r] : r \in REPLICAS }
EnoughRecords(c) == Cardinality(Acc[c]) >= SuperQuorum - 1
RemoveKey(S, k) == { d \in S: KEY[d] # k }

Init ==
    /\ Leader \in REPLICAS
    /\ Spec \in [REPLICAS -> SUBSET CMDS]
    /\ Spec = [r \in REPLICAS |-> {}]
    /\ Ucp \in [REPLICAS -> SUBSET CMDS]
    /\ Ucp = [r \in REPLICAS |-> {}]
    /\ Committed = {}
    /\ Proposed = {}
    /\ Responded = {}
    /\ Acc \in [CMDS -> SUBSET REPLICAS]
    /\ Acc = [c \in CMDS |-> {}]
    /\ LConf = {}

Propose(c) ==
    /\ c \in CMDS \ Proposed
    /\ Proposed' = Proposed \cup {c}
    /\ UNCHANGED << Leader, Spec, Ucp, Committed, Responded, Acc, LConf >>

ProcessProposeLeader(r, c) ==
    /\ r = Leader
    /\ c \in Proposed
    /\ LET lc == (ConflictsInSpec(Leader, c) \/ ConflictsInUcp(Leader, c)) IN
       /\ Spec' = [Spec EXCEPT ![Leader] = Spec[Leader] \cup (IF lc THEN {} ELSE {c})]
       /\ Ucp' = [Ucp EXCEPT ![Leader] = Ucp[Leader] \cup {c}]
       /\ LConf' = IF lc THEN LConf \cup {c} ELSE LConf \ {c}
       /\ UNCHANGED << Leader, Committed, Proposed, Responded, Acc >>

ProcessProposeNonLeader(r, c) ==
    /\ r \in Followers
    /\ c \in Proposed
    /\ IF ConflictsInSpec(r, c) THEN
          /\ Spec' = Spec
          /\ Acc' = Acc
       ELSE
          /\ Spec' = [Spec EXCEPT ![r] = Spec[r] \cup {c}]
          /\ Acc' = [Acc EXCEPT ![c] = Acc[c] \cup {r}]
    /\ UNCHANGED << Leader, Ucp, Committed, Proposed, Responded, LConf >>

FastPathRespond(c) ==
    /\ c \in Proposed \ Responded
    /\ ~(c \in LConf)
    /\ EnoughRecords(c)
    /\ Responded' = Responded \cup {c}
    /\ UNCHANGED << Leader, Spec, Ucp, Committed, Proposed, Acc, LConf >>

Commit ==
    /\ \E c \in (UCPUnion \ Committed):
         /\ Committed' = Committed \cup {c}
         /\ UNCHANGED << Leader, Spec, Ucp, Proposed, Responded, Acc, LConf >>

ProcessCommitMsg(r, c) ==
    /\ r \in REPLICAS
    /\ c \in Committed
    /\ Spec' = [Spec EXCEPT ![r] = RemoveKey(Spec[r], KEY[c])]
    /\ Ucp' = [Ucp EXCEPT ![r] = Ucp[r] \ {c}]
    /\ Responded' = Responded \cup {c}
    /\ UNCHANGED << Leader, Committed, Proposed, Acc, LConf >>

LeaderChange(l) ==
    /\ l \in REPLICAS
    /\ l # Leader
    /\ LET S == { c \in CMDS: CountSpec(c) >= RecoverQuorum } IN
       /\ Leader' = l
       /\ Spec' = [Spec EXCEPT ![l] = Spec[l] \cup S]
       /\ Ucp'  = [Ucp  EXCEPT ![l] = Ucp[l]  \cup S]
       /\ UNCHANGED << Committed, Proposed, Responded, Acc, LConf >>

Next ==
    \E c \in CMDS:
        Propose(c)
    \/ \E r \in REPLICAS, c \in CMDS:
        ProcessProposeLeader(r, c)
    \/ \E r \in REPLICAS, c \in CMDS:
        ProcessProposeNonLeader(r, c)
    \/ Commit
    \/ \E r \in REPLICAS, c \in CMDS:
        ProcessCommitMsg(r, c)
    \/ \E l \in REPLICAS:
        LeaderChange(l)
    \/ \E c \in CMDS:
        FastPathRespond(c)

vars == << Leader, Spec, Ucp, Committed, Proposed, Responded, Acc, LConf >>

SpecCurp == Init /\ [][Next]_vars

====