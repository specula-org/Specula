---- MODULE curp ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS REPLICAS, KEYS, CMDS

ASSUME REPLICAS # {} /\ IsFiniteSet(REPLICAS) /\ CMDS \subseteq [id: Nat, key: KEYS]

N == Cardinality(REPLICAS)

Quorum(n) == (n \div 2) + 1
RecoverQuorum(n) == (Quorum(n) \div 2) + 1
SuperQuorum(n) == (n - Quorum(n)) + RecoverQuorum(n)

Key(c) == c.key
Conflicts(S, c) == \E x \in S: x.key = c.key

VARIABLES leader, sp, ucp, proposed, committed, applied, leaderSpecOK, respFast, respSlow

Followers(l) == REPLICAS \ {l}
CountFollowersRecorded(l, c) == Cardinality({ r \in Followers(l) : c \in sp[r] })
LeaderApplied(c) == <<leader, c>> \in applied
responded == respFast \cup respSlow

TypeOK ==
  /\ leader \in REPLICAS
  /\ sp \in [REPLICAS -> SUBSET CMDS]
  /\ ucp \in [REPLICAS -> SUBSET CMDS]
  /\ proposed \subseteq CMDS
  /\ committed \subseteq CMDS
  /\ applied \subseteq {<<r, c>> \in REPLICAS \X CMDS}
  /\ leaderSpecOK \subseteq CMDS
  /\ respFast \subseteq CMDS
  /\ respSlow \subseteq CMDS

Init ==
  /\ leader \in REPLICAS
  /\ sp = [r \in REPLICAS |-> {}]
  /\ ucp = [r \in REPLICAS |-> {}]
  /\ proposed = {}
  /\ committed = {}
  /\ applied = {}
  /\ leaderSpecOK = {}
  /\ respFast = {}
  /\ respSlow = {}
  /\ TypeOK

Propose(c) ==
  /\ c \in CMDS
  /\ c \notin proposed
  /\ proposed' = proposed \cup {c}
  /\ UNCHANGED <<leader, sp, ucp, committed, applied, leaderSpecOK, respFast, respSlow>>

ProcessProposeLeader(r, c) ==
  /\ r = leader
  /\ c \in proposed
  /\ IF ~Conflicts(sp[r], c) /\ ~Conflicts(ucp[r], c)
     THEN /\ sp' = [sp EXCEPT ![r] = sp[r] \cup {c}]
          /\ ucp' = [ucp EXCEPT ![r] = ucp[r] \cup {c}]
          /\ leaderSpecOK' = leaderSpecOK \cup {c}
     ELSE /\ sp' = sp
          /\ ucp' = [ucp EXCEPT ![r] = ucp[r] \cup {c}]
          /\ leaderSpecOK' = leaderSpecOK
  /\ UNCHANGED <<leader, proposed, committed, applied, respFast, respSlow>>

ProcessProposeNonLeader(r, c) ==
  /\ r \in REPLICAS
  /\ r # leader
  /\ c \in proposed
  /\ ~Conflicts(sp[r], c)
  /\ sp' = [sp EXCEPT ![r] = sp[r] \cup {c}]
  /\ UNCHANGED <<leader, ucp, proposed, committed, applied, leaderSpecOK, respFast, respSlow>>

Commit(c) ==
  /\ c \in proposed
  /\ c \notin committed
  /\ committed' = committed \cup {c}
  /\ UNCHANGED <<leader, sp, ucp, proposed, applied, leaderSpecOK, respFast, respSlow>>

ProcessCommitMsg(r, c) ==
  /\ r \in REPLICAS
  /\ c \in committed
  /\ <<r, c>> \notin applied
  /\ sp' = [sp EXCEPT ![r] = sp[r] \ {c}]
  /\ ucp' = [ucp EXCEPT ![r] = ucp[r] \ {c}]
  /\ applied' = applied \cup {<<r, c>>}
  /\ UNCHANGED <<leader, proposed, committed, leaderSpecOK, respFast, respSlow>>

LeaderChange(l) ==
  /\ l \in REPLICAS
  /\ l # leader
  /\ \E Q \in SUBSET REPLICAS:
        /\ Cardinality(Q) >= Quorum(N)
        /\ LET Rcv == { c \in proposed :
                         Cardinality({ r \in Q : c \in sp[r] }) >= RecoverQuorum(N) }
           IN /\ leader' = l
              /\ sp' = [sp EXCEPT ![l] = sp[l] \cup Rcv]
              /\ ucp' = [ucp EXCEPT ![l] = ucp[l] \cup Rcv]
              /\ leaderSpecOK' = {}
              /\ UNCHANGED <<proposed, committed, applied, respFast, respSlow>>

FastPathRespond(c) ==
  /\ c \in proposed
  /\ c \notin respFast
  /\ c \notin respSlow
  /\ c \in leaderSpecOK
  /\ CountFollowersRecorded(leader, c) >= SuperQuorum(N) - 1
  /\ respFast' = respFast \cup {c}
  /\ UNCHANGED <<leader, sp, ucp, proposed, committed, applied, leaderSpecOK, respSlow>>

SlowPathRespond(c) ==
  /\ c \in committed
  /\ c \notin respFast
  /\ c \notin respSlow
  /\ LeaderApplied(c)
  /\ respSlow' = respSlow \cup {c}
  /\ UNCHANGED <<leader, sp, ucp, proposed, committed, applied, leaderSpecOK, respFast>>

Next ==
  \/ (\E c \in CMDS: Propose(c))
  \/ (\E c \in CMDS, r \in REPLICAS: ProcessProposeLeader(r, c))
  \/ (\E c \in CMDS, r \in REPLICAS: ProcessProposeNonLeader(r, c))
  \/ (\E c \in CMDS: Commit(c))
  \/ (\E c \in CMDS, r \in REPLICAS: ProcessCommitMsg(r, c))
  \/ (\E l \in REPLICAS: LeaderChange(l))
  \/ (\E c \in CMDS: FastPathRespond(c))
  \/ (\E c \in CMDS: SlowPathRespond(c))

Spec == Init /\ [][Next]_<<leader, sp, ucp, proposed, committed, applied, leaderSpecOK, respFast, respSlow>>

====