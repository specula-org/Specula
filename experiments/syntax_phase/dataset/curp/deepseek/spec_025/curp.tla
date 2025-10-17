---- MODULE curp ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Replicas, Commands, Keys, Values

ASSUME \A cmd \in Commands: cmd.key \in Keys /\ cmd.value \in Values
ASSUME \A cmd1, cmd2 \in Commands: (cmd1.id = cmd2.id) => (cmd1 = cmd2)

VARIABLES leader, sp, ucp, committed, proposed

vars == <<leader, sp, ucp, committed, proposed>>

Quorum == Cardinality(Replicas) \div 2 + 1
RecoverQuorum == Quorum \div 2 + 1
SuperQuorum == (Cardinality(Replicas) - Quorum) + RecoverQuorum

TypeInvariant ==
  /\ leader \in Replicas \cup {Nil}
  /\ sp \in [Replicas -> SUBSET Commands]
  /\ ucp \subseteq Commands
  /\ committed \subseteq Commands
  /\ proposed \subseteq Commands

Init ==
  /\ leader = Nil
  /\ sp = [r \in Replicas |-> {}]
  /\ ucp = {}
  /\ committed = {}
  /\ proposed = {}

Propose(cmd) ==
  /\ cmd \notin proposed
  /\ proposed' = proposed \cup {cmd}
  /\ UNCHANGED <<leader, sp, ucp, committed>>

ProcessProposeNonLeader(r, cmd) ==
  /\ r \in Replicas
  /\ leader \in Replicas \cup {Nil}
  /\ r # leader
  /\ cmd \in proposed
  /\ cmd \notin committed
  /\ cmd \notin sp[r]
  /\ \A c \in sp[r]: c.key # cmd.key
  /\ sp' = [sp EXCEPT ![r] = @ \cup {cmd}]
  /\ UNCHANGED <<leader, ucp, committed, proposed>>

ProcessProposeLeader(r, cmd) ==
  /\ r \in Replicas
  /\ leader = r
  /\ cmd \in proposed
  /\ cmd \notin committed
  /\ cmd \notin sp[r] \cup ucp
  /\ LET conflict == \E c \in (sp[r] \cup ucp): c.key = cmd.key
     IN
     IF conflict
       THEN /\ ucp' = ucp \cup {cmd}
            /\ sp' = [sp EXCEPT ![r] = @ \cup {cmd}]
       ELSE /\ ucp' = ucp \cup {cmd}
            /\ sp' = [sp EXCEPT ![r] = @ \cup {cmd}]
  /\ UNCHANGED <<leader, committed, proposed>>

Commit(cmd) ==
  /\ leader # Nil
  /\ cmd \in ucp
  /\ committed' = committed \cup {cmd}
  /\ ucp' = ucp \ {cmd}
  /\ UNCHANGED <<leader, sp, proposed>>

ProcessCommitMsg(r, cmd) ==
  /\ cmd \in committed
  /\ cmd \in sp[r]
  /\ sp' = [sp EXCEPT ![r] = @ \ {cmd}]
  /\ UNCHANGED <<leader, ucp, committed, proposed>>

LeaderChange(l) ==
  /\ l \in Replicas
  /\ leader' = l
  /\ \E Q \in SUBSET Replicas:
      /\ Cardinality(Q) >= Quorum
      /\ LET all_cmds == UNION {sp[r] : r \in Q}
             recovered == {cmd \in all_cmds \ committed: 
                           Cardinality({r \in Q: cmd \in sp[r]}) >= RecoverQuorum}
         IN
         /\ ucp' = recovered
         /\ sp' = [sp EXCEPT ![l] = sp[l] \cup recovered]
  /\ UNCHANGED <<committed, proposed>>

Next ==
  \/ \E cmd \in Commands: Propose(cmd)
  \/ \E r \in Replicas, cmd \in Commands: ProcessProposeNonLeader(r, cmd)
  \/ \E r \in Replicas, cmd \in Commands: ProcessProposeLeader(r, cmd)
  \/ \E cmd \in Commands: Commit(cmd)
  \/ \E r \in Replicas, cmd \in Commands: ProcessCommitMsg(r, cmd)
  \/ \E l \in Replicas: LeaderChange(l)

Spec == Init /\ [][Next]_vars

====