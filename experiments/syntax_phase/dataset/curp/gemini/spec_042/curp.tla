---- MODULE curp ----
EXTENDS TLC, Naturals, FiniteSets, Sequences

CONSTANTS Replicas, Commands, Keys, Key

ASSUME IsFiniteSet(Replicas) /\ Replicas # {}
ASSUME IsFiniteSet(Commands)
ASSUME \A c \in Commands: Key[c] \in Keys

N == Cardinality(Replicas)
QuorumSize == (N \div 2) + 1
RecoverQuorumSize == (QuorumSize \div 2) + 1
SuperQuorumSize == (N - QuorumSize) + RecoverQuorumSize

VARIABLES
    leader,
    \* Commands being tracked by the leader for fast-path consensus.
    \* A set of records: [cmd |-> c, witnesses |-> W]
    uncommitted_pool,
    \* Commands speculatively executed on each replica.
    \* A function from Replica -> Set of Commands.
    speculative_pool,
    \* Commands durably committed on each replica.
    \* A function from Replica -> Set of Commands.
    committed_cmds,
    \* The set of in-flight messages.
    messages

vars == <<leader, uncommitted_pool, speculative_pool, committed_cmds, messages>>

GetKeys(cmds) == {Key[c] : c \in cmds}
Conflicts(cmd, cmds) == Key[cmd] \in GetKeys(cmds)

Init ==
    /\ \E l \in Replicas: leader = l
    /\ uncommitted_pool = {}
    /\ speculative_pool = [r \in Replicas |-> {}]
    /\ committed_cmds = [r \in Replicas |-> {}]
    /\ messages = {}

ClientPropose(cmd) ==
    /\ cmd \in Commands
    /\ \A uc \in uncommitted_pool: cmd # uc.cmd
    /\ \A r \in Replicas: cmd \notin committed_cmds[r]
    /\ messages' = messages \cup {[type |-> "propose", cmd |-> cmd, to |-> leader]}
    /\ UNCHANGED <<leader, uncommitted_pool, speculative_pool, committed_cmds>>

LeaderReceivesPropose(cmd) ==
    /\ \E msg \in messages:
        /\ msg = [type |-> "propose", cmd |-> cmd, to |-> leader]
        /\ LET
            current_uncommitted_cmds == {uc.cmd : uc \in uncommitted_pool}
            current_committed_cmds == committed_cmds[leader]
           IN
            /\ \lnot Conflicts(cmd, current_uncommitted_cmds \cup current_committed_cmds)
            /\ LET uc_entry = [cmd |-> cmd, witnesses |-> {leader}]
               IN uncommitted_pool' = uncommitted_pool \cup {uc_entry}
            /\ speculative_pool' = [speculative_pool EXCEPT ![leader] = @ \cup {cmd}]
            /\ messages' = (messages \ {msg}) \cup
                            {[type |-> "speculate", cmd |-> cmd, from |-> leader, to |-> r] : r \in Replicas \ {leader}}
            /\ UNCHANGED committed_cmds
    /\ UNCHANGED leader

FollowerReceivesSpeculate(r, cmd) ==
    /\ r # leader
    /\ \E msg \in messages:
        /\ msg = [type |-> "speculate", cmd |-> cmd, from |-> leader, to |-> r]
        /\ \lnot Conflicts(cmd, speculative_pool[r] \cup committed_cmds[r])
        /\ speculative_pool' = [speculative_pool EXCEPT ![r] = @ \cup {cmd}]
        /\ messages' = (messages \ {msg}) \cup {[type |-> "speculate_ack", cmd |-> cmd, from |-> r, to |-> leader]}
        /\ UNCHANGED <<leader, uncommitted_pool, committed_cmds>>

LeaderReceivesAck(r, cmd) ==
    /\ r # leader
    /\ \E msg \in messages:
        /\ msg = [type |-> "speculate_ack", cmd |-> cmd, from |-> r, to |-> leader]
        /\ \E uc \in uncommitted_pool:
            /\ uc.cmd = cmd
            /\ r \notin uc.witnesses
            /\ LET new_uc = [cmd |-> cmd, witnesses |-> uc.witnesses \cup {r}]
               IN uncommitted_pool' = (uncommitted_pool \ {uc}) \cup {new_uc}
            /\ messages' = messages \ {msg}
            /\ UNCHANGED <<leader, speculative_pool, committed_cmds>>

LeaderCommits(uc) ==
    /\ uc \in uncommitted_pool
    /\ Cardinality(uc.witnesses) >= QuorumSize
    /\ LET cmd == uc.cmd
       IN /\ uncommitted_pool' = uncommitted_pool \ {uc}
          /\ speculative_pool' = [speculative_pool EXCEPT ![leader] = @ \ {cmd}]
          /\ committed_cmds' = [committed_cmds EXCEPT ![leader] = @ \cup {cmd}]
          /\ messages' = messages \cup
                         {[type |-> "commit", cmd |-> cmd, from |-> leader, to |-> r] : r \in Replicas \ {leader}}
    /\ UNCHANGED leader

NodeReceivesCommit(r, cmd) ==
    /\ \E msg \in messages:
        /\ msg = [type |-> "commit", cmd |-> cmd, from |-> leader, to |-> r]
        /\ speculative_pool' = [speculative_pool EXCEPT ![r] = @ \ {cmd}]
        /\ committed_cmds' = [committed_cmds EXCEPT ![r] = @ \cup {cmd}]
        /\ messages' = messages \ {msg}
        /\ UNCHANGED <<leader, uncommitted_pool>>

LeaderChange(l) ==
    /\ l \in Replicas
    /\ l # leader
    /\ LET
        all_spec_cmds == UNION {speculative_pool[r] : r \in Replicas}
        CmdWitnesses(c) == {r \in Replicas : c \in speculative_pool[r]}
        recovered_cmds_set == {c \in all_spec_cmds : Cardinality(CmdWitnesses(c)) >= RecoverQuorumSize}
       IN
        /\ leader' = l
        /\ uncommitted_pool' = {[cmd |-> c, witnesses |-> CmdWitnesses(c)] : c \in recovered_cmds_set}
        /\ speculative_pool' = [speculative_pool EXCEPT ![l] = @ \cup recovered_cmds_set]
        /\ messages' = {}
    /\ UNCHANGED committed_cmds

Next ==
    \/ \E cmd \in Commands: ClientPropose(cmd)
    \/ \E cmd \in Commands: LeaderReceivesPropose(cmd)
    \/ \E r \in Replicas, cmd \in Commands: FollowerReceivesSpeculate(r, cmd)
    \/ \E r \in Replicas, cmd \in Commands: LeaderReceivesAck(r, cmd)
    \/ \E uc \in uncommitted_pool: LeaderCommits(uc)
    \/ \E r \in Replicas, cmd \in Commands: NodeReceivesCommit(r, cmd)
    \/ \E l \in Replicas: LeaderChange(l)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====