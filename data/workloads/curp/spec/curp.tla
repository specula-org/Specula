---- MODULE curp ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Servers, Cmds

VARIABLES leader, specPool, uncommittedPool, committed

vars == <<leader, specPool, uncommittedPool, committed>>

SeqToSet(seq) ==
    {seq[i] : i \in 1..Len(seq)}

TypeOK ==
    /\ leader \in Servers
    /\ specPool \in [Servers -> SUBSET Cmds]
    /\ uncommittedPool \in [Servers -> SUBSET Cmds]
    /\ committed \in Seq(Cmds)

Init ==
    /\ leader \in Servers
    /\ specPool = [s \in Servers |-> {}]
    /\ uncommittedPool = [s \in Servers |-> {}]
    /\ committed = <<>>

CmdUnused(c) ==
    /\ c \in Cmds
    /\ \A s \in Servers : c \notin specPool[s] /\ c \notin uncommittedPool[s]

CmdAvailable(c) ==
    c \in Cmds

Propose(c) ==
    /\ CmdUnused(c)
    /\ \E S \in SUBSET Servers :
        specPool' = [s \in Servers |-> IF s \in S THEN specPool[s] \cup {c} ELSE specPool[s]]
    /\ UNCHANGED <<leader, uncommittedPool, committed>>

ProcessProposeLeader(c) ==
    /\ CmdAvailable(c)
    /\ specPool' = [specPool EXCEPT ![leader] = @ \cup {c}]
    /\ uncommittedPool' = [uncommittedPool EXCEPT ![leader] = @ \cup {c}]
    /\ UNCHANGED <<leader, committed>>

ProcessProposeNonLeader(s, c) ==
    /\ s \in Servers \ {leader}
    /\ CmdAvailable(c)
    /\ specPool' = [specPool EXCEPT ![s] = @ \cup {c}]
    /\ UNCHANGED <<leader, uncommittedPool, committed>>

Commit(c) ==
    /\ c \in specPool[leader]
    /\ committed' = Append(committed, c)
    /\ uncommittedPool' = [uncommittedPool EXCEPT ![leader] = @ \ {c}]
    /\ UNCHANGED <<leader, specPool>>

ProcessCommitMsg(s, c) ==
    /\ s \in Servers
    /\ c \in SeqToSet(committed)
    /\ IF c \in specPool[s]
        THEN
            /\ \E removed \in SUBSET specPool[s] :
                /\ c \in removed
                /\ specPool' = [specPool EXCEPT ![s] = @ \ removed]
                /\ uncommittedPool' = [uncommittedPool EXCEPT ![s] = @ \ removed]
        ELSE
            /\ specPool' = specPool
            /\ uncommittedPool' = uncommittedPool
    /\ UNCHANGED <<leader, committed>>

LeaderChange(s) ==
    /\ s \in Servers
    /\ leader' = s
    /\ UNCHANGED <<specPool, uncommittedPool, committed>>

Next ==
    \/ \E c \in Cmds : Propose(c)
    \/ \E c \in Cmds : ProcessProposeLeader(c)
    \/ \E s \in Servers, c \in Cmds : ProcessProposeNonLeader(s, c)
    \/ \E c \in Cmds : Commit(c)
    \/ \E s \in Servers, c \in Cmds : ProcessCommitMsg(s, c)
    \/ \E s \in Servers : LeaderChange(s)

Spec ==
    Init /\ [][Next]_vars

====
