---- MODULE curp ----
EXTENDS Naturals, Sequences, FiniteSets
CONSTANTS Servers, Commands, Key, NULL
VARIABLES specPools, uncommittedPools, log, roles, terms, commitIndex, lastApplieds, currentLeader
vars == <<specPools, uncommittedPools, log, roles, terms, commitIndex, lastApplieds, currentLeader>>
Quorum == (Cardinality(Servers) \div 2) + 1
RecoverQuorum == (Quorum \div 2) + 1
SuperQuorum == (Cardinality(Servers) - Quorum) + RecoverQuorum
Init == 
    /\ specPools = [s \in Servers |-> {}]
    /\ uncommittedPools = [s \in Servers |-> {}]
    /\ log = <<>>
    /\ roles = [s \in Servers |-> "Follower"]
    /\ terms = [s \in Servers |-> 0]
    /\ commitIndex = 0
    /\ lastApplieds = [s \in Servers |-> 0]
    /\ currentLeader = NULL
Propose(cmd) ==
    /\ specPools' = [s \in Servers |-> specPools[s] \cup {cmd}]
    /\ IF currentLeader # NULL
        THEN 
            LET conflict == \E c \in specPools[currentLeader] \cup uncommittedPools[currentLeader] : Key(c) = Key(cmd)
            IN
            /\ uncommittedPools' = [s \in Servers |-> IF s = currentLeader THEN uncommittedPools[s] \cup {cmd} ELSE uncommittedPools[s]]
            /\ IF ~conflict 
               THEN /\ log' = Append(log, [term |-> terms[currentLeader], command |-> cmd])
                    /\ commitIndex' = commitIndex
               ELSE /\ log' = log
                    /\ commitIndex' = commitIndex
        ELSE 
            /\ uncommittedPools' = uncommittedPools
            /\ log' = log
            /\ commitIndex' = commitIndex
    /\ UNCHANGED <<roles, terms, lastApplieds, currentLeader>>
Commit() ==
    /\ commitIndex < Len(log)
    /\ commitIndex' = commitIndex + 1
    /\ UNCHANGED <<specPools, uncommittedPools, log, roles, terms, lastApplieds, currentLeader>>
ProcessCommitMsg(r) ==
    /\ lastApplieds[r] < commitIndex
    /\ LET newApplied = lastApplieds[r] + 1
       cmd = log[newApplied]["command"]
       IN
       /\ lastApplieds' = [lastApplieds EXCEPT ![r] = newApplied]
       /\ specPools' = [specPools EXCEPT ![r] = specPools[r] \ {cmd}]
       /\ uncommittedPools' = [uncommittedPools EXCEPT ![r] = uncommittedPools[r] \ {cmd}]
    /\ UNCHANGED <<log, roles, terms, commitIndex, currentLeader>>
LeaderChange(l) ==
    /\ l \in Servers
    /\ currentLeader' = l
    /\ roles' = [roles EXCEPT ![l] = "Leader"]
    /\ terms' = [s \in Servers |-> Max({terms[s] : s \in Servers}) + 1]
    /\ LET RecoverCommands = {cmd \in Commands : Cardinality({s \in Servers : cmd \in specPools[s]}) >= RecoverQuorum }
           newCommands = RecoverCommands \ {log[i]["command"] : i \in 1..Len(log)}
           newEntries = CHOOSE seq \in [1..Cardinality(newCommands) -> [term: Nat, command: Commands]] : Range(seq) = { [term |-> terms'[l], command |-> cmd] : cmd \in newCommands }
       IN
       ( specPools' = [specPools EXCEPT ![l] = specPools[l] \cup RecoverCommands]
         /\ uncommittedPools' = [uncommittedPools EXCEPT ![l] = uncommittedPools[l] \cup RecoverCommands]
         /\ log' = IF newCommands = {} THEN log ELSE log \o newEntries
         /\ commitIndex' = commitIndex
         /\ lastApplieds' = lastApplieds )
Next == 
    \/ \E cmd \in Commands : Propose(cmd)
    \/ Commit()
    \/ \E r \in Servers : ProcessCommitMsg(r)
    \/ \E l \in Servers : LeaderChange(l)
Spec == Init /\ [][Next]_vars
====