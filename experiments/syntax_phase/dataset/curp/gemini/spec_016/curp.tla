---- MODULE curp ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Server, NumCmds, NumKeys

ASSUME IsFiniteSet(Server)
ASSUME Server /= {}
ASSUME NumCmds \in Nat \ {0}
ASSUME NumKeys \in Nat \ {0}

Key == 1..NumKeys
CmdID == 1..NumCmds
Command == [ id: CmdID, keys: SUBSET Key ]

VARIABLES leader, spec_pool, uncommitted_pool, committed_log, network, client_responses

vars == << leader, spec_pool, uncommitted_pool, committed_log, network, client_responses >>

Quorum(S) == Cardinality(S) \div 2 + 1
FaultTolerance(S) == Cardinality(S) - Quorum(S)
RecoverQuorum(S) == Quorum(S) \div 2 + 1
SuperQuorum(S) == FaultTolerance(S) + RecoverQuorum(S)

HasConflict(cmd, pool) == \E c \in pool : cmd.keys \cap c.keys /= {}

Init ==
    /\ \E l \in Server : leader = l
    /\ spec_pool = [s \in Server |-> {}]
    /\ uncommitted_pool = [s \in Server |-> {}]
    /\ committed_log = <<>>
    /\ network = EmptyBag
    /\ client_responses = [cid \in {} |-> ""]

ClientPropose(cmd) ==
    /\ cmd.id \notin DOMAIN client_responses
    /\ network' = network \cup+ Bag({[type |-> "propose", cmd |-> cmd, to |-> leader]})
                         \cup+ Bag({[type |-> "record", cmd |-> cmd, to |-> s] : s \in Server \ {leader}})
    /\ client_responses' = client_responses \cup [cmd.id |-> [status |-> "pending"]]
    /\ UNCHANGED << leader, spec_pool, uncommitted_pool, committed_log >>

ProcessProposeLeader ==
    /\ \E msg \in BagToSet(network):
        /\ msg.type = "propose"
        /\ msg.to = leader
        /\ LET self == leader
               cmd == msg.cmd
               conflict == HasConflict(cmd, spec_pool[self]) \/ HasConflict(cmd, uncommitted_pool[self])
               reply == [type |-> "propose_reply", cmd_id |-> cmd.id, conflict |-> conflict, from |-> self]
           IN
           /\ network' = (network \- Bag({msg})) \cup+ Bag({reply})
           /\ IF ~conflict THEN
                /\ spec_pool' = [spec_pool EXCEPT ![self] = @ \cup {cmd}]
                /\ uncommitted_pool' = [uncommitted_pool EXCEPT ![self] = @ \cup {cmd}]
              ELSE
                /\ UNCHANGED << spec_pool, uncommitted_pool >>
    /\ UNCHANGED << leader, committed_log, client_responses >>

ProcessRecordRequest(self) ==
    /\ self \in Server \ {leader}
    /\ \E msg \in BagToSet(network):
        /\ msg.type = "record"
        /\ msg.to = self
        /\ LET cmd == msg.cmd
               conflict == HasConflict(cmd, spec_pool[self])
               reply == [type |-> "record_reply", cmd_id |-> cmd.id, conflict |-> conflict, from |-> self]
           IN
           /\ network' = (network \- Bag({msg})) \cup+ Bag({reply})
           /\ IF ~conflict THEN
                /\ spec_pool' = [spec_pool EXCEPT ![self] = @ \cup {cmd}]
              ELSE
                /\ UNCHANGED << spec_pool >>
    /\ UNCHANGED << leader, uncommitted_pool, committed_log, client_responses >>

ClientHandleFastPath(cmd_id) ==
    /\ cmd_id \in DOMAIN client_responses
    /\ client_responses[cmd_id].status = "pending"
    /\ LET leader_reply_msg == {m \in BagToSet(network) : m.type = "propose_reply" /\ m.cmd_id = cmd_id}
       IN \/ leader_reply_msg = {}
          \/ LET leader_reply == CHOOSE m \in leader_reply_msg : TRUE
             IN \/ leader_reply.conflict = TRUE
                \/ LET follower_replies == {m \in BagToSet(network) : m.type = "record_reply" /\ m.cmd_id = cmd_id}
                       non_conflict_acks == {m.from : m \in follower_replies | ~m.conflict} \cup {leader}
                   IN Cardinality(non_conflict_acks) < SuperQuorum(Server)
    /\ client_responses' = [client_responses EXCEPT ![cmd_id].status = "slow_path_wait"]
    /\ UNCHANGED << leader, spec_pool, uncommitted_pool, committed_log, network >>

ClientHandleFastPathSuccess(cmd_id) ==
    /\ cmd_id \in DOMAIN client_responses
    /\ client_responses[cmd_id].status = "pending"
    /\ \E leader_reply \in BagToSet(network):
        /\ leader_reply.type = "propose_reply"
        /\ leader_reply.cmd_id = cmd_id
        /\ leader_reply.conflict = FALSE
        /\ LET follower_replies == {m \in BagToSet(network) : m.type = "record_reply" /\ m.cmd_id = cmd_id}
               non_conflict_acks == {m.from : m \in follower_replies | ~m.conflict} \cup {leader}
           IN Cardinality(non_conflict_acks) >= SuperQuorum(Server)
    /\ client_responses' = [client_responses EXCEPT ![cmd_id].status = "fast_path_ok"]
    /\ UNCHANGED << leader, spec_pool, uncommitted_pool, committed_log, network >>

Commit(cmd) ==
    /\ cmd \in uncommitted_pool[leader]
    /\ \A i \in DOMAIN committed_log : committed_log[i].id /= cmd.id
    /\ committed_log' = Append(committed_log, cmd)
    /\ network' = network \cup+ Bag({[type |-> "commit", cmd |-> cmd, to |-> s] : s \in Server})
    /\ IF cmd.id \in DOMAIN client_responses /\ client_responses[cmd.id].status /= "fast_path_ok" THEN
        client_responses' = [client_responses EXCEPT ![cmd.id].status = "slow_path_ok"]
       ELSE
        client_responses' = client_responses
    /\ UNCHANGED << leader, spec_pool, uncommitted_pool >>

ProcessCommitMsg(self) ==
    /\ \E msg \in BagToSet(network):
        /\ msg.type = "commit"
        /\ msg.to = self
        /\ LET cmd == msg.cmd IN
            /\ network' = network \- Bag({msg})
            /\ spec_pool' = [spec_pool EXCEPT ![self] = @ \ {cmd}]
            /\ uncommitted_pool' = [uncommitted_pool EXCEPT ![self] = @ \ {cmd}]
    /\ UNCHANGED << leader, committed_log, client_responses >>

LeaderChange(new_leader) ==
    /\ new_leader \in Server
    /\ new_leader /= leader
    /\ \E voter_quorum \subseteq Server:
        /\ Cardinality(voter_quorum) >= Quorum(Server)
        /\ LET collected_cmds == UNION {s \in voter_quorum : spec_pool[s]}
               recovered_cmds == {c \in collected_cmds : Cardinality({s \in Server : c \in spec_pool[s]}) >= RecoverQuorum(Server)}
           IN
           /\ leader' = new_leader
           /\ spec_pool' = [spec_pool EXCEPT ![new_leader] = recovered_cmds]
           /\ uncommitted_pool' = [uncommitted_pool EXCEPT ![new_leader] = recovered_cmds]
    /\ UNCHANGED << committed_log, network, client_responses >>

Next ==
    \/ \E cmd \in Command : ClientPropose(cmd)
    \/ ProcessProposeLeader
    \/ \E s \in Server : ProcessRecordRequest(s)
    \/ \E cid \in DOMAIN client_responses : ClientHandleFastPath(cid)
    \/ \E cid \in DOMAIN client_responses : ClientHandleFastPathSuccess(cid)
    \/ \E cmd \in Command : Commit(cmd)
    \/ \E s \in Server : ProcessCommitMsg(s)
    \/ \E l \in Server : LeaderChange(l)

Spec == Init /\ [][Next]_vars

====