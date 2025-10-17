---- MODULE curp ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Replicas, Keys, Values, CommandIds

ASSUME IsFiniteSet(Replicas) /\ Cardinality(Replicas) >= 1
ASSUME IsFiniteSet(Keys)
ASSUME IsFiniteSet(Values)
ASSUME IsFiniteSet(CommandIds)

Commands == [ id: CommandIds, key: Keys, val: Values ]

GetCommandKey(cmd) == cmd.key

Conflicts(cmd1, cmd2) == GetCommandKey(cmd1) = GetCommandKey(cmd2)

Quorum(size) == (size \div 2) + 1
RecoverQuorum(size) == Quorum(size) \div 2 + 1
SuperQuorum(size) == (size - Quorum(size)) + RecoverQuorum(size)

VARIABLES
    leader,
    speculative_pool,
    uncommitted_pool,
    kv_store,
    propose_messages,
    propose_responses,
    client_status,
    committed_cmds,
    applied_cmds

vars == << leader, speculative_pool, uncommitted_pool, kv_store,
           propose_messages, propose_responses, client_status,
           committed_cmds, applied_cmds >>

TypeOK ==
    /\ leader \in Replicas
    /\ speculative_pool \in [Replicas -> SUBSET Commands]
    /\ uncommitted_pool \in [Replicas -> SUBSET Commands]
    /\ kv_store \in [Replicas -> [Keys -> Values]]
    /\ propose_messages \in [Replicas -> SUBSET Commands]
    /\ propose_responses \in [Commands -> Bag({"fast", "slow"})]
    /\ client_status \in [Commands -> {"unproposed", "proposed", "speculated", "committed_wait", "committed"}]
    /\ committed_cmds \in SUBSET Commands
    /\ applied_cmds \in [Replicas -> SUBSET Commands]

Init ==
    /\ \E r \in Replicas : leader = r
    /\ speculative_pool = [r \in Replicas |-> {}]
    /\ uncommitted_pool = [r \in Replicas |-> {}]
    /\ \E f \in [Keys -> Values] : kv_store = [r \in Replicas |-> f]
    /\ propose_messages = [r \in Replicas |-> {}]
    /\ propose_responses = [cmd \in Commands |-> EmptyBag]
    /\ client_status = [cmd \in Commands |-> "unproposed"]
    /\ committed_cmds = {}
    /\ applied_cmds = [r \in Replicas |-> {}]

Propose(cmd) ==
    /\ client_status[cmd] = "unproposed"
    /\ client_status' = [client_status EXCEPT ![cmd] = "proposed"]
    /\ propose_messages' = [r \in Replicas |-> propose_messages[r] \cup {cmd}]
    /\ UNCHANGED << leader, speculative_pool, uncommitted_pool, kv_store,
                    propose_responses, committed_cmds, applied_cmds >>

ProcessPropose(r) ==
    /\ propose_messages[r] /= {}
    /\ \E cmd \in propose_messages[r] :
        LET is_leader == r = leader
            conflict_set == IF is_leader THEN speculative_pool[r] \cup uncommitted_pool[r] ELSE speculative_pool[r]
            has_conflict == \E other \in conflict_set : Conflicts(cmd, other)
        IN
        /\ propose_messages' = [propose_messages EXCEPT ![r] = @ \ {cmd}]
        /\ propose_responses' = [propose_responses EXCEPT ![cmd] = @ (+) << IF has_conflict THEN "slow" ELSE "fast" >>]
        /\ speculative_pool' = IF has_conflict THEN speculative_pool ELSE [speculative_pool EXCEPT ![r] = @ \cup {cmd}]
        /\ uncommitted_pool' = IF is_leader THEN [uncommitted_pool EXCEPT ![r] = @ \cup {cmd}] ELSE uncommitted_pool
        /\ UNCHANGED << leader, kv_store, client_status, committed_cmds, applied_cmds >>

ClientConclude(cmd) ==
    /\ client_status[cmd] = "proposed"
    /\ Cardinality(propose_responses[cmd]) >= SuperQuorum(Cardinality(Replicas))
    /\ LET is_fast_path == \A resp \in {"fast", "slow"} :
                            Items(propose_responses[cmd], resp) > 0 => resp = "fast"
       IN client_status' = [client_status EXCEPT ![cmd] = IF is_fast_path THEN "speculated" ELSE "committed_wait"]
    /\ UNCHANGED << leader, speculative_pool, uncommitted_pool, kv_store,
                    propose_messages, propose_responses, committed_cmds, applied_cmds >>

Commit(cmd) ==
    /\ cmd \in uncommitted_pool[leader]
    /\ cmd \notin committed_cmds
    /\ committed_cmds' = committed_cmds \cup {cmd}
    /\ UNCHANGED << leader, speculative_pool, uncommitted_pool, kv_store,
                    propose_messages, propose_responses, client_status, applied_cmds >>

Apply(r, cmd) ==
    /\ cmd \in committed_cmds
    /\ cmd \notin applied_cmds[r]
    /\ applied_cmds' = [applied_cmds EXCEPT ![r] = @ \cup {cmd}]
    /\ kv_store' = [kv_store EXCEPT ![r] = [ @ EXCEPT ![cmd.key] = cmd.val ]]
    /\ speculative_pool' = [speculative_pool EXCEPT ![r] = @ \ {cmd}]
    /\ uncommitted_pool' = [uncommitted_pool EXCEPT ![r] = @ \ {cmd}]
    /\ client_status' = [client_status EXCEPT ![cmd] = "committed"]
    /\ UNCHANGED << leader, propose_messages, propose_responses, committed_cmds >>

LeaderChange(new_leader) ==
    /\ new_leader \in Replicas
    /\ new_leader # leader
    /\ \E QuorumMembers \subseteq Replicas :
        /\ Cardinality(QuorumMembers) = RecoverQuorum(Cardinality(Replicas))
        /\ LET CollectedPools == { speculative_pool[m] : m \in QuorumMembers }
               AllCollectedCmds == UNION S \in CollectedPools : S
               CmdCounts == [c \in AllCollectedCmds |-> Cardinality({p \in CollectedPools : c \in p})]
               RecoveredUncommitted == { c \in AllCollectedCmds : CmdCounts[c] >= RecoverQuorum(Cardinality(Replicas)) }
           IN
            /\ leader' = new_leader
            /\ uncommitted_pool' = [uncommitted_pool EXCEPT ![new_leader] = RecoveredUncommitted]
            /\ speculative_pool' = [speculative_pool EXCEPT ![new_leader] = AllCollectedCmds]
            /\ UNCHANGED << kv_store, propose_messages, propose_responses,
                            client_status, committed_cmds, applied_cmds >>

Next ==
    \/ \E cmd \in Commands : Propose(cmd)
    \/ \E r \in Replicas : ProcessPropose(r)
    \/ \E cmd \in Commands : ClientConclude(cmd)
    \/ \E cmd \in Commands : Commit(cmd)
    \/ \E r \in Replicas, cmd \in Commands : Apply(r, cmd)
    \/ \E l \in Replicas : LeaderChange(l)

Spec == Init /\ [][Next]_vars

====