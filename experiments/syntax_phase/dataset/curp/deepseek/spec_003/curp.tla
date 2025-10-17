---- MODULE curp ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags
CONSTANTS Replicas, Keys
VARIABLES spec_pool, uncommitted_pool, log_entries, commit_index, applied_index, term, leader_id, role, voted_for
vars == <<spec_pool, uncommitted_pool, log_entries, commit_index, applied_index, term, leader_id, role, voted_for>>
QuorumSize == Cardinality(Replicas) \div 2 + 1
RecoverQuorumSize == QuorumSize \div 2 + 1
IsQuorum(Q) == Cardinality(Q) >= QuorumSize
Max(S) == CHOOSE x \in S : \A y \in S : y <= x
Init == 
  /\ spec_pool = [r \in Replicas |-> {}]
  /\ uncommitted_pool = [r \in Replicas |-> {}]
  /\ log_entries = [r \in Replicas |-> <<>>]
  /\ commit_index = [r \in Replicas |-> 0]
  /\ applied_index = [r \in Replicas |-> 0]
  /\ term = [r \in Replicas |-> 0]
  /\ leader_id = [r \in Replicas |-> "Nil"]
  /\ role = [r \in Replicas |-> "Follower"]
  /\ voted_for = [r \in Replicas |-> "Nil"]
ProcessProposeLeader(r, cmd) ==
  /\ role[r] = "Leader"
  /\ cmd \notin spec_pool[r]
  /\ cmd \notin uncommitted_pool[r]
  /\ spec_pool' = [spec_pool EXCEPT ![r] = @ \cup {cmd}]
  /\ uncommitted_pool' = [uncommitted_pool EXCEPT ![r] = @ \cup {cmd}]
  /\ log_entries' = [log_entries EXCEPT ![r] = Append(@, cmd)]
  /\ UNCHANGED <<commit_index, applied_index, term, leader_id, role, voted_for>>
ProcessProposeNonLeader(r, cmd) ==
  /\ role[r] # "Leader"
  /\ cmd \notin spec_pool[r]
  /\ spec_pool' = [spec_pool EXCEPT ![r] = @ \cup {cmd}]
  /\ UNCHANGED <<uncommitted_pool, log_entries, commit_index, applied_index, term, leader_id, role, voted_for>>
Commit(r, i) ==
  /\ i \in 1..Len(log_entries[r])
  /\ i > commit_index[r]
  /\ \E Q \in SUBSET Replicas : 
        IsQuorum(Q) 
        /\ \A q \in Q : i <= Len(log_entries[q]) /\ log_entries[q][i] = log_entries[r][i]
  /\ commit_index' = [commit_index EXCEPT ![r] = i]
  /\ UNCHANGED <<spec_pool, uncommitted_pool, log_entries, applied_index, term, leader_id, role, voted_for>>
ProcessCommitMsg(r, cmd) ==
  LET i = CHOOSE j \in 1..Len(log_entries[r]) : log_entries[r][j] = cmd IN
  /\ commit_index[r] >= i
  /\ applied_index[r] < i
  /\ applied_index' = [applied_index EXCEPT ![r] = i]
  /\ spec_pool' = [spec_pool EXCEPT ![r] = @ \ {cmd}]
  /\ uncommitted_pool' = [uncommitted_pool EXCEPT ![r] = @ \ {cmd}]
  /\ UNCHANGED <<log_entries, commit_index, term, leader_id, role, voted_for>>
LeaderChange(l) ==
  /\ role[l] # "Leader"
  /\ term' = [term EXCEPT ![l] = Max({term[r] : r \in Replicas}) + 1]
  /\ role' = [role EXCEPT ![l] = "Leader"]
  /\ leader_id' = [leader_id EXCEPT ![l] = l]
  /\ voted_for' = [voted_for EXCEPT ![l] = "Nil"]
  /\ LET recovered_keys = {k \in Keys : Cardinality({r \in Replicas : k \in spec_pool[r]}) >= RecoverQuorumSize} IN
     ( spec_pool' = [spec_pool EXCEPT ![l] = @ \cup recovered_keys] /\
       uncommitted_pool' = [uncommitted_pool EXCEPT ![l] = @ \cup recovered_keys] )
  /\ UNCHANGED <<log_entries, commit_index, applied_index>>
Next == 
  \/ \E r \in Replicas, cmd \in Keys : ProcessProposeLeader(r, cmd)
  \/ \E r \in Replicas, cmd \in Keys : ProcessProposeNonLeader(r, cmd)
  \/ \E r \in Replicas, i \in Nat : Commit(r, i)
  \/ \E r \in Replicas, cmd \in Keys : ProcessCommitMsg(r, cmd)
  \/ \E l \in Replicas : LeaderChange(l)
Spec == Init /\ [][Next]_vars
====