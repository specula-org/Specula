---- MODULE spin ----
EXTENDS Naturals, Sequences

CONSTANTS Threads

VARIABLES holder, status

TypeOK == 
  /\ holder \subseteq Threads
  /\ Cardinality(holder) <= 1
  /\ status \in [Threads -> {"out", "trying", "critical"}]

Init == 
  /\ holder = {}
  /\ status = [t \in Threads |-> "out"]

Start(t) == 
  /\ status[t] = "out"
  /\ status' = [status EXCEPT ![t] = "trying"]
  /\ UNCHANGED holder

Success(t) == 
  /\ status[t] = "trying"
  /\ holder = {}
  /\ holder' = {t}
  /\ status' = [status EXCEPT ![t] = "critical"]

Release(t) == 
  /\ status[t] = "critical"
  /\ holder = {t}
  /\ holder' = {}
  /\ status' = [status EXCEPT ![t] = "out"]

Next == \E t \in Threads: Start(t) \/ Success(t) \/ Release(t)

MutualExclusion == 
  \A t1, t2 \in Threads: 
    ~ (status[t1] = "critical" /\ status[t2] = "critical" /\ t1 /= t2)

Consistency == 
  \A t \in Threads: 
    (status[t] = "critical" => holder = {t})
  /\ (holder # {} => \E t \in Threads: holder = {t} /\ status[t] = "critical")

Invariant == TypeOK /\ MutualExclusion /\ Consistency

====