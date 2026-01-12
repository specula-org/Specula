---- MODULE ringbuffer ----
EXTENDS Naturals, TLC

VARIABLES rbs

vars == <<rbs>>

RBState == [head: Nat, tail: Nat, capacity: Nat]

RBIds == DOMAIN rbs

IsPowerOfTwo(n) ==
    /\ n > 0
    /\ \E k \in 0..n : n = 2^k

RbOk(st) ==
    /\ st.head <= st.tail
    /\ st.capacity > 0
    /\ IsPowerOfTwo(st.capacity)
    /\ st.tail - st.head <= st.capacity

TypeOK ==
    \A rb \in RBIds : RbOk(rbs[rb])

Init ==
    rbs = [i \in {} |-> [head |-> 0, tail |-> 0, capacity |-> 0]]

Create(rb, cap) ==
    /\ rb \notin RBIds
    /\ IsPowerOfTwo(cap)
    /\ cap > 0
    /\ rbs' = rbs @@ [i \in {rb} |-> [head |-> 0, tail |-> 0, capacity |-> cap]]

Split(rb) ==
    /\ rb \in RBIds
    /\ UNCHANGED rbs

PushItems(rb, n) ==
    /\ rb \in RBIds
    /\ n \in Nat \ {0}
    /\ LET st == rbs[rb] IN st.tail - st.head + n <= st.capacity
    /\ rbs' = [rbs EXCEPT ![rb].tail = @ + n]

PopItems(rb, n) ==
    /\ rb \in RBIds
    /\ n \in Nat \ {0}
    /\ LET st == rbs[rb] IN st.tail - st.head >= n
    /\ rbs' = [rbs EXCEPT ![rb].head = @ + n]

PushFail(rb) ==
    /\ rb \in RBIds
    /\ LET st == rbs[rb] IN st.tail - st.head = st.capacity
    /\ UNCHANGED rbs

PopFail(rb) ==
    /\ rb \in RBIds
    /\ LET st == rbs[rb] IN st.tail = st.head
    /\ UNCHANGED rbs

Next ==
    \/ \E rb \in Nat, cap \in Nat : Create(rb, cap)
    \/ \E rb \in RBIds : Split(rb)
    \/ \E rb \in RBIds, n \in Nat \ {0} : (PushItems(rb, n) \/ PopItems(rb, n))
    \/ \E rb \in RBIds : (PushFail(rb) \/ PopFail(rb))

Spec ==
    Init /\ [][Next]_vars

====
