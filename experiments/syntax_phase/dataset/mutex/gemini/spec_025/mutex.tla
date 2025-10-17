---- MODULE rwmutex ----
EXTENDS TLC, Sequences, Naturals, FiniteSets, Bags

CONSTANTS Proc
ASSUME Proc = {"p1", "p2", "p3"}

WRITER             == 1
UPGRADEABLE_READER == 2
BEING_UPGRADED     == 4
READER_UNIT        == 8

ReaderCount(s)      == s \div READER_UNIT
IsWriter(s)         == (s \div WRITER) % 2 = 1
IsUpgradable(s)     == (s \div UPGRADEABLE_READER) % 2 = 1
IsUpgrading(s)      == (s \div BEING_UPGRADED) % 2 = 1

VARIABLES state, pc, wait_queue

vars == <<state, pc, wait_queue>>

TypeOK ==
    /\ state \in Nat
    /\ pc \in [Proc -> {"idle", "req_read", "reading", "req_write", "writing",
                        "req_upread", "upreading", "upgrading", "blocked"}]
    /\ wait_queue \in Seq([proc: Proc, type: {"read", "write", "upread"}])

Init ==
    /\ state = 0
    /\ pc = [p \in Proc |-> "idle"]
    /\ wait_queue = <<>>

RequestRead(p) ==
    /\ pc[p] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "req_read"]
    /\ UNCHANGED <<state, wait_queue>>

TryAcquireRead(p) ==
    /\ pc[p] = "req_read"
    /\ \lnot IsWriter(state) /\ \lnot IsUpgradable(state) /\ \lnot IsUpgrading(state)
    /\ state' = state + READER_UNIT
    /\ pc' = [pc EXCEPT ![p] = "reading"]
    /\ UNCHANGED <<wait_queue>>

BlockRead(p) ==
    /\ pc[p] = "req_read"
    /\ (IsWriter(state) \/ IsUpgradable(state) \/ IsUpgrading(state))
    /\ wait_queue' = Append(wait_queue, [proc |-> p, type |-> "read"])
    /\ pc' = [pc EXCEPT ![p] = "blocked"]
    /\ UNCHANGED <<state>>

ReleaseRead(p) ==
    /\ pc[p] = "reading"
    /\ (LET new_state == state - READER_UNIT
       IN /\ state' = new_state
          /\ IF new_state = 0 /\ Len(wait_queue) > 0
             THEN LET woken == Head(wait_queue)
                  IN /\ pc' = [pc EXCEPT ![p] = "idle", ![woken["proc"]] = "req_" \o woken["type"]]
                     /\ wait_queue' = Tail(wait_queue)
             ELSE /\ pc' = [pc EXCEPT ![p] = "idle"]
                  /\ UNCHANGED <<wait_queue>>)

RequestWrite(p) ==
    /\ pc[p] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "req_write"]
    /\ UNCHANGED <<state, wait_queue>>

TryAcquireWrite(p) ==
    /\ pc[p] = "req_write"
    /\ state = 0
    /\ state' = WRITER
    /\ pc' = [pc EXCEPT ![p] = "writing"]
    /\ UNCHANGED <<wait_queue>>

BlockWrite(p) ==
    /\ pc[p] = "req_write"
    /\ state /= 0
    /\ wait_queue' = Append(wait_queue, [proc |-> p, type |-> "write"])
    /\ pc' = [pc EXCEPT ![p] = "blocked"]
    /\ UNCHANGED <<state>>

ReleaseWrite(p) ==
    /\ pc[p] = "writing"
    /\ state' = 0
    /\ (LET WokenProcsSet == {wq["proc"] : wq \in {wait_queue[i] : i \in 1..Len(wait_queue)}}
           Unblock(q) == "req_" \o (CHOOSE r \in {wait_queue[i] : i \in 1..Len(wait_queue)} : r["proc"] = q)["type"]
       IN /\ pc' = [q \in Proc |-> IF q = p THEN "idle"
                                    ELSE IF q \in WokenProcsSet THEN Unblock(q)
                                    ELSE pc[q]]
          /\ wait_queue' = <<>>)

RequestUpgradableRead(p) ==
    /\ pc[p] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "req_upread"]
    /\ UNCHANGED <<state, wait_queue>>

TryAcquireUpgradableRead(p) ==
    /\ pc[p] = "req_upread"
    /\ state = 0
    /\ state' = UPGRADEABLE_READER
    /\ pc' = [pc EXCEPT ![p] = "upreading"]
    /\ UNCHANGED <<wait_queue>>

BlockUpgradableRead(p) ==
    /\ pc[p] = "req_upread"
    /\ state /= 0
    /\ wait_queue' = Append(wait_queue, [proc |-> p, type |-> "upread"])
    /\ pc' = [pc EXCEPT ![p] = "blocked"]
    /\ UNCHANGED <<state>>

ReleaseUpgradableRead(p) ==
    /\ pc[p] = "upreading"
    /\ state' = 0
    /\ (LET WokenProcsSet == {wq["proc"] : wq \in {wait_queue[i] : i \in 1..Len(wait_queue)}}
           Unblock(q) == "req_" \o (CHOOSE r \in {wait_queue[i] : i \in 1..Len(wait_queue)} : r["proc"] = q)["type"]
       IN /\ pc' = [q \in Proc |-> IF q = p THEN "idle"
                                    ELSE IF q \in WokenProcsSet THEN Unblock(q)
                                    ELSE pc[q]]
          /\ wait_queue' = <<>>)

StartUpgrade(p) ==
    /\ pc[p] = "upreading"
    /\ state' = state + BEING_UPGRADED
    /\ pc' = [pc EXCEPT ![p] = "upgrading"]
    /\ UNCHANGED <<wait_queue>>

CompleteUpgrade(p) ==
    /\ pc[p] = "upgrading"
    /\ ReaderCount(state) = 0
    /\ state' = WRITER
    /\ pc' = [pc EXCEPT ![p] = "writing"]
    /\ UNCHANGED <<wait_queue>>

Downgrade(p) ==
    /\ pc[p] = "writing"
    /\ state' = UPGRADEABLE_READER
    /\ pc' = [pc EXCEPT ![p] = "upreading"]
    /\ UNCHANGED <<wait_queue>>

PStep(p) ==
    \/ RequestRead(p)
    \/ TryAcquireRead(p)
    \/ BlockRead(p)
    \/ ReleaseRead(p)
    \/ RequestWrite(p)
    \/ TryAcquireWrite(p)
    \/ BlockWrite(p)
    \/ ReleaseWrite(p)
    \/ RequestUpgradableRead(p)
    \/ TryAcquireUpgradableRead(p)
    \/ BlockUpgradableRead(p)
    \/ ReleaseUpgradableRead(p)
    \/ StartUpgrade(p)
    \/ CompleteUpgrade(p)
    \/ Downgrade(p)

Next == \E p \in Proc : PStep(p)

Spec == Init /\ [][Next]_vars /\ \A p \in Proc : WF_vars(PStep(p))

====
```