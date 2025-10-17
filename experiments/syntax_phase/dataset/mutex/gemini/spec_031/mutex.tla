---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads

ASSUME {ToString(t) : t \in Threads} \subseteq {"t1", "t2", "t3"}

\* State encoding constants
WRITER             == 268435456 \* 2^28
UPGRADEABLE_READER == 134217728 \* 2^27
BEING_UPGRADED     == 67108864  \* 2^26

\* Helper operators to decode the state
IsWriter(s)        == (s \div WRITER) % 2 = 1
IsUpgradable(s)    == (s \div UPGRADEABLE_READER) % 2 = 1
IsUpgrading(s)     == (s \div BEING_UPGRADED) % 2 = 1
ReaderCount(s)     == s % BEING_UPGRADED

VARIABLES state, thread_status, wait_queue

vars == << state, thread_status, wait_queue >>

Status == {"idle", "waiting_read", "reading", "waiting_write", "writing",
           "waiting_upread", "upgraded", "upgrading"}

TypeOK ==
    /\ state \in Nat
    /\ thread_status \in [Threads -> Status]
    /\ wait_queue \in Seq(Threads)

Init ==
    /\ state = 0
    /\ thread_status = [t \in Threads |-> "idle"]
    /\ wait_queue = <<>>

\* A thread requests a read lock
RequestRead(t) ==
    /\ thread_status[t] = "idle"
    /\ thread_status' = [thread_status EXCEPT ![t] = "waiting_read"]
    /\ wait_queue' = Append(wait_queue, t)
    /\ UNCHANGED state

\* A waiting thread acquires a read lock
AcquireRead(t) ==
    /\ thread_status[t] = "waiting_read"
    /\ Head(wait_queue) = t
    /\ \lnot IsWriter(state)
    /\ \lnot IsUpgrading(state)
    /\ state' = state + 1
    /\ thread_status' = [thread_status EXCEPT ![t] = "reading"]
    /\ wait_queue' = Tail(wait_queue)

\* A thread releases a read lock
ReleaseRead(t) ==
    /\ thread_status[t] = "reading"
    /\ state' = state - 1
    /\ thread_status' = [thread_status EXCEPT ![t] = "idle"]
    /\ UNCHANGED wait_queue

\* A thread requests a write lock
RequestWrite(t) ==
    /\ thread_status[t] = "idle"
    /\ thread_status' = [thread_status EXCEPT ![t] = "waiting_write"]
    /\ wait_queue' = Append(wait_queue, t)
    /\ UNCHANGED state

\* A waiting thread acquires a write lock
AcquireWrite(t) ==
    /\ thread_status[t] = "waiting_write"
    /\ Head(wait_queue) = t
    /\ state = 0
    /\ state' = WRITER
    /\ thread_status' = [thread_status EXCEPT ![t] = "writing"]
    /\ wait_queue' = Tail(wait_queue)

\* A thread releases a write lock
ReleaseWrite(t) ==
    /\ thread_status[t] = "writing"
    /\ state' = 0
    /\ thread_status' = [thread_status EXCEPT ![t] = "idle"]
    /\ UNCHANGED wait_queue

\* A thread requests an upgradeable read lock
RequestUpgradableRead(t) ==
    /\ thread_status[t] = "idle"
    /\ thread_status' = [thread_status EXCEPT ![t] = "waiting_upread"]
    /\ wait_queue' = Append(wait_queue, t)
    /\ UNCHANGED state

\* A waiting thread acquires an upgradeable read lock
AcquireUpgradableRead(t) ==
    /\ thread_status[t] = "waiting_upread"
    /\ Head(wait_queue) = t
    /\ \lnot IsWriter(state)
    /\ \lnot IsUpgradable(state)
    /\ state' = state + UPGRADEABLE_READER
    /\ thread_status' = [thread_status EXCEPT ![t] = "upgraded"]
    /\ wait_queue' = Tail(wait_queue)

\* A thread releases an upgradeable read lock
ReleaseUpgradableRead(t) ==
    /\ thread_status[t] = "upgraded"
    /\ state' = state - UPGRADEABLE_READER
    /\ thread_status' = [thread_status EXCEPT ![t] = "idle"]
    /\ UNCHANGED wait_queue

\* An upgradeable reader starts the upgrade process
StartUpgrade(t) ==
    /\ thread_status[t] = "upgraded"
    /\ state' = state + BEING_UPGRADED
    /\ thread_status' = [thread_status EXCEPT ![t] = "upgrading"]
    /\ UNCHANGED wait_queue

\* An upgrading thread completes the upgrade when all readers are gone
CompleteUpgrade(t) ==
    /\ thread_status[t] = "upgrading"
    /\ ReaderCount(state) = 0
    /\ state' = (state - UPGRADEABLE_READER - BEING_UPGRADED) + WRITER
    /\ thread_status' = [thread_status EXCEPT ![t] = "writing"]
    /\ UNCHANGED wait_queue

\* A writer atomically downgrades to an upgradeable reader
Downgrade(t) ==
    /\ thread_status[t] = "writing"
    /\ state' = (state - WRITER) + UPGRADEABLE_READER
    /\ thread_status' = [thread_status EXCEPT ![t] = "upgraded"]
    /\ UNCHANGED wait_queue

Progress(t) ==
    \/ RequestRead(t)
    \/ AcquireRead(t)
    \/ ReleaseRead(t)
    \/ RequestWrite(t)
    \/ AcquireWrite(t)
    \/ ReleaseWrite(t)
    \/ RequestUpgradableRead(t)
    \/ AcquireUpgradableRead(t)
    \/ ReleaseUpgradableRead(t)
    \/ StartUpgrade(t)
    \/ CompleteUpgrade(t)
    \/ Downgrade(t)

Next == \E t \in Threads : Progress(t)

Spec == Init /\ [][Next]_vars /\ \A t \in Threads : WF_vars(Progress(t))

====