---- MODULE UnknownModule ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Threads, MaxReaders

VARIABLES 
    \* Variables need to be declared based on the actions referenced in Spec
    readers,     \* Set of threads currently reading
    writers,     \* Set of threads currently writing  
    waiting,     \* Set of threads waiting
    lock_state   \* Current lock state

Vars == <<readers, writers, waiting, lock_state>>

Init == 
    /\ readers = {}
    /\ writers = {}
    /\ waiting = {}
    /\ lock_state = "free"

\* Minimal action definitions to support the Spec formula
WakeWaitingThread == 
    /\ waiting # {}
    /\ \E t \in waiting : waiting' = waiting \ {t}
    /\ UNCHANGED <<readers, writers, lock_state>>

UnlockRead(t) ==
    /\ t \in readers
    /\ readers' = readers \ {t}
    /\ UNCHANGED <<writers, waiting, lock_state>>

UnlockWrite(t) ==
    /\ t \in writers
    /\ writers' = writers \ {t}
    /\ UNCHANGED <<readers, waiting, lock_state>>

UnlockUpread(t) ==
    /\ t \in readers
    /\ readers' = readers \ {t}
    /\ UNCHANGED <<writers, waiting, lock_state>>

Next == 
    \/ WakeWaitingThread
    \/ \E t \in Threads : UnlockRead(t)
    \/ \E t \in Threads : UnlockWrite(t)
    \/ \E t \in Threads : UnlockUpread(t)

Spec == Init /\ [][Next]_Vars /\ WF_Vars(WakeWaitingThread) /\ \A t \in Threads : WF_Vars(UnlockRead(t)) /\ \A t \in Threads : WF_Vars(UnlockWrite(t)) /\ \A t \in Threads : WF_Vars(UnlockUpread(t))

====