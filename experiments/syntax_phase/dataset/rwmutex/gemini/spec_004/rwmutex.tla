---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS
    Threads,    \* The set of threads
    Nil         \* A value not in Threads

(* Bitmask constants for the lock state *)
READER           == 1
BEING_UPGRADED   == 2^(61)
UPGRADEABLE_READER == 2^(62)
WRITER           == 2^(63)
READER_MASK      == BEING_UPGRADED - 1

VARIABLES
    lock,             \* The atomic usize state
    wait_queue,       \* FIFO queue of waiting threads
    readers,          \* Set of threads holding a read lock
    writer,           \* The thread holding the write lock, or Nil
    up_reader,        \* The thread holding the upgradeable read lock, or Nil
    upgrading_thread  \* The thread attempting to upgrade, or Nil

Vars == <<lock, wait_queue, readers, writer, up_reader, upgrading_thread>>

IsWaiting(t) == \E i \in 1..Len(wait_queue): wait_queue[i] = t
IsActive(t) == t \in readers \/ t = writer \/ t = up_reader \/ t = upgrading_thread

TypeOK ==
    /\ lock \in Nat
    /\ wait_queue \in Seq(Threads)
    /\ readers \subseteq Threads
    /\ writer \in Threads \cup {Nil}
    /\ up_reader \in Threads \cup {Nil}
    /\ upgrading_thread \in Threads \cup {Nil}
    /\ Cardinality({t \in {writer, up_reader, upgrading_thread} \ {Nil} : TRUE}) \in {0, 1}
    /\ readers \cap {writer, up_reader, upgrading_thread} = {}
    /\ (writer # Nil) <=> ((lock \div WRITER) % 2 = 1)
    /\ (up_reader # Nil \/ upgrading_thread # Nil) <=> ((lock \div UPGRADEABLE_READER) % 2 = 1)
    /\ (upgrading_thread # Nil) <=> ((lock \div BEING_UPGRADED) % 2 = 1)
    /\ Cardinality(readers) = (lock \cap READER_MASK)

Init ==
    /\ lock = 0
    /\ wait_queue = <<>>
    /\ readers = {}
    /\ writer = Nil
    /\ up_reader = Nil
    /\ upgrading_thread = Nil

AcquireRead(self) ==
    /\ \lnot IsActive(self)
    /\ \lnot IsWaiting(self)
    /\ LET prev_lock == lock IN
       /\ IF (prev_lock \cap (WRITER \cup BEING_UPGRADED)) = 0 THEN
            /\ lock' = lock + READER
            /\ readers' = readers \cup {self}
            /\ UNCHANGED <<wait_queue, writer, up_reader, upgrading_thread>>
       /\ ELSE
            /\ wait_queue' = Append(wait_queue, self)
            /\ UNCHANGED <<lock, readers, writer, up_reader, upgrading_thread>>

ReleaseRead(self) ==
    /\ self \in readers
    /\ LET prev_lock == lock IN
       /\ lock' = lock - READER
       /\ readers' = readers \ {self}
       /\ IF (prev_lock \cap READER_MASK) = READER THEN
            /\ wait_queue' = IF Len(wait_queue) > 0 THEN Tail(wait_queue) ELSE <<>>
       /\ ELSE
            /\ UNCHANGED wait_queue
       /\ UNCHANGED <<writer, up_reader, upgrading_thread>>

AcquireWrite(self) ==
    /\ \lnot IsActive(self)
    /\ \lnot IsWaiting(self)
    /\ IF lock = 0 THEN
        /\ lock' = WRITER
        /\ writer' = self
        /\ UNCHANGED <<wait_queue, readers, up_reader, upgrading_thread>>
    /\ ELSE
        /\ wait_queue' = Append(wait_queue, self)
        /\ UNCHANGED <<lock, readers, writer, up_reader, upgrading_thread>>

ReleaseWrite(self) ==
    /\ writer = self
    /\ lock' = lock \cap \ {WRITER}
    /\ writer' = Nil
    /\ wait_queue' = <<>>
    /\ UNCHANGED <<readers, up_reader, upgrading_thread>>

AcquireUpRead(self) ==
    /\ \lnot IsActive(self)
    /\ \lnot IsWaiting(self)
    /\ LET prev_lock == lock IN
       /\ IF (prev_lock \cap (WRITER \cup UPGRADEABLE_READER)) = 0 THEN
            /\ lock' = lock \cup UPGRADEABLE_READER
            /\ up_reader' = self
            /\ UNCHANGED <<wait_queue, readers, writer, upgrading_thread>>
       /\ ELSE
            /\ wait_queue' = Append(wait_queue, self)
            /\ UNCHANGED <<lock, readers, writer, up_reader, upgrading_thread>>

ReleaseUpRead(self) ==
    /\ up_reader = self
    /\ LET prev_lock == lock IN
       /\ lock' = lock \cap \ {UPGRADEABLE_READER, BEING_UPGRADED}
       /\ up_reader' = Nil
       /\ upgrading_thread' = IF upgrading_thread = self THEN Nil ELSE upgrading_thread
       /\ IF prev_lock = UPGRADEABLE_READER THEN
            /\ wait_queue' = <<>>
       /\ ELSE
            /\ UNCHANGED wait_queue
       /\ UNCHANGED <<readers, writer>>

StartUpgrade(self) ==
    /\ up_reader = self
    /\ upgrading_thread = Nil
    /\ lock' = lock \cup BEING_UPGRADED
    /\ upgrading_thread' = self
    /\ UNCHANGED <<wait_queue, readers, writer, up_reader>>

FinishUpgrade(self) ==
    /\ upgrading_thread = self
    /\ IF (lock \cap READER_MASK) = 0 THEN
        /\ lock' = WRITER
        /\ writer' = self
        /\ up_reader' = Nil
        /\ upgrading_thread' = Nil
        /\ UNCHANGED <<wait_queue, readers>>
    /\ ELSE
        /\ UNCHANGED Vars

Downgrade(self) ==
    /\ writer = self
    /\ lock' = UPGRADEABLE_READER
    /\ writer' = Nil
    /\ up_reader' = self
    /\ UNCHANGED <<wait_queue, readers, upgrading_thread>>

Next ==
    \E self \in Threads:
        \/ AcquireRead(self)
        \/ ReleaseRead(self)
        \/ AcquireWrite(self)
        \/ ReleaseWrite(self)
        \/ AcquireUpRead(self)
        \/ ReleaseUpRead(self)
        \/ StartUpgrade(self)
        \/ FinishUpgrade(self)
        \/ Downgrade(self)

Spec == Init /\ [][Next]_Vars /\ WF_Vars(Next)

====