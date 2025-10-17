---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets

CONSTANTS
    Threads,    \* The set of threads
    Nil         \* A value not in Threads

(* Bitmask constants for the lock state *)
READER           == 1
BEING_UPGRADED   == 2^(61)
UPGRADEABLE_READER == 2^(62)
WRITER           == 2^(63)
READER_MASK      == BEING_UPGRADED - 1

RECURSIVE BitwiseAnd(_,_)
BitwiseAnd(a, b) ==
    IF a = 0 \/ b = 0 THEN 0
    ELSE (2 * BitwiseAnd(a \div 2, b \div 2)) + ((a % 2) * (b % 2))

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
    /\ writer \in Threads \cup {{Nil}}
    /\ up_reader \in Threads \cup {{Nil}}
    /\ upgrading_thread \in Threads \cup {{Nil}}
    /\ Cardinality({{t \in {{writer, up_reader, upgrading_thread}} \ {{Nil}} : TRUE}}) \in {{0, 1}}
    /\ readers \cap ({{writer, up_reader, upgrading_thread}} \ {{Nil}}) = {{}}
    /\ (writer # Nil) <=> ((lock \div WRITER) % 2 = 1)
    /\ (up_reader # Nil \/ upgrading_thread # Nil) <=> ((lock \div UPGRADEABLE_READER) % 2 = 1)
    /\ (upgrading_thread # Nil) <=> ((lock \div BEING_UPGRADED) % 2 = 1)
    /\ Cardinality(readers) = BitwiseAnd(lock, READER_MASK)

Init ==
    /\ lock = 0
    /\ wait_queue = <<>>
    /\ readers = {{}}
    /\ writer = Nil
    /\ up_reader = Nil
    /\ upgrading_thread = Nil

AcquireRead(self) ==
    /\ \lnot IsActive(self)
    /\ \lnot IsWaiting(self)
    /\ LET prev_lock == lock IN
       IF BitwiseAnd(prev_lock, WRITER + BEING_UPGRADED) = 0 THEN
            /\ lock' = lock + READER
            /\ readers' = readers \cup {{self}}
            /\ UNCHANGED <<wait_queue, writer, up_reader, upgrading_thread>>
       ELSE
            /\ wait_queue' = Append(wait_queue, self)
            /\ UNCHANGED <<lock, readers, writer, up_reader, upgrading_thread>>

ReleaseRead(self) ==
    /\ self \in readers
    /\ LET prev_lock == lock IN
       /\ lock' = lock - READER
       /\ readers' = readers \ {{self}}
       /\ wait_queue' = IF BitwiseAnd(prev_lock, READER_MASK) = READER THEN
                          (IF Len(wait_queue) > 0 THEN Tail(wait_queue) ELSE <<>>)
                        ELSE
                          wait_queue
       /\ UNCHANGED <<writer, up_reader, upgrading_thread>>

AcquireWrite(self) ==
    /\ \lnot IsActive(self)
    /\ \lnot IsWaiting(self)
    /\ IF lock = 0 THEN
        /\ lock' = WRITER
        /\ writer' = self
        /\ UNCHANGED <<wait_queue, readers, up_reader, upgrading_thread>>
    ELSE
        /\ wait_queue' = Append(wait_queue, self)
        /\ UNCHANGED <<lock, readers, writer, up_reader, upgrading_thread>>

ReleaseWrite(self) ==
    /\ writer = self
    /\ lock' = lock - WRITER
    /\ writer' = Nil
    /\ wait_queue' = <<>>
    /\ UNCHANGED <<readers, up_reader, upgrading_thread>>

AcquireUpRead(self) ==
    /\ \lnot IsActive(self)
    /\ \lnot IsWaiting(self)
    /\ LET prev_lock == lock IN
       IF BitwiseAnd(prev_lock, WRITER + UPGRADEABLE_READER) = 0 THEN
            /\ lock' = lock + UPGRADEABLE_READER
            /\ up_reader' = self
            /\ UNCHANGED <<wait_queue, readers, writer, upgrading_thread>>
       ELSE
            /\ wait_queue' = Append(wait_queue, self)
            /\ UNCHANGED <<lock, readers, writer, up_reader, upgrading_thread>>

ReleaseUpRead(self) ==
    /\ up_reader = self
    /\ LET prev_lock == lock IN
       /\ lock' = lock - (UPGRADEABLE_READER + BEING_UPGRADED)
       /\ up_reader' = Nil
       /\ upgrading_thread' = IF upgrading_thread = self THEN Nil ELSE upgrading_thread
       /\ wait_queue' = IF prev_lock = UPGRADEABLE_READER THEN
                          <<>>
                        ELSE
                          wait_queue
       /\ UNCHANGED <<readers, writer>>

StartUpgrade(self) ==
    /\ up_reader = self
    /\ upgrading_thread = Nil
    /\ lock' = lock + BEING_UPGRADED
    /\ upgrading_thread' = self
    /\ UNCHANGED <<wait_queue, readers, writer, up_reader>>

FinishUpgrade(self) ==
    /\ upgrading_thread = self
    /\ IF BitwiseAnd(lock, READER_MASK) = 0 THEN
        /\ lock' = WRITER
        /\ writer' = self
        /\ up_reader' = Nil
        /\ upgrading_thread' = Nil
        /\ UNCHANGED <<wait_queue, readers>>
    ELSE
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
