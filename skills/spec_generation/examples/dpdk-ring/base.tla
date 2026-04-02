---- MODULE base ----
(***************************************************************************)
(* TLA+ specification of DPDK rte_ring — a lock-free multi-producer /     *)
(* multi-consumer ring buffer.                                             *)
(*                                                                         *)
(* Source: dpdk/lib/ring/                                                  *)
(*   rte_ring_core.h          — data structures                            *)
(*   rte_ring_c11_pvt.h       — MP/MC CAS + tail update                   *)
(*   rte_ring_elem_pvt.h      — top-level enqueue / dequeue               *)
(*   rte_ring_rts_elem_pvt.h  — RTS counter mechanism                     *)
(*   rte_ring_hts_elem_pvt.h  — HTS serialized mode                       *)
(*   rte_ring_peek_elem_pvt.h — Peek START / FINISH                       *)
(*                                                                         *)
(* Bug Families:                                                           *)
(*   F1 — Two-phase commit stall / liveness                                *)
(*   F2 — Memory ordering / stale-read vulnerabilities                     *)
(*   F3 — Peek mode atomicity gaps                                         *)
(*   F4 — RTS counter overflow / ABA                                       *)
(***************************************************************************)

EXTENDS Integers, Sequences, FiniteSets, TLC

\* ========================================================================
\* Constants
\* ========================================================================

CONSTANTS
    Thread,         \* Set of thread IDs (both producers and consumers)
    Capacity,       \* Ring usable capacity (rte_ring_core.h:124)
    Mode,           \* Ring sync mode: "MPMC", "HTS", or "RTS"
    MaxBatch,       \* Maximum elements per enqueue/dequeue batch
    HTDMax,         \* RTS: max head-tail distance (rte_ring_rts_elem_pvt.h:73)
    CntMax          \* RTS: counter wraps at this value (Family 4 — small for ABA)

ASSUME Capacity \in Nat \ {0}
ASSUME Mode \in {"MPMC", "HTS", "RTS"}
ASSUME MaxBatch \in 1..Capacity
ASSUME HTDMax \in 1..Capacity
ASSUME CntMax \in Nat \ {0}

\* ========================================================================
\* Variables
\* ========================================================================

\* --- Ring state (rte_ring_core.h:65-98) ---
VARIABLES
    prodHead,       \* Producer head position (uint32_t, rte_ring_core.h:66)
    prodTail,       \* Producer tail position (uint32_t, rte_ring_core.h:67)
    consHead,       \* Consumer head position (uint32_t, rte_ring_core.h:66)
    consTail,       \* Consumer tail position (uint32_t, rte_ring_core.h:67)
    ring            \* Ring buffer: slot index -> value (abstract)

\* --- Per-thread state (Family 1: two-phase commit window) ---
VARIABLES
    phase,          \* Thread phase: "Idle", "Reserved", "Writing", "Done"
                    \* Models the window between CAS-reserve and tail-publish
    reservedOH,     \* old_head captured by thread at CAS (rte_ring_c11_pvt.h:92)
    reservedN,      \* Number of slots reserved by thread
    side,           \* Which side thread is operating on: "prod" or "cons"
    reservedVals    \* Values thread will write (producers only)

\* --- RTS counters (Family 1, 4: rte_ring_rts_elem_pvt.h:76-83) ---
VARIABLES
    prodCnt,        \* Producer head counter (rte_ring_core.h:81)
    consCnt,        \* Consumer head counter (same)
    prodTailCnt,    \* Producer tail counter (rte_ring_core.h:86, tail.val.cnt)
    consTailCnt     \* Consumer tail counter

\* --- Stale read model (Family 2: memory ordering bugs) ---
VARIABLES
    visibleConsTail,    \* visibleConsTail[t] = producer t's view of consTail
    visibleProdTail     \* visibleProdTail[t] = consumer t's view of prodTail

\* --- Thread stall (Family 1: stall/crash between phases) ---
VARIABLES
    stalled         \* stalled[t] = TRUE if thread t is stalled/crashed

\* --- Peek mode (Family 3: START/FINISH split) ---
VARIABLES
    peekActive      \* peekActive[t] = TRUE if thread t is in peek START..FINISH

\* --- RTS stale head model (Family 4: stale RELAXED head read in update_tail) ---
VARIABLES
    rtsStaleHead    \* rtsStaleHead[t] = [valid |-> BOOLEAN, cnt |-> Nat, pos |-> Nat]
                    \* Thread t's possibly-stale view of head (cnt, pos) during publish

\* --- Dequeued values for correctness checking ---
VARIABLES
    enqueued,       \* Sequence of all values enqueued (in order of tail publish)
    dequeued        \* Sequence of all values dequeued (in order of tail publish)

\* Variable groups for UNCHANGED
ringVars    == <<prodHead, prodTail, consHead, consTail, ring>>
threadVars  == <<phase, reservedOH, reservedN, side, reservedVals>>
rtsVars     == <<prodCnt, consCnt, prodTailCnt, consTailCnt>>
staleVars   == <<visibleConsTail, visibleProdTail>>
stallVars   == <<stalled>>
peekVars    == <<peekActive>>
rtsStaleHeadVars == <<rtsStaleHead>>
historyVars == <<enqueued, dequeued>>

allVars == <<ringVars, threadVars, rtsVars, staleVars, stallVars, peekVars, rtsStaleHeadVars, historyVars>>

\* ========================================================================
\* Helpers
\* ========================================================================

\* Modular position arithmetic. In the real code, positions are uint32_t
\* and wrap at 2^32. We model a smaller domain: positions modulo
\* (2 * Capacity) which is sufficient because the ring size is always a
\* power of 2 and capacity < size.
PosRange == 0..(2 * Capacity - 1)
WrapPos(x) == x % (2 * Capacity)

\* Slot index from position (rte_ring_elem_pvt.h:161 — prod_head & r->mask)
SlotOf(pos) == pos % Capacity

\* Number of items in the ring: (prodTail - consTail) mod wrap
\* (rte_ring_c11_pvt.h:112 — capacity + stail - *old_head, for consumer: capacity=0)
ItemCount == WrapPos(prodTail - consTail + 2 * Capacity)

\* Free space: capacity - items
FreeSpace == Capacity - ItemCount

\* RTS counter increment with wraparound (Family 4)
IncCnt(c) == IF c + 1 >= CntMax THEN 0 ELSE c + 1

\* Value domain for ring elements (abstract integers starting from 1)
\* Each enqueue gets a fresh value from a global counter
VARIABLES nextVal
freshVars == <<nextVal>>

\* ========================================================================
\* Init
\* ========================================================================

Init ==
    \* Ring state: all positions start at 0 (rte_ring_core.h:66-67 after init)
    /\ prodHead = 0
    /\ prodTail = 0
    /\ consHead = 0
    /\ consTail = 0
    /\ ring = [i \in 0..(Capacity - 1) |-> 0]  \* slots initially empty (0 = no value)
    \* Thread state
    /\ phase = [t \in Thread |-> "Idle"]
    /\ reservedOH = [t \in Thread |-> 0]
    /\ reservedN = [t \in Thread |-> 0]
    /\ side = [t \in Thread |-> "none"]
    /\ reservedVals = [t \in Thread |-> <<>>]
    \* RTS counters (rte_ring_rts_elem_pvt.h — start at 0)
    /\ prodCnt = 0
    /\ consCnt = 0
    /\ prodTailCnt = 0
    /\ consTailCnt = 0
    \* Stale reads — initially accurate (Family 2)
    /\ visibleConsTail = [t \in Thread |-> 0]
    /\ visibleProdTail = [t \in Thread |-> 0]
    \* Stall (Family 1)
    /\ stalled = [t \in Thread |-> FALSE]
    \* Peek (Family 3)
    /\ peekActive = [t \in Thread |-> FALSE]
    \* RTS stale head — not captured (Family 4)
    /\ rtsStaleHead = [t \in Thread |-> [valid |-> FALSE, cnt |-> 0, pos |-> 0]]
    \* History
    /\ enqueued = <<>>
    /\ dequeued = <<>>
    /\ nextVal = 1

\* ========================================================================
\* MPMC Mode Actions (rte_ring_c11_pvt.h, rte_ring_elem_pvt.h)
\* ========================================================================

\* --- MPMC Producer: Reserve slots via CAS on prodHead ---
\* Models __rte_ring_headtail_move_head (rte_ring_c11_pvt.h:74-143)
\* called from __rte_ring_move_prod_head (rte_ring_elem_pvt.h:338-346)
\* then __rte_ring_do_enqueue_elem (rte_ring_elem_pvt.h:406-426)
MPMCReserveProd(t, n) ==
    /\ Mode = "MPMC"
    /\ phase[t] = "Idle"
    /\ stalled[t] = FALSE
    /\ n \in 1..MaxBatch
    \* Acquire load of cons tail inside CAS loop (rte_ring_c11_pvt.h:104)
    /\ LET stail == consTail
           free  == WrapPos(Capacity + stail - prodHead + 2 * Capacity)
           actual_n == IF n > free THEN 0 ELSE n
       IN
       /\ actual_n > 0
       \* CAS on prodHead (rte_ring_c11_pvt.h:137-140)
       /\ prodHead' = WrapPos(prodHead + actual_n)
       /\ phase' = [phase EXCEPT ![t] = "Reserved"]
       /\ reservedOH' = [reservedOH EXCEPT ![t] = prodHead]
       /\ reservedN' = [reservedN EXCEPT ![t] = actual_n]
       /\ side' = [side EXCEPT ![t] = "prod"]
       \* Allocate fresh values for this batch
       /\ reservedVals' = [reservedVals EXCEPT ![t] =
            [i \in 1..actual_n |-> nextVal + i - 1]]
       /\ nextVal' = nextVal + actual_n
       \* Acquire load refreshes visible opposing tail
       /\ visibleConsTail' = [visibleConsTail EXCEPT ![t] = consTail]
    /\ UNCHANGED <<prodTail, consHead, consTail, ring>>
    /\ UNCHANGED rtsVars
    /\ UNCHANGED visibleProdTail
    /\ UNCHANGED stallVars
    /\ UNCHANGED peekVars
    /\ UNCHANGED rtsStaleHeadVars
    /\ UNCHANGED historyVars

\* --- MPMC Consumer: Reserve slots via CAS on consHead ---
\* Models __rte_ring_headtail_move_head (rte_ring_c11_pvt.h:74-143)
\* called from __rte_ring_move_cons_head (rte_ring_elem_pvt.h:371-379)
\* capacity=0 for consumer (rte_ring_elem_pvt.h:377)
MPMCReserveCons(t, n) ==
    /\ Mode = "MPMC"
    /\ phase[t] = "Idle"
    /\ stalled[t] = FALSE
    /\ n \in 1..MaxBatch
    \* Acquire load of prod tail inside CAS loop (rte_ring_c11_pvt.h:104)
    /\ LET stail == prodTail
           entries == WrapPos(stail - consHead + 2 * Capacity)
           actual_n == IF n > entries THEN 0 ELSE n
       IN
       /\ actual_n > 0
       \* CAS on consHead (rte_ring_c11_pvt.h:137-140)
       /\ consHead' = WrapPos(consHead + actual_n)
       /\ phase' = [phase EXCEPT ![t] = "Reserved"]
       /\ reservedOH' = [reservedOH EXCEPT ![t] = consHead]
       /\ reservedN' = [reservedN EXCEPT ![t] = actual_n]
       /\ side' = [side EXCEPT ![t] = "cons"]
       /\ reservedVals' = [reservedVals EXCEPT ![t] = <<>>]
       \* Acquire load refreshes visible opposing tail
       /\ visibleProdTail' = [visibleProdTail EXCEPT ![t] = prodTail]
    /\ UNCHANGED <<prodHead, prodTail, consTail, ring>>
    /\ UNCHANGED rtsVars
    /\ UNCHANGED visibleConsTail
    /\ UNCHANGED stallVars
    /\ UNCHANGED peekVars
    /\ UNCHANGED rtsStaleHeadVars
    /\ UNCHANGED historyVars
    /\ UNCHANGED freshVars

\* --- Write Data: Copy elements into ring buffer ---
\* Models __rte_ring_enqueue_elems (rte_ring_elem_pvt.h:157-162)
\* or __rte_ring_dequeue_elems (rte_ring_elem_pvt.h:294-300)
WriteData(t) ==
    /\ phase[t] = "Reserved"
    /\ stalled[t] = FALSE
    /\ IF side[t] = "prod" THEN
         \* Producer writes values to ring slots (rte_ring_elem_pvt.h:419)
         /\ ring' = [i \in 0..(Capacity - 1) |->
              IF \E j \in 1..reservedN[t] :
                   SlotOf(WrapPos(reservedOH[t] + j - 1)) = i
              THEN reservedVals[t][
                   CHOOSE j \in 1..reservedN[t] :
                        SlotOf(WrapPos(reservedOH[t] + j - 1)) = i]
              ELSE ring[i]]
         /\ UNCHANGED reservedVals
       ELSE
         \* Consumer reads values from ring slots (rte_ring_elem_pvt.h:466)
         /\ reservedVals' = [reservedVals EXCEPT ![t] =
              [j \in 1..reservedN[t] |->
                   ring[SlotOf(WrapPos(reservedOH[t] + j - 1))]]]
         /\ UNCHANGED ring
    /\ phase' = [phase EXCEPT ![t] = "Writing"]
    /\ UNCHANGED <<prodHead, prodTail, consHead, consTail>>
    /\ UNCHANGED <<reservedOH, reservedN, side>>
    /\ UNCHANGED rtsVars
    /\ UNCHANGED staleVars
    /\ UNCHANGED stallVars
    /\ UNCHANGED peekVars
    /\ UNCHANGED rtsStaleHeadVars
    /\ UNCHANGED historyVars
    /\ UNCHANGED freshVars

\* --- MPMC Publish Tail: spin-wait then store-release ---
\* Models __rte_ring_update_tail (rte_ring_c11_pvt.h:25-45)
\* The spin-wait at line 36-37 blocks until tail == old_head
MPMCPublishTail(t) ==
    /\ Mode = "MPMC"
    /\ phase[t] = "Writing"
    /\ stalled[t] = FALSE
    /\ IF side[t] = "prod" THEN
         \* Spin-wait: prodTail must equal our old_head (rte_ring_c11_pvt.h:36)
         /\ prodTail = reservedOH[t]
         \* Store-release new tail (rte_ring_c11_pvt.h:44)
         /\ prodTail' = WrapPos(reservedOH[t] + reservedN[t])
         /\ enqueued' = enqueued \o reservedVals[t]
         /\ UNCHANGED <<prodHead, consHead, consTail, ring, dequeued>>
       ELSE
         \* Spin-wait: consTail must equal our old_head (rte_ring_c11_pvt.h:36)
         /\ consTail = reservedOH[t]
         \* Store-release new tail
         /\ consTail' = WrapPos(reservedOH[t] + reservedN[t])
         /\ dequeued' = dequeued \o reservedVals[t]
         /\ UNCHANGED <<prodHead, prodTail, consHead, ring, enqueued>>
    /\ phase' = [phase EXCEPT ![t] = "Idle"]
    /\ reservedN' = [reservedN EXCEPT ![t] = 0]
    /\ reservedVals' = [reservedVals EXCEPT ![t] = <<>>]
    /\ UNCHANGED <<reservedOH, side>>
    /\ UNCHANGED rtsVars
    /\ UNCHANGED staleVars
    /\ UNCHANGED stallVars
    /\ UNCHANGED peekVars
    /\ UNCHANGED rtsStaleHeadVars
    /\ UNCHANGED freshVars

\* ========================================================================
\* HTS Mode Actions (rte_ring_hts_elem_pvt.h)
\* ========================================================================

\* --- HTS Reserve: wait for head==tail, then CAS 64-bit (head, tail) ---
\* Models __rte_ring_hts_move_head (rte_ring_hts_elem_pvt.h:95-162)
\* The head_wait at line 119 spins until head == tail (serialization)
HTSReserveProd(t, n) ==
    /\ Mode = "HTS"
    /\ phase[t] = "Idle"
    /\ stalled[t] = FALSE
    /\ n \in 1..MaxBatch
    \* HTS gate: head == tail (rte_ring_hts_elem_pvt.h:63 — head_wait)
    /\ prodHead = prodTail
    \* Acquire load of opposing tail (rte_ring_hts_elem_pvt.h:126)
    /\ LET stail == consTail
           free  == WrapPos(Capacity + stail - prodHead + 2 * Capacity)
           actual_n == IF n > free THEN 0 ELSE n
       IN
       /\ actual_n > 0
       \* 64-bit CAS: move head, keep tail (rte_ring_hts_elem_pvt.h:144-145,155-158)
       /\ prodHead' = WrapPos(prodHead + actual_n)
       \* prodTail stays at old value (np.pos.tail = op.pos.tail, line 144)
       /\ phase' = [phase EXCEPT ![t] = "Reserved"]
       /\ reservedOH' = [reservedOH EXCEPT ![t] = prodHead]
       /\ reservedN' = [reservedN EXCEPT ![t] = actual_n]
       /\ side' = [side EXCEPT ![t] = "prod"]
       /\ reservedVals' = [reservedVals EXCEPT ![t] =
            [i \in 1..actual_n |-> nextVal + i - 1]]
       /\ nextVal' = nextVal + actual_n
       /\ visibleConsTail' = [visibleConsTail EXCEPT ![t] = consTail]
    /\ UNCHANGED <<prodTail, consHead, consTail, ring>>
    /\ UNCHANGED rtsVars
    /\ UNCHANGED visibleProdTail
    /\ UNCHANGED stallVars
    /\ UNCHANGED peekVars
    /\ UNCHANGED rtsStaleHeadVars
    /\ UNCHANGED historyVars

HTSReserveCons(t, n) ==
    /\ Mode = "HTS"
    /\ phase[t] = "Idle"
    /\ stalled[t] = FALSE
    /\ n \in 1..MaxBatch
    \* HTS gate: head == tail (rte_ring_hts_elem_pvt.h:63)
    /\ consHead = consTail
    \* Acquire load of opposing tail (rte_ring_hts_elem_pvt.h:126)
    /\ LET stail == prodTail
           entries == WrapPos(stail - consHead + 2 * Capacity)
           actual_n == IF n > entries THEN 0 ELSE n
       IN
       /\ actual_n > 0
       /\ consHead' = WrapPos(consHead + actual_n)
       /\ phase' = [phase EXCEPT ![t] = "Reserved"]
       /\ reservedOH' = [reservedOH EXCEPT ![t] = consHead]
       /\ reservedN' = [reservedN EXCEPT ![t] = actual_n]
       /\ side' = [side EXCEPT ![t] = "cons"]
       /\ reservedVals' = [reservedVals EXCEPT ![t] = <<>>]
       /\ visibleProdTail' = [visibleProdTail EXCEPT ![t] = prodTail]
    /\ UNCHANGED <<prodHead, prodTail, consTail, ring>>
    /\ UNCHANGED rtsVars
    /\ UNCHANGED visibleConsTail
    /\ UNCHANGED stallVars
    /\ UNCHANGED peekVars
    /\ UNCHANGED rtsStaleHeadVars
    /\ UNCHANGED historyVars
    /\ UNCHANGED freshVars

\* --- HTS Publish Tail: direct store (no spin-wait needed) ---
\* Models __rte_ring_hts_update_tail (rte_ring_hts_elem_pvt.h:26-43)
\* Simple: tail = old_tail + num (no ordering dependency since HTS serializes)
HTSPublishTail(t) ==
    /\ Mode = "HTS"
    /\ phase[t] = "Writing"
    /\ stalled[t] = FALSE
    /\ IF side[t] = "prod" THEN
         \* rte_ring_hts_elem_pvt.h:34,42 — tail = old_tail + num
         /\ prodTail' = WrapPos(reservedOH[t] + reservedN[t])
         /\ enqueued' = enqueued \o reservedVals[t]
         /\ UNCHANGED <<prodHead, consHead, consTail, ring, dequeued>>
       ELSE
         /\ consTail' = WrapPos(reservedOH[t] + reservedN[t])
         /\ dequeued' = dequeued \o reservedVals[t]
         /\ UNCHANGED <<prodHead, prodTail, consHead, ring, enqueued>>
    /\ phase' = [phase EXCEPT ![t] = "Idle"]
    /\ reservedN' = [reservedN EXCEPT ![t] = 0]
    /\ reservedVals' = [reservedVals EXCEPT ![t] = <<>>]
    /\ UNCHANGED <<reservedOH, side>>
    /\ UNCHANGED rtsVars
    /\ UNCHANGED staleVars
    /\ UNCHANGED stallVars
    /\ UNCHANGED peekVars
    /\ UNCHANGED rtsStaleHeadVars
    /\ UNCHANGED freshVars

\* ========================================================================
\* RTS Mode Actions (rte_ring_rts_elem_pvt.h)
\* ========================================================================

\* --- RTS Reserve: CAS on 64-bit (cnt, pos) pair ---
\* Models __rte_ring_rts_move_head (rte_ring_rts_elem_pvt.h:109-176)
\* Includes HTD wait at line 133 and counter increment at line 159
RTSReserveProd(t, n) ==
    /\ Mode = "RTS"
    /\ phase[t] = "Idle"
    /\ stalled[t] = FALSE
    /\ n \in 1..MaxBatch
    \* HTD throttle: head - tail.pos <= htd_max (rte_ring_rts_elem_pvt.h:77)
    /\ WrapPos(prodHead - prodTail + 2 * Capacity) <= HTDMax
    \* Acquire load of opposing tail (rte_ring_rts_elem_pvt.h:140)
    /\ LET stail == consTail
           free  == WrapPos(Capacity + stail - prodHead + 2 * Capacity)
           actual_n == IF n > free THEN 0 ELSE n
       IN
       /\ actual_n > 0
       \* CAS on (cnt, pos): pos += n, cnt += 1 (rte_ring_rts_elem_pvt.h:158-159,169-172)
       /\ prodHead' = WrapPos(prodHead + actual_n)
       /\ prodCnt' = IncCnt(prodCnt)
       /\ phase' = [phase EXCEPT ![t] = "Reserved"]
       /\ reservedOH' = [reservedOH EXCEPT ![t] = prodHead]
       /\ reservedN' = [reservedN EXCEPT ![t] = actual_n]
       /\ side' = [side EXCEPT ![t] = "prod"]
       /\ reservedVals' = [reservedVals EXCEPT ![t] =
            [i \in 1..actual_n |-> nextVal + i - 1]]
       /\ nextVal' = nextVal + actual_n
       /\ visibleConsTail' = [visibleConsTail EXCEPT ![t] = consTail]
    /\ UNCHANGED <<prodTail, consHead, consTail, ring>>
    /\ UNCHANGED <<consCnt, prodTailCnt, consTailCnt>>
    /\ UNCHANGED visibleProdTail
    /\ UNCHANGED stallVars
    /\ UNCHANGED peekVars
    /\ UNCHANGED rtsStaleHeadVars
    /\ UNCHANGED historyVars

RTSReserveCons(t, n) ==
    /\ Mode = "RTS"
    /\ phase[t] = "Idle"
    /\ stalled[t] = FALSE
    /\ n \in 1..MaxBatch
    \* HTD throttle (rte_ring_rts_elem_pvt.h:77)
    /\ WrapPos(consHead - consTail + 2 * Capacity) <= HTDMax
    \* Acquire load of opposing tail
    /\ LET stail == prodTail
           entries == WrapPos(stail - consHead + 2 * Capacity)
           actual_n == IF n > entries THEN 0 ELSE n
       IN
       /\ actual_n > 0
       /\ consHead' = WrapPos(consHead + actual_n)
       /\ consCnt' = IncCnt(consCnt)
       /\ phase' = [phase EXCEPT ![t] = "Reserved"]
       /\ reservedOH' = [reservedOH EXCEPT ![t] = consHead]
       /\ reservedN' = [reservedN EXCEPT ![t] = actual_n]
       /\ side' = [side EXCEPT ![t] = "cons"]
       /\ reservedVals' = [reservedVals EXCEPT ![t] = <<>>]
       /\ visibleProdTail' = [visibleProdTail EXCEPT ![t] = prodTail]
    /\ UNCHANGED <<prodHead, prodTail, consTail, ring>>
    /\ UNCHANGED <<prodCnt, prodTailCnt, consTailCnt>>
    /\ UNCHANGED visibleConsTail
    /\ UNCHANGED stallVars
    /\ UNCHANGED peekVars
    /\ UNCHANGED rtsStaleHeadVars
    /\ UNCHANGED historyVars
    /\ UNCHANGED freshVars

\* --- RTS Publish Tail: counter-based CAS ---
\* Models __rte_ring_rts_update_tail (rte_ring_rts_elem_pvt.h:24-62)
\* Key insight: only the LAST thread (whose incremented tail.cnt == head.cnt)
\* actually advances tail.pos to head.pos. Others just bump tail.cnt.
\*
\* The head is loaded with RELAXED ordering (rte_ring_rts_elem_pvt.h:49),
\* so it may be stale. If RTSCaptureHead was taken, rtsStaleHead[t].valid
\* is TRUE and we use the captured (possibly stale) values.
RTSPublishTail(t) ==
    /\ Mode = "RTS"
    /\ phase[t] = "Writing"
    /\ stalled[t] = FALSE
    /\ IF side[t] = "prod" THEN
         \* Read head — may be stale if captured (rte_ring_rts_elem_pvt.h:49)
         LET headCnt == IF rtsStaleHead[t].valid THEN rtsStaleHead[t].cnt ELSE prodCnt
             headPos == IF rtsStaleHead[t].valid THEN rtsStaleHead[t].pos ELSE prodHead
             newTailCnt == IncCnt(prodTailCnt)
         IN
         /\ prodTailCnt' = newTailCnt
         /\ UNCHANGED consTailCnt
         /\ IF newTailCnt = headCnt THEN
              \* Last thread (or thinks it is): advance tail to head position
              \* Collect ALL values from ring in [oldTail, newTail)
              LET numAdvanced == WrapPos(headPos - prodTail + 2 * Capacity)
                  advancedVals == [i \in 1..numAdvanced |->
                       ring[SlotOf(WrapPos(prodTail + i - 1))]]
              IN
              /\ prodTail' = headPos
              /\ enqueued' = enqueued \o advancedVals
              /\ UNCHANGED <<prodHead, consHead, consTail, ring, dequeued>>
            ELSE
              \* Not last: just bump counter (line 52 — cnt incremented but pos unchanged)
              /\ UNCHANGED <<prodHead, prodTail, consHead, consTail, ring>>
              /\ UNCHANGED historyVars
       ELSE
         LET headCnt == IF rtsStaleHead[t].valid THEN rtsStaleHead[t].cnt ELSE consCnt
             headPos == IF rtsStaleHead[t].valid THEN rtsStaleHead[t].pos ELSE consHead
             newTailCnt == IncCnt(consTailCnt)
         IN
         /\ consTailCnt' = newTailCnt
         /\ UNCHANGED prodTailCnt
         /\ IF newTailCnt = headCnt THEN
              \* Last thread: advance tail position
              LET numAdvanced == WrapPos(headPos - consTail + 2 * Capacity)
                  advancedVals == [i \in 1..numAdvanced |->
                       ring[SlotOf(WrapPos(consTail + i - 1))]]
              IN
              /\ consTail' = headPos
              /\ dequeued' = dequeued \o advancedVals
              /\ UNCHANGED <<prodHead, prodTail, consHead, ring, enqueued>>
            ELSE
              /\ UNCHANGED <<prodHead, prodTail, consHead, consTail, ring>>
              /\ UNCHANGED historyVars
    /\ phase' = [phase EXCEPT ![t] = "Idle"]
    /\ reservedN' = [reservedN EXCEPT ![t] = 0]
    /\ reservedVals' = [reservedVals EXCEPT ![t] = <<>>]
    \* Clear stale head after publish
    /\ rtsStaleHead' = [rtsStaleHead EXCEPT ![t] = [valid |-> FALSE, cnt |-> 0, pos |-> 0]]
    /\ UNCHANGED <<reservedOH, side>>
    /\ UNCHANGED <<prodCnt, consCnt>>
    /\ UNCHANGED staleVars
    /\ UNCHANGED stallVars
    /\ UNCHANGED peekVars
    /\ UNCHANGED freshVars

\* ========================================================================
\* RTS Stale Head Capture (Family 4: rte_ring_rts_elem_pvt.h:49)
\* ========================================================================

\* Models a RELAXED load of head (cnt, pos) during update_tail.
\* The stale value must be a (cnt, pos) pair that head.raw has actually held.
\* Since head advances monotonically (pos += n, cnt += 1 per reserve),
\* valid stale values are: (tailCnt + k, WrapPos(tail + k)) for some k.
\*
\* Critical constraint: C11 same-thread ordering guarantees that the
\* RELAXED load sees at least the thread's OWN CAS result. The thread's
\* CAS stored head = (tailCnt + k_own, WrapPos(tail + k_own)) where
\* k_own corresponds to the thread's reservation end position.
\* So k >= k_own (thread can't see a value older than its own CAS).
RTSCaptureHead(t) ==
    /\ Mode = "RTS"
    /\ phase[t] = "Writing"
    /\ stalled[t] = FALSE
    /\ rtsStaleHead[t].valid = FALSE
    /\ IF side[t] = "prod" THEN
         \* k_min: thread's own CAS advanced head TO reservedOH + reservedN
         \* k_max: current head position
         LET kMin == WrapPos(WrapPos(reservedOH[t] + reservedN[t]) - prodTail + 2 * Capacity)
             kMax == WrapPos(prodHead - prodTail + 2 * Capacity)
         IN \E k \in kMin..kMax :
              LET stalePos == WrapPos(prodTail + k)
                  staleCnt == (prodTailCnt + k) % CntMax
              IN rtsStaleHead' = [rtsStaleHead EXCEPT ![t] =
                   [valid |-> TRUE, cnt |-> staleCnt, pos |-> stalePos]]
       ELSE
         LET kMin == WrapPos(WrapPos(reservedOH[t] + reservedN[t]) - consTail + 2 * Capacity)
             kMax == WrapPos(consHead - consTail + 2 * Capacity)
         IN \E k \in kMin..kMax :
              LET stalePos == WrapPos(consTail + k)
                  staleCnt == (consTailCnt + k) % CntMax
              IN rtsStaleHead' = [rtsStaleHead EXCEPT ![t] =
                   [valid |-> TRUE, cnt |-> staleCnt, pos |-> stalePos]]
    /\ UNCHANGED ringVars
    /\ UNCHANGED threadVars
    /\ UNCHANGED rtsVars
    /\ UNCHANGED staleVars
    /\ UNCHANGED stallVars
    /\ UNCHANGED peekVars
    /\ UNCHANGED historyVars
    /\ UNCHANGED freshVars

\* ========================================================================
\* Stale Read Action (Family 2: rte_ring_c11_pvt.h:104-105)
\* ========================================================================

\* A thread's view of the opposing tail may lag behind the actual value.
\* This models weak memory ordering: the acquire-load of s->tail may return
\* any value between the thread's last observation and the current actual.
StaleRead(t) ==
    /\ stalled[t] = FALSE
    \* Update visible tails to any value between current view and actual
    /\ \E newVisCons \in {v \in PosRange :
            \* Between current view and actual consTail
            LET lo == visibleConsTail[t]
                hi == consTail
            IN WrapPos(v - lo + 2 * Capacity) <= WrapPos(hi - lo + 2 * Capacity)} :
       visibleConsTail' = [visibleConsTail EXCEPT ![t] = newVisCons]
    /\ \E newVisProd \in {v \in PosRange :
            LET lo == visibleProdTail[t]
                hi == prodTail
            IN WrapPos(v - lo + 2 * Capacity) <= WrapPos(hi - lo + 2 * Capacity)} :
       visibleProdTail' = [visibleProdTail EXCEPT ![t] = newVisProd]
    /\ UNCHANGED ringVars
    /\ UNCHANGED threadVars
    /\ UNCHANGED rtsVars
    /\ UNCHANGED stallVars
    /\ UNCHANGED peekVars
    /\ UNCHANGED rtsStaleHeadVars
    /\ UNCHANGED historyVars
    /\ UNCHANGED freshVars

\* ========================================================================
\* Thread Stall / Crash (Family 1: rte_ring_c11_pvt.h:35-37 window)
\* ========================================================================

\* A thread stalls between Reserve and PublishTail, blocking tail progress
Stall(t) ==
    /\ phase[t] \in {"Reserved", "Writing"}
    /\ stalled[t] = FALSE
    /\ stalled' = [stalled EXCEPT ![t] = TRUE]
    /\ UNCHANGED ringVars
    /\ UNCHANGED threadVars
    /\ UNCHANGED rtsVars
    /\ UNCHANGED staleVars
    /\ UNCHANGED peekVars
    /\ UNCHANGED rtsStaleHeadVars
    /\ UNCHANGED historyVars
    /\ UNCHANGED freshVars

\* ========================================================================
\* Peek Mode Actions (Family 3: rte_ring_peek_elem_pvt.h)
\* ========================================================================

\* --- Peek Start: reserve slots but don't write data yet ---
\* Models __rte_ring_do_enqueue_start (rte_ring_peek_elem_pvt.h:113-140)
\* Only supports ST and HTS modes (line 128-134: MPMC/RTS assert-fail)
PeekStartProd(t, n) ==
    /\ Mode \in {"HTS"}  \* Only HTS supports MT peek (ST not modeled)
    /\ phase[t] = "Idle"
    /\ stalled[t] = FALSE
    /\ peekActive[t] = FALSE
    /\ n \in 1..MaxBatch
    \* HTS gate (rte_ring_peek_elem_pvt.h:124-126 calls hts_move_prod_head)
    /\ prodHead = prodTail
    /\ LET stail == consTail
           free  == WrapPos(Capacity + stail - prodHead + 2 * Capacity)
           actual_n == IF n > free THEN 0 ELSE n
       IN
       /\ actual_n > 0
       /\ prodHead' = WrapPos(prodHead + actual_n)
       /\ phase' = [phase EXCEPT ![t] = "Reserved"]
       /\ reservedOH' = [reservedOH EXCEPT ![t] = prodHead]
       /\ reservedN' = [reservedN EXCEPT ![t] = actual_n]
       /\ side' = [side EXCEPT ![t] = "prod"]
       /\ peekActive' = [peekActive EXCEPT ![t] = TRUE]
       /\ reservedVals' = [reservedVals EXCEPT ![t] =
            [i \in 1..actual_n |-> nextVal + i - 1]]
       /\ nextVal' = nextVal + actual_n
       /\ visibleConsTail' = [visibleConsTail EXCEPT ![t] = consTail]
    /\ UNCHANGED <<prodTail, consHead, consTail, ring>>
    /\ UNCHANGED rtsVars
    /\ UNCHANGED visibleProdTail
    /\ UNCHANGED stallVars
    /\ UNCHANGED rtsStaleHeadVars
    /\ UNCHANGED historyVars

PeekStartCons(t, n) ==
    /\ Mode \in {"HTS"}
    /\ phase[t] = "Idle"
    /\ stalled[t] = FALSE
    /\ peekActive[t] = FALSE
    /\ n \in 1..MaxBatch
    /\ consHead = consTail
    /\ LET stail == prodTail
           entries == WrapPos(stail - consHead + 2 * Capacity)
           actual_n == IF n > entries THEN 0 ELSE n
       IN
       /\ actual_n > 0
       /\ consHead' = WrapPos(consHead + actual_n)
       /\ phase' = [phase EXCEPT ![t] = "Reserved"]
       /\ reservedOH' = [reservedOH EXCEPT ![t] = consHead]
       /\ reservedN' = [reservedN EXCEPT ![t] = actual_n]
       /\ side' = [side EXCEPT ![t] = "cons"]
       /\ peekActive' = [peekActive EXCEPT ![t] = TRUE]
       /\ reservedVals' = [reservedVals EXCEPT ![t] = <<>>]
       /\ visibleProdTail' = [visibleProdTail EXCEPT ![t] = prodTail]
    /\ UNCHANGED <<prodHead, prodTail, consTail, ring>>
    /\ UNCHANGED rtsVars
    /\ UNCHANGED visibleConsTail
    /\ UNCHANGED stallVars
    /\ UNCHANGED rtsStaleHeadVars
    /\ UNCHANGED historyVars
    /\ UNCHANGED freshVars

\* --- Peek Finish: commit n slots (n=0 aborts) ---
\* Models rte_ring_enqueue_elem_finish via __rte_ring_hts_set_head_tail
\* (rte_ring_peek_elem_pvt.h:96-108)
\* n=0 abort: head reverts to tail (line 104-105: pos = tail + 0 = tail)
PeekFinish(t, commitN) ==
    /\ peekActive[t] = TRUE
    /\ phase[t] \in {"Reserved", "Writing"}
    /\ stalled[t] = FALSE
    /\ commitN \in 0..reservedN[t]
    /\ IF side[t] = "prod" THEN
         \* __rte_ring_hts_set_head_tail (rte_ring_peek_elem_pvt.h:104-105)
         \* pos = tail + num; head = pos; tail = pos
         LET newPos == WrapPos(reservedOH[t] + commitN)
         IN
         /\ prodHead' = newPos
         /\ prodTail' = newPos
         /\ IF commitN > 0 THEN
              \* Write committed values to ring
              /\ ring' = [i \in 0..(Capacity - 1) |->
                   IF \E j \in 1..commitN :
                        SlotOf(WrapPos(reservedOH[t] + j - 1)) = i
                   THEN reservedVals[t][
                        CHOOSE j \in 1..commitN :
                             SlotOf(WrapPos(reservedOH[t] + j - 1)) = i]
                   ELSE ring[i]]
              /\ enqueued' = enqueued \o SubSeq(reservedVals[t], 1, commitN)
              /\ UNCHANGED dequeued
            ELSE
              /\ UNCHANGED <<ring, enqueued, dequeued>>
         /\ UNCHANGED <<consHead, consTail>>
       ELSE
         LET newPos == WrapPos(reservedOH[t] + commitN)
         IN
         /\ consHead' = newPos
         /\ consTail' = newPos
         /\ IF commitN > 0 THEN
              \* Read committed values from ring
              LET vals == [j \in 1..commitN |->
                   ring[SlotOf(WrapPos(reservedOH[t] + j - 1))]]
              IN
              /\ dequeued' = dequeued \o vals
              /\ UNCHANGED enqueued
            ELSE
              /\ UNCHANGED <<enqueued, dequeued>>
         /\ UNCHANGED <<prodHead, prodTail, ring>>
    /\ phase' = [phase EXCEPT ![t] = "Idle"]
    /\ peekActive' = [peekActive EXCEPT ![t] = FALSE]
    /\ reservedN' = [reservedN EXCEPT ![t] = 0]
    /\ reservedVals' = [reservedVals EXCEPT ![t] = <<>>]
    /\ UNCHANGED <<reservedOH, side>>
    /\ UNCHANGED rtsVars
    /\ UNCHANGED staleVars
    /\ UNCHANGED stallVars
    /\ UNCHANGED rtsStaleHeadVars
    /\ UNCHANGED freshVars

\* ========================================================================
\* Next State Relation
\* ========================================================================

ReserveProd(t) == \E n \in 1..MaxBatch :
    \/ MPMCReserveProd(t, n)
    \/ HTSReserveProd(t, n)
    \/ RTSReserveProd(t, n)

ReserveCons(t) == \E n \in 1..MaxBatch :
    \/ MPMCReserveCons(t, n)
    \/ HTSReserveCons(t, n)
    \/ RTSReserveCons(t, n)

PublishTail(t) ==
    \/ MPMCPublishTail(t)
    \/ HTSPublishTail(t)
    \/ RTSPublishTail(t)

PeekStart(t) == \E n \in 1..MaxBatch :
    \/ PeekStartProd(t, n)
    \/ PeekStartCons(t, n)

PeekFinishAction(t) == \E n \in 0..MaxBatch :
    PeekFinish(t, n)

Next ==
    \E t \in Thread :
        \/ ReserveProd(t)
        \/ ReserveCons(t)
        \/ WriteData(t)
        \/ PublishTail(t)
        \/ StaleRead(t)
        \/ Stall(t)
        \/ PeekStart(t)
        \/ PeekFinishAction(t)
        \/ RTSCaptureHead(t)

Spec == Init /\ [][Next]_allVars

\* ========================================================================
\* Invariants
\* ========================================================================

\* --- Standard Safety ---

\* RingSafety: every dequeued value was enqueued, in FIFO order
\* The dequeued sequence must be a prefix of enqueued
RingSafety ==
    /\ Len(dequeued) <= Len(enqueued)
    /\ \A i \in 1..Len(dequeued) : dequeued[i] = enqueued[i]

\* CapacityBound: in-flight elements never exceed capacity (Family 2)
\* In-flight = prodTail - consTail (elements visible to consumers but not yet consumed)
\* Plus reserved-but-not-published elements
CapacityBound ==
    WrapPos(prodHead - consTail + 2 * Capacity) <= Capacity

\* NoOverwrite: producer doesn't write to slot consumer hasn't finished reading
\* Encoded as: prodHead - consTail <= capacity (head never passes cons tail by > capacity)
NoOverwrite == CapacityBound

\* TailMonotonicity: tails only advance (within modular arithmetic)
\* This is structural — enforced by the actions, checked as a sanity invariant
\* (Checked via temporal property instead — see below)

\* --- Extension Invariants (Bug Families) ---

\* CounterConsistency (Family 1, 4): the actual in-flight thread count per
\* side must be < CntMax. If violated, the counter domain is too small and
\* ABA wraparound can occur.
CounterConsistency ==
    Mode = "RTS" =>
    LET prodInFlight == Cardinality({t \in Thread : phase[t] /= "Idle" /\ side[t] = "prod"})
        consInFlight == Cardinality({t \in Thread : phase[t] /= "Idle" /\ side[t] = "cons"})
    IN
    /\ prodInFlight < CntMax
    /\ consInFlight < CntMax

\* NoABA (Family 4): the modular counter difference must equal the actual
\* in-flight thread count. If they diverge, a counter has wrapped (ABA)
\* and the last-thread check in update_tail may misfire.
NoABA ==
    Mode = "RTS" =>
    LET prodInFlight == Cardinality({t \in Thread : phase[t] /= "Idle" /\ side[t] = "prod"})
        consInFlight == Cardinality({t \in Thread : phase[t] /= "Idle" /\ side[t] = "cons"})
    IN
    /\ (prodCnt - prodTailCnt + CntMax) % CntMax = prodInFlight
    /\ (consCnt - consTailCnt + CntMax) % CntMax = consInFlight

\* NoGarbageEnqueued: every enqueued value was written by a producer
\* (fresh values start at 1, ring slots initialized to 0). If a 0
\* appears in enqueued, an unwritten slot was exposed to consumers.
NoGarbageEnqueued == \A i \in 1..Len(enqueued) : enqueued[i] > 0

\* --- Structural Invariants ---

\* Head is always >= tail (modular)
HeadTailOrder ==
    /\ WrapPos(prodHead - prodTail + 2 * Capacity) >= 0
    /\ WrapPos(consHead - consTail + 2 * Capacity) >= 0

\* All thread phases are valid
ValidPhases ==
    \A t \in Thread : phase[t] \in {"Idle", "Reserved", "Writing"}

\* HTS mode: at most one thread in-flight PER SIDE
\* HTS serializes prod and cons independently (separate ht structures)
HTSSingleInFlight ==
    Mode = "HTS" =>
    /\ Cardinality({t \in Thread : phase[t] # "Idle" /\ stalled[t] = FALSE /\ side[t] = "prod"}) <= 1
    /\ Cardinality({t \in Thread : phase[t] # "Idle" /\ stalled[t] = FALSE /\ side[t] = "cons"}) <= 1

\* ========================================================================
\* Liveness / Temporal Properties
\* ========================================================================

\* TailProgress (Family 1): if no thread is stalled and ring is non-empty,
\* tail eventually advances
NoStalls == \A t \in Thread : stalled[t] = FALSE
TailProgress ==
    \A t \in Thread :
        (phase[t] = "Writing" /\ NoStalls) ~> (phase[t] = "Idle")

\* MPMCStallBlocks (Family 1, negative): one stalled producer blocks all
\* producer tail progress. This should FAIL for MPMC mode.
\* Simplified: if any thread is stalled, some Writing thread stays Writing forever.
MPMCStallBlocks ==
    \A t \in Thread :
        ((stalled[t] = TRUE /\ phase[t] # "Idle" /\ side[t] = "prod") =>
         [](\E t2 \in Thread : phase[t2] = "Writing" /\ side[t2] = "prod"))

\* RTSBoundedStall (Family 1): in RTS mode, if one thread stalls,
\* other threads can still make progress (up to htd_max slots).
\* Non-stalled Writing threads eventually become Idle.
RTSBoundedStall ==
    \A t \in Thread :
        ((stalled[t] = FALSE /\ phase[t] = "Writing") ~> (phase[t] = "Idle"))

====
